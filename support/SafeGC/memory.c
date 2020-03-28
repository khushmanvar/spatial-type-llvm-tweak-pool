//* This file implements a memory allocator and SafeGC "a conservative garbage collector" for temporal safety of c programs.

// think about doubts, free(), determining correctly list is empty before starting sweep phase, > ot >=, 
#define _GNU_SOURCE

// #define DEBUG

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h> // doubt
#include <unistd.h> // doubt
#include <sys/types.h>// doubt
#include <sys/stat.h> // doubt
#include <string.h> // doubt
#include <fcntl.h> // doubt
#include <elf.h> // doubt
#include <assert.h>
#include <pthread.h>
#include "memory.h"

typedef unsigned long long ulong64;
#define MAGIC_ADDR 0x12abcdef // doubt
#define PATH_SZ 128

#define SEGMENT_SIZE (4ULL << 32) // it is 2^34
#define PAGE_SIZE 4096 // it is 2^12
#define METADATA_SIZE ((SEGMENT_SIZE/PAGE_SIZE) * 2) // it is 2^23
#define NUM_PAGES_IN_SEG (METADATA_SIZE/2) // it is 2^22
#define OTHER_METADATA_SIZE ((METADATA_SIZE/PAGE_SIZE) * 2) // it is 2^12
#define COMMIT_SIZE PAGE_SIZE // it is 2^12
#define Align(x, y) (((x) + (y-1)) & ~(y-1)) // doubt
#define ADDR_TO_PAGE(x) (char*)(((ulong64)(x)) & ~(PAGE_SIZE-1)) // 
#define ADDR_TO_SEGMENT(x) (Segment*)(((ulong64)(x)) & ~(SEGMENT_SIZE-1)) // 
#define FREE 1 
#define MARK 2
#define GC_THRESHOLD (32ULL << 20) // it is 2^25 (32 MB)


long long marked = 0;
long long freed = 0;
long long total = 0;


long long NumGCTriggered = 0;
long long NumBytesFreed = 0;
long long NumBytesAllocated = 0;
extern char  etext, edata, end; // doubt

struct OtherMetadata // 20 byte metadata per segment.
{
	char *AllocPtr;
	char *CommitPtr;
	char *ReservePtr;
	char *DataPtr;
	int BigAlloc;
};

typedef struct Segment
{
	union // doubt.
	{
		unsigned short Size[NUM_PAGES_IN_SEG]; // it is 8 MB.
		struct OtherMetadata Other;
	};
} Segment;

typedef struct SegmentList
{
	struct Segment *Segment;
	struct SegmentList *Next;
} SegmentList;

typedef struct ObjHeader
{
	unsigned Size;
	unsigned Status; //doubt why so big? how to use other bits?
	ulong64 Type;
} ObjHeader;

#define OBJ_HEADER_SIZE (sizeof(ObjHeader))


static SegmentList *Segments = NULL;

static void setAllocPtr(Segment *Seg, char *Ptr) { Seg->Other.AllocPtr = Ptr; }
static void setCommitPtr(Segment *Seg, char *Ptr) { Seg->Other.CommitPtr = Ptr; }
static void setReservePtr(Segment *Seg, char *Ptr) { Seg->Other.ReservePtr = Ptr; }
static void setDataPtr(Segment *Seg, char *Ptr) { Seg->Other.DataPtr = Ptr; }
static char* getAllocPtr(Segment *Seg) { return Seg->Other.AllocPtr; }
static char* getCommitPtr(Segment *Seg) { return Seg->Other.CommitPtr; }
static char* getReservePtr(Segment *Seg) { return Seg->Other.ReservePtr; }
static char* getDataPtr(Segment *Seg) { return Seg->Other.DataPtr; }
static void setBigAlloc(Segment *Seg, int BigAlloc) { Seg->Other.BigAlloc = BigAlloc; }
static int getBigAlloc(Segment *Seg) { return Seg->Other.BigAlloc; }
static void myfree(void *Ptr);
static void checkAndRunGC();

static void addToSegmentList(Segment *Seg)
{
	SegmentList *L = malloc(sizeof(SegmentList));
	if (L == NULL)
	{
		printf("Unable to allocate list node\n");
		exit(0);
	}
	L->Segment = Seg;
	L->Next = Segments;
	Segments = L;
}

static void allowAccess(void *Ptr, size_t Size) 
{
	assert((Size % PAGE_SIZE) == 0); // size shoukd be a multiple of page_size
	assert(((ulong64)Ptr & (PAGE_SIZE-1)) == 0); // ptr should be address of first byte of a page.

	int Ret = mprotect(Ptr, Size, PROT_READ|PROT_WRITE);
	if (Ret == -1)
	{
		printf("unable to mprotect %s():%d\n", __func__, __LINE__);
		exit(0);
	}
}

static Segment* allocateSegment(int BigAlloc)
{
	void* Base = mmap(NULL, SEGMENT_SIZE * 2, PROT_NONE, MAP_ANON|MAP_PRIVATE, -1, 0); // why segment_size*2 = 2^35
	if (Base == MAP_FAILED)
	{
		printf("unable to allocate a segment\n");
		exit(0);
	}

	/* segments are aligned to segment size */
	Segment *Segment = (struct Segment*)Align((ulong64)Base, SEGMENT_SIZE); // doubt.
	allowAccess(Segment, METADATA_SIZE);

	char *AllocPtr = (char*)Segment + METADATA_SIZE;
	char *ReservePtr = (char*)Segment + SEGMENT_SIZE;
	setAllocPtr(Segment, AllocPtr);
	setReservePtr(Segment, ReservePtr);
	setCommitPtr(Segment, AllocPtr);
	setDataPtr(Segment, AllocPtr);
	setBigAlloc(Segment, BigAlloc);
	addToSegmentList(Segment);
	return Segment;
}

static void extendCommitSpace(Segment *Seg)
{
	char *AllocPtr = getAllocPtr(Seg);
	char *CommitPtr = getCommitPtr(Seg);
	char *ReservePtr = getReservePtr(Seg);
	char *NewCommitPtr = CommitPtr + COMMIT_SIZE;

	assert(AllocPtr == CommitPtr);
	if (NewCommitPtr <= ReservePtr)
	{
		allowAccess(CommitPtr, COMMIT_SIZE);
		setCommitPtr(Seg, NewCommitPtr);
	}
	else
	{
		assert(CommitPtr == ReservePtr);
	}
}

static unsigned short* getSizeMetadata(char *Ptr)
{
	char *Page = ADDR_TO_PAGE(Ptr);
	Segment *Seg = ADDR_TO_SEGMENT(Ptr);
	ulong64 PageNo = (Page - (char*)Seg)/ PAGE_SIZE;
	return &Seg->Size[PageNo];
}

static void createHole(Segment *Seg)
{
	char *AllocPtr = getAllocPtr(Seg);
	char *CommitPtr = getCommitPtr(Seg);
	size_t HoleSz = CommitPtr - AllocPtr;
	if (HoleSz > 0)
	{
		assert(HoleSz >= 8); // doubt 8 bits or bytes.
		ObjHeader *Header = (ObjHeader*)AllocPtr;
		Header->Size = HoleSz;
		Header->Status = 0;
		setAllocPtr(Seg, CommitPtr);
		myfree(AllocPtr + OBJ_HEADER_SIZE);
		NumBytesFreed -= HoleSz;
	}
}

static void reclaimMemory(void *Ptr, size_t Size)
{
	assert((Size % PAGE_SIZE) == 0);
	assert(((ulong64)Ptr & (PAGE_SIZE-1)) == 0);
	
	int Ret = mprotect(Ptr, Size, PROT_NONE);
	if (Ret == -1)
	{
		printf("unable to mprotect %s():%d\n", __func__, __LINE__);
		exit(0);
	}
	Ret = madvise(Ptr, Size, MADV_DONTNEED);
	if (Ret == -1)
	{
		printf("unable to reclaim physical page %s():%d\n", __func__, __LINE__);
		exit(0);
	}
}

/* used by the GC to free objects. */
static void myfree(void *Ptr)
{
	ObjHeader *Header = (ObjHeader*)((char*)Ptr - OBJ_HEADER_SIZE);
	#ifdef DEBUG
		printf("entering myfree()\n");
		printf("freeing this object (header): %p\n", Header);
		printf("header->size: %d\n", Header->Size);
		printf("header->status: %d\n", Header->Status);
		printf("header->type: %lld\n", Header->Type);
		printf("entering myfree()\n");
	#endif

	assert((Header->Status & FREE) == 0);
	NumBytesFreed += Header->Size;
	
	if (Header->Size > COMMIT_SIZE)
	{
		assert((Header->Size % PAGE_SIZE) == 0);
		assert(((ulong64)Header & (PAGE_SIZE-1)) == 0);
		size_t Size = Header->Size;
		char *Start = (char*)Header;
		size_t Iter;
		for (Iter = 0; Iter < Size; Iter += PAGE_SIZE)
		{
			unsigned short *SzMeta = getSizeMetadata((char*)Start + Iter);
			SzMeta[0] = PAGE_SIZE;
		}
		Header->Status = FREE;
		reclaimMemory(Header, Header->Size);
		return;
	}

	unsigned short *SzMeta = getSizeMetadata((char*)Header);
	SzMeta[0] += Header->Size;
	assert(SzMeta[0] <= PAGE_SIZE);
	Header->Status = FREE;
	if (SzMeta[0] == PAGE_SIZE)
	{
		char *Page = ADDR_TO_PAGE(Ptr);
		reclaimMemory(Page, PAGE_SIZE);
	}
}

static void* BigAlloc(size_t Size)
{
	size_t AlignedSize = Align(Size + OBJ_HEADER_SIZE, PAGE_SIZE); // doubt
	assert(AlignedSize <= SEGMENT_SIZE - METADATA_SIZE); // doubt
	static Segment *CurSeg = NULL;
	if (CurSeg == NULL)
	{
		CurSeg = allocateSegment(1);
	}
	char *AllocPtr = getAllocPtr(CurSeg);
	char *CommitPtr = getCommitPtr(CurSeg);
	char *NewAllocPtr = AllocPtr + AlignedSize;
	char *ReservePtr = getReservePtr(CurSeg);
	if (NewAllocPtr > ReservePtr)
	{
		CurSeg = allocateSegment(1);
		return BigAlloc(Size);
	}
	assert(AllocPtr == CommitPtr);
	allowAccess(CommitPtr, AlignedSize);
	setAllocPtr(CurSeg, NewAllocPtr);
	setCommitPtr(CurSeg, NewAllocPtr);

	unsigned short *SzMeta = getSizeMetadata(AllocPtr);
	SzMeta[0] = 1;

	ObjHeader *Header = (ObjHeader*)AllocPtr;
	Header->Size = AlignedSize;
	Header->Status = 0;
	Header->Type = 0;
	return AllocPtr + OBJ_HEADER_SIZE;
}


void *_mymalloc(size_t Size)
{
	size_t AlignedSize = Align(Size, 8) + OBJ_HEADER_SIZE;

	NumBytesAllocated += AlignedSize;
	checkAndRunGC(AlignedSize);
	if (AlignedSize > COMMIT_SIZE)
	{
		return BigAlloc(Size);
	}
	assert(Size != 0);
	assert(sizeof(struct OtherMetadata) <= OTHER_METADATA_SIZE);
	assert(sizeof(struct Segment) == METADATA_SIZE);

	static Segment *CurSeg = NULL;

	if (CurSeg == NULL)
	{
		CurSeg = allocateSegment(0);
	}
	char *AllocPtr = getAllocPtr(CurSeg);
	char *CommitPtr = getCommitPtr(CurSeg);
	char *NewAllocPtr = AllocPtr + AlignedSize;
	if (NewAllocPtr > CommitPtr)
	{
		if (AllocPtr != CommitPtr)
		{
			/* Free remaining space on this page */
			createHole(CurSeg);
		}
		extendCommitSpace(CurSeg);
		AllocPtr = getAllocPtr(CurSeg);
		NewAllocPtr = AllocPtr + AlignedSize;
		CommitPtr = getCommitPtr(CurSeg);
		if (NewAllocPtr > CommitPtr)
		{
			CurSeg = allocateSegment(0);
			return _mymalloc(Size);
		}
	}

	setAllocPtr(CurSeg, NewAllocPtr);
	ObjHeader *Header = (ObjHeader*)AllocPtr;
	Header->Size = AlignedSize;
	Header->Status = 0;
	Header->Type = 0;
	return AllocPtr + OBJ_HEADER_SIZE;
}


/***-------------------------------my code starts here-----------------------------------------------****/
//* object header list node.
typedef struct DLList
{
	char *  objhdr;
	struct DLList * next;
}   DLList;

//* object header list head and tail.
DLList * dllhead=NULL;
DLList * dlltail=NULL;


//* a util function to print object header scan list for debussing purposes
static void printDLList()
{
	#ifdef DEBUG
		//printf("entering printDLList()\n"); //* impp
	#endif
	if (dllhead==NULL)
	{
		#ifdef DEBUG
			printf("scan list is empty, HEAD: %p TAIL: %p\n", dllhead, dlltail);	
		#endif
		
		return;
	}
	int len = 0;
	DLList * node_itr = dllhead;
	while (node_itr!=NULL)
	{
		len+=1;
		#ifdef DEBUG
			printf("ptr: %p\n",node_itr);
			printf("ObjHeader: %p\n",node_itr->objhdr);
		#endif
		node_itr = node_itr->next;
	}
	#ifdef DEBUG
		printf("length of scan list is: %d\n",len);
		printf("exiting printDLList()\n"); //* impp
	#endif	
}


//* util funtion to push new object header at back/tail of object header list.
static void push(char * objhdr)
{
	
	#ifdef DEBUG
		printf("entering push()\n"); //* impp
	#endif
	
	DLList * newtail = (DLList *)malloc(sizeof(DLList));
	newtail->objhdr = objhdr;
	newtail->next = NULL;
	if (dlltail==NULL)
	{
		dlltail = newtail;
		dllhead = newtail;
	}else
	{
		dlltail->next = newtail;
		dlltail = newtail;	
	}
	#ifdef DEBUG
		printf("pushed pointer: %p\n", dlltail->objhdr);
		printf("head: %p\n", dllhead->objhdr);
		printDLList(); //* impp
		printf("exiting push()\n"); //* impp
	#endif
	
}

//* util function to pop value from front of scanlist.
static char* pop()
{
	#ifdef DEBUG
		printf("entering pop()\n"); //* impp
	#endif
	
	char * toret;
	if (dllhead!=NULL)
	{
		toret = dllhead->objhdr;
		DLList * temp = dllhead;
		dllhead = dllhead->next;
		if (dllhead==NULL)
		{
			dlltail = NULL;
		}
		free(temp); // doubt.
	}else
	{
		toret = NULL;
	}
	#ifdef DEBUG
		printf("exiting pop()\n"); //* impp
	#endif
	return toret;
}

/* find page, page no. in segment, size mtadate of page corresponding to addr.
 * if page is not freed or unallocated, i.e. SzMeta[0]!=PAGE_SIZE then check bigalloc, otherwise return NULL.
 * if bigalloc is 1, backtrack to previous pages till we get 1 in the metadata (till ObjectHeader).
 * if bilalloc is 0, start from start of page and move forward until that object is reached between whoch addr lies.
 * return the objectHeader.	
*/
static char * giveObjectHeaderAddr(char * addr, Segment * s, int is_BigAlloc)
{
	#ifdef DEBUG
		printf("entering giveObjectHeaderAddr()\n"); //* impp	
	#endif
	
	//* local variables storing metadate of page, page and page no. corresponding to addr.
	unsigned short *SzMeta = getSizeMetadata(addr);
	char *Page = ADDR_TO_PAGE(addr);
	ulong64 PageNo = (Page - (char*)s)/ PAGE_SIZE;
	
	//* this variable will store the object header if able to find.
	char *Header = NULL;

	//* if the corresponding heap page is allocated (or not freed) only then proceed.
	if (!(SzMeta[0]==PAGE_SIZE))
	{
		if (is_BigAlloc==1)
		{
			while(s->Size[PageNo]!=1)
			{
				Page -= PAGE_SIZE;
				PageNo-=1;
			}
			Header = Page;	
		}else
		{
			//* variables to iterate over all objects on this page.
			char * header_itr = Page;
			ObjHeader * header_itr_ptr = (ObjHeader*)header_itr;
			while(!( addr<=header_itr+header_itr_ptr->Size  &&  addr>=header_itr+OBJ_HEADER_SIZE) && (header_itr<Page+PAGE_SIZE)) // doubt signs <, <=, >, >=.
			{
				header_itr = header_itr + header_itr_ptr->Size;
				header_itr_ptr = (ObjHeader*)header_itr;
			}
			Header = header_itr;
			assert(Header!=NULL);
		}	
	}else
	{
		Header = NULL;
	}
	#ifdef DEBUG
		printf("exiting giveObjectHeaderAddr()\n"); //* impp
	#endif		
	return Header;
	
}

/* it first extracts the 8 byte value at location ptr_inp and stores it in ptr.
 * it then tries to find a head segment within which ptr can lie.
 * if successful in finding a segment, this means ptr is a heap object's address.
 * then it passes ptr to giveObjectHeaderAddr function to get object header corresponding to ptr.
 * if it does not get object header (instead gets NULL) this means page corresponding to ptr is not allocated or de-allocated.
 * it then checks for validity of that object. The oject should not be free and not be marked. Then it pushes object header in scan list.
*/

static void handleRootPtr(char* ptr_inp)
{
	#ifdef DEBUG
		printf("entering handleRootPtr()\n"); //* impp	
	#endif
	
	//* Local vars related to current segment.
	SegmentList* segment_itr = Segments;
	Segment* current_segment;
	struct OtherMetadata current_other;
	char* current_DataPtr;
	char* current_AllocPtr; 
	int current_BigAlloc; 
	
	//* variable which will be assigned the segment of ptr_inp.
	Segment* ptr_segment = NULL;

	//* variable which will be assigned object header address if ptr is a head object's address.
	char* Header;

	//* 8-byte value stored at location ptr_inp treated as a pointer.
	char* ptr = (char *) (*((ulong64 *)ptr_inp ));

	//* Local vars related to itertion over Page and Objects.
	char* page_itr;
	char* ObjHeader_itr;
	ObjHeader* ObjHeader_itr_ptr;
	unsigned short *SzMeta;

	//* iterating over all segments and comparing ptr's value to be lying between data pointer and alloc pointer of a segment.
	//* takes decision whether ptr is a heap address and store its segment's pointer in ptr_segment.
	while (segment_itr!=NULL)
	{
		current_segment = segment_itr->Segment;
		current_other = current_segment->Other;
		current_DataPtr = current_other.DataPtr;
		current_AllocPtr = current_other.AllocPtr; //* most imp line
		if (current_DataPtr<=ptr &&  ptr<=current_AllocPtr)
		{
			ptr_segment = current_segment;
			break;
		}
		segment_itr = segment_itr->Next;
	}

	/* checking whether we were successful to find a segment for ptr.
	 * if yes getting the object header of ptr and pusing that object header to object header scan list.
	*/
	if (ptr_segment==NULL)
	{
		#ifdef DEBUG
			printf("this pointer %p is not a heap address because it does not lie in range of any segment\n", ptr); //* inmpp
		#endif
		
	}else
	{
		current_BigAlloc = ptr_segment->Other.BigAlloc;
		#ifdef DEBUG
			printf("this pointer is a heap address. \n"); //* impp
			printf("ptr_segment.BigAlloc %d\n", current_BigAlloc);
			printf("ptr: %p\n", ptr); // *impp
		#endif
		

		//* getting the object header and pushing it to scan list only if the object is not marked and not free.
		Header = giveObjectHeaderAddr(ptr, ptr_segment, current_BigAlloc);
		if (Header!=NULL)
		{
			#ifdef DEBUG
				printf("ObjHeader: %p\n", Header); // *impp
				printf("size: %d\n", ((ObjHeader *)Header)->Size); //* impp
				printf("Status: %d\n", ((ObjHeader *)Header)->Status);
				printf("Type: %lld\n", ((ObjHeader *)Header)->Type);
			#endif
			
			if (((ObjHeader *)Header)->Status==0)
			{
				push(Header); //* here i have to make sure that the object header pointer which i am going to push is a valid pointer of a not free, not marked object.
			}else
			{
				#ifdef DEBUG
					printf("object pointed by %p is not valid\n", ptr); //* impp
				#endif	
				
			}
		}else
		{
			#ifdef DEBUG
				printf("this pointer %p is not a heap address because its page is freed. \n", ptr); //* inmpp
			#endif
			
		}	
	}
	#ifdef DEBUG
		printf("exiting handleRootPtr()\n"); //* impp
	#endif
}

/* it checks of the passed object header pointer is not null.
 * it cheks if the pointed object is already marked or is free. It proceeds only if the object is not marked or not free.
 * then it walks all 4 byte aligned addressed with passed object.
 * it just passes the 4 byte aligned address to handleRootPtr to handle that pointer for a probably heap address.
*/
static void scanPtr(char* ObjHeader_itr)
{
	#ifdef DEBUG
		printf("entering scanPtr()\n"); //* impp
	#endif
	
	//* variables corresponging to passed pointer header.
	ObjHeader* ObjHeader_itr_ptr = ((ObjHeader *)ObjHeader_itr);
	char* ObjHeader_end = ObjHeader_itr + ObjHeader_itr_ptr->Size; // doubt is it correct?
	char* ObjHeader_aligned_start = (char *)Align((ulong64)ObjHeader_itr+OBJ_HEADER_SIZE,4);
	
	//* main objects iterating pointer.
	char * ptr_itr;

	//* logic to handle passed object pointer
	if (ObjHeader_itr!=NULL) // doubt can it ever be NULL?
	{
		if (ObjHeader_itr_ptr->Status != 0)
		{
			return;
		}
		#ifdef DEBUG
			printf("popped: %p\n", ObjHeader_itr_ptr); //* impp
		#endif
		if (ObjHeader_itr_ptr->Status == 0)
		{
			
			#ifdef DEBUG
				printf("popped size: %d\n", ObjHeader_itr_ptr->Size);
				printf("popped status: %d\n", ObjHeader_itr_ptr->Status);
				printf("popped Type: %lld\n", ObjHeader_itr_ptr->Type);
				printf("ObjHeader_aligned_start: %p\n", ObjHeader_aligned_start); //* impp
				printf("ObjHeader_end: %p\n",ObjHeader_end);
				printf("marked: %p size: %d\n", ObjHeader_itr_ptr, ObjHeader_itr_ptr->Size);
			#endif
			
			marked+=1;
			ObjHeader_itr_ptr->Status = MARK;	
			for (ptr_itr=ObjHeader_aligned_start ; ptr_itr<=ObjHeader_end ; ptr_itr+=4)
			{
				if (ptr_itr + 8 <= ObjHeader_end) // doubt < or <=
				{
					#ifdef DEBUG
						printf("field looking like pointer: %p\n",ptr_itr); // *impp
					#endif
					handleRootPtr(ptr_itr);
				}
			}			
		}else
		{
			#ifdef DEBUG
				printf("this pointer is either already marked or free: %p\n", ObjHeader_itr);
			#endif
		}
	
	}
	#ifdef DEBUG
		printf("exiting scanPtr()\n"); //* impp
	#endif
}


/* scan and mark objects in the scanner list.
 * add newly encountered objects to the scanner list.
 */
/* this function just pops all object headers pointer from DLList until list becomes empty.
 * after popping it passes object header pointer to scanPtr method to scan this object completely.
*/
static void scanner()
{
	#ifdef DEBUG
		printf("entering scanner()\n"); //* impp
	#endif
	while (!(dlltail==NULL || dllhead==NULL)) // doubt how to correctly check list is empty.
	{
		char * ObjHeader_itr = pop();
		if (getSizeMetadata(ObjHeader_itr)[0]!=PAGE_SIZE)
		{
			scanPtr(ObjHeader_itr);	
		}
		
	}
	#ifdef DEBUG
		printf("exiting scanner()\n"); //* impp
	#endif
}

//* a util function to print info about segments.
static void maze()
{
	// #ifdef DEBUG
		printf("entering maze()\n"); //* impp
		printf("**----Start :: printing info about segments----**\n"); //* impp
	// #endif
	
	SegmentList * segment_head = Segments;
	int count = 0;
	while (segment_head!=NULL)
	{
		count+=1;
		Segment * current_segment = segment_head->Segment;
		struct OtherMetadata current_other = current_segment->Other;
			//#ifdef DEBUG
				printf("segment no. %d\n",count);
				printf("current_segment DataPtr: %p\n", current_other.DataPtr);
				printf("current_segment ReservePtr: %p\n", current_other.ReservePtr);
				printf("current BigAlloc: %d\n", current_other.BigAlloc);
				printf("current_CommitPtr: %p\n", current_other.CommitPtr);
				printf("current_AllocPtr: %p\n", current_other.AllocPtr);
			//#endif
		segment_head = segment_head->Next;
	}
	//#ifdef DEBUG
		printf("**----END :: printing info about segments----**\n"); //* impp
		printf("exiting maze()\n"); //* impp
	//#endif
}

//* a function written to debug for checking all objects in head at start of runGc.
static void dummy_sweep()
{
	//maze();
	//* Local vars related to current segment.
	SegmentList* segment_itr = Segments;
	Segment* current_segment;
	struct OtherMetadata current_other;
	char* current_DataPtr;
	char* current_CommitPtr; 
	int current_BigAlloc; 
	
	//* Local vars related to itertion over Page and Objects.
	char* page_itr;
	char* ObjHeader_itr;
	ObjHeader* ObjHeader_itr_ptr;
	unsigned short *SzMeta;
	
	//* iterating over all segments.
	while (segment_itr!=NULL)
	{
		
		current_segment = segment_itr->Segment;
		current_other = current_segment->Other;
		current_DataPtr = current_other.DataPtr;
		current_CommitPtr = current_other.AllocPtr; //* most imp line
		current_BigAlloc = current_other.BigAlloc;
		page_itr = current_DataPtr;

		if (current_BigAlloc==1)
		{	
			while(page_itr<current_CommitPtr) // duubt < or <=
			{
				
				SzMeta = getSizeMetadata(page_itr);
				if (SzMeta[0]==1)
				{
					total+=1;
					ObjHeader_itr = page_itr;
					ObjHeader_itr_ptr = (ObjHeader*)ObjHeader_itr;
					// printf("sweeping object: %p\n",ObjHeader_itr_ptr);
					// printf("its bigalloc is %d\n",current_BigAlloc);
					// printf("its type is: %d\n", ObjHeader_itr_ptr->Status);
					// printf("its size is: %d\n", ObjHeader_itr_ptr->Size);
					// printf("its actual type is: %lld\n", ObjHeader_itr_ptr->Type);
				}
				page_itr += PAGE_SIZE;
			}
		}else if (current_BigAlloc==0)
		{
			while(page_itr<current_CommitPtr) // duubt < or <=
			{
				
				SzMeta = getSizeMetadata(page_itr);
				if (SzMeta[0]!=PAGE_SIZE)
				{
					ObjHeader_itr = page_itr;
					ObjHeader_itr_ptr = (ObjHeader*)ObjHeader_itr;
					while (ObjHeader_itr < page_itr + PAGE_SIZE && ObjHeader_itr < current_CommitPtr	) // duubt < or <=
					{
						
						total+=1;
						// printf("sweeping object: %p\n",ObjHeader_itr_ptr);
						// printf("its type is: %d\n", ObjHeader_itr_ptr->Status);
						// printf("its size is: %d\n", ObjHeader_itr_ptr->Size);
						// printf("its actual type is: %lld\n", ObjHeader_itr_ptr->Type);
						// printf("page of this object is: %p\n", ADDR_TO_PAGE(ObjHeader_itr));
						// printf("metadata of this page: %d\n",getSizeMetadata(ObjHeader_itr)[0] );
						if (ObjHeader_itr_ptr->Size==0)
						{
							exit(0);
						}
						ObjHeader_itr = ObjHeader_itr + ObjHeader_itr_ptr->Size;
						ObjHeader_itr_ptr = (ObjHeader*)ObjHeader_itr;
						//printf("new objectHeader after addition of old size: %p\n", ObjHeader_itr);
					}
				}
				page_itr += PAGE_SIZE;
			}
		}
		segment_itr = segment_itr->Next;
	}
}

/* Free all unmarked objects. */
static void sweep()
{
	//maze();
	#ifdef DEBUG
		printf("entering sweep()\n"); //* impp
	#endif
	
	//* Local vars related to current segment.
	SegmentList* segment_itr = Segments;
	Segment* current_segment;
	struct OtherMetadata current_other;
	char* current_DataPtr;
	char* current_AllocPtr; 
	int current_BigAlloc; 
	
	//* Local vars related to itertion over Page and Objects.
	char* page_itr;
	char* ObjHeader_itr;
	ObjHeader* ObjHeader_itr_ptr;
	unsigned short *SzMeta;
	
	//* iterating over all segments.
	while (segment_itr!=NULL)
	{
		
		//* setting current segment related Local vars.
		current_segment = segment_itr->Segment;
		current_other = current_segment->Other;
		current_DataPtr = current_other.DataPtr;
		current_AllocPtr = current_other.AllocPtr; //* most imp line
		current_BigAlloc = current_other.BigAlloc;
		
		//* initializing page iteration variable as top address of current page.
		page_itr = current_DataPtr;

		//* handling a segmnent with BigAlloc=1.
		/* iterate over all pages in this segment.
		 * check if metadata of a page is = 1. This means the first byte of this page is the address of ab object header.
		 * if object is unmarked, free it.
		 * if object is marked, unmark it.
		 * if object is free, ignore it.	
		 */
		if (current_BigAlloc==1)
		{	
			while(page_itr<current_AllocPtr) // duubt < or <=
			{
				SzMeta = getSizeMetadata(page_itr);
				if (SzMeta[0]==1)
				{
					ObjHeader_itr = page_itr;
					ObjHeader_itr_ptr = (ObjHeader*)ObjHeader_itr;
					unsigned ObjHeader_itr_ptr_size = ObjHeader_itr_ptr->Size;
					#ifdef DEBUG
						printf("sweeping object: %p\n",ObjHeader_itr_ptr);
						printf("its bigalloc is %d\n",current_BigAlloc);
						printf("its type is: %d\n", ObjHeader_itr_ptr->Status);
						printf("its size is: %d\n", ObjHeader_itr_ptr->Size);
						printf("its actual type is: %lld\n", ObjHeader_itr_ptr->Type);
					#endif
					if (ObjHeader_itr_ptr->Status==0)
					{
						#ifdef DEBUG
							printf("FREED large object %p of size: %d\n", ObjHeader_itr_ptr, ObjHeader_itr_ptr->Size);
						#endif
						freed+=1;
						myfree((char*)ObjHeader_itr_ptr + OBJ_HEADER_SIZE);
					}else if (ObjHeader_itr_ptr->Status==MARK)
					{
						ObjHeader_itr_ptr->Status=0;	
					}
					page_itr += ObjHeader_itr_ptr_size;
				}else
				{
					page_itr += PAGE_SIZE;
				}
				
			}
		}
		
		//* handling a segmnent with BigAlloc=0.
		/* iterate over all pages in this segment.
		 * check if metadata of a page is != PAGE_SIZE ( his page is not free), start iterating objects in it.
		 * first byte of a page will be an objectheader. Initialize Object header iteration pointer to first byte of page.
		 * increment object header pointer by size of object in each iteration to reach the next object.
		 * if an object is unmarked, free it.
		 * if an object is marked, unmark it.
		 * if an object is free, ignore it.	
		 */
		else if (current_BigAlloc==0)
		{
			while(page_itr<current_AllocPtr) // duubt < or <=
			{
				SzMeta = getSizeMetadata(page_itr);
				if (SzMeta[0]!=PAGE_SIZE)
				{
					ObjHeader_itr = page_itr;
					ObjHeader_itr_ptr = (ObjHeader*)ObjHeader_itr;
					
					ObjHeader* ObjectHeader_to_free = NULL;
					while (SzMeta[0]!=PAGE_SIZE && (ObjHeader_itr < page_itr + PAGE_SIZE && ObjHeader_itr < current_AllocPtr)) // doubt < or <=
					{
						ObjectHeader_to_free = NULL;
						#ifdef DEBUG
							printf("sweeping object: %p\n",ObjHeader_itr_ptr);
							printf("its bigalloc is %d\n", current_BigAlloc);
							printf("its type is: %d\n", ObjHeader_itr_ptr->Status);
							printf("its size is: %d\n", ObjHeader_itr_ptr->Size);
							printf("its actual type is: %lld\n", ObjHeader_itr_ptr->Type);
						#endif
						if (ObjHeader_itr_ptr->Size==0)
						{
							#ifdef DEBUG
								printf("program exited due to finding a 0 sized object on heap.");
							#endif
							exit(0);
						}
						if (ObjHeader_itr_ptr->Status==0)
						{
							#ifdef DEBUG
								printf("FREED small object %p of size: %d\n", ObjHeader_itr_ptr, ObjHeader_itr_ptr->Size);
							#endif
							ObjectHeader_to_free = ObjHeader_itr_ptr;
						}else if (ObjHeader_itr_ptr->Status==MARK)
						{
							ObjHeader_itr_ptr->Status=0;	
						}
						ObjHeader_itr = ObjHeader_itr + ObjHeader_itr_ptr->Size;
						ObjHeader_itr_ptr = (ObjHeader*)ObjHeader_itr;
						if (ObjectHeader_to_free!=NULL)
						{
							#ifdef DEBUG
								printf("debug %p\n", ObjectHeader_to_free );	
							#endif
							freed+=1;
							myfree((char*)ObjectHeader_to_free + OBJ_HEADER_SIZE);
						}
					}
				}
				page_itr += PAGE_SIZE;
			}
		}
		segment_itr = segment_itr->Next;
		//* end of main while loop iterating over all segments.	
	}
	#ifdef DEBUG
		printf("exiting sweep()\n"); //* impp
	#endif
	
}


/* walk all 4-byte aligned addresses.
 * add valid objects to the scanner list for  
 * mark and scan.
 */
/* it first prints top and bottom for debugging.
 * it then aligns top to 4 byte divisible.
 * it then iterates all 4 byte aligned address from alogned_top to bottom.
 * while iterating if some pointer is 8 bytes before bottom, it passes it to handleRootPtr funtion which will further handle it.
 * it prints each pointer it passes to handleRootPtr for debugging purposes.
 */
static void scanRoots(unsigned *Top, unsigned *Bottom)
{
	#ifdef DEBUG
		printf("entering scanRoots()\n"); //* impp
		//* for debugging.
		printf("TOP: %p\n", Top); // *impp
		printf("Bottom: %p\n", Bottom); // *impp
	#endif

	//* main looping logic for iterating addresses of roots.
	char * aligned_top = (char *)Align((ulong64)Top,4);
	char * ptr_itr;
	for (ptr_itr=aligned_top ; ptr_itr<=(char*)Bottom ; ptr_itr+=4)
	{
		if (ptr_itr + 8 <= (char*)Bottom) // doubt < or <=
		{
			#ifdef DEBUG
				printf("pointer: %p\n",ptr_itr); // *impp
			#endif
				handleRootPtr(ptr_itr);
		}
	}
	#ifdef DEBUG
		printf("exiting scanRoots()\n"); //* impp
	#endif
}


static size_t
getDataSecSz()
{
	char Exec[PATH_SZ];
	ssize_t Count = readlink( "/proc/self/exe", Exec, PATH_SZ);
	size_t DsecSz = -1;

	if (Count == -1) {
		return -1;
	}
	Exec[Count] = '\0';

	int fd = open(Exec, O_RDONLY);
	if (fd == -1) {
		return -1;
	}

	struct stat Statbuf;
	fstat(fd, &Statbuf);

	char *Base = mmap(NULL, Statbuf.st_size, PROT_READ, MAP_SHARED, fd, 0);
	if (Base == NULL) {
		close(fd);
		return -1;
	}

	Elf64_Ehdr *Header = (Elf64_Ehdr*)Base;

	if (Header->e_ident[0] != 0x7f
		|| Header->e_ident[1] != 'E'
		|| Header->e_ident[2] != 'L'
		|| Header->e_ident[3] != 'F')
	{
		goto out;
	}

	int i;
	Elf64_Shdr *Shdr = (Elf64_Shdr*)(Base + Header->e_shoff);
	char *Strtab = Base + Shdr[Header->e_shstrndx].sh_offset;

	for (i = 0; i < Header->e_shnum; i++)
	{
		char *Name = Strtab + Shdr[i].sh_name;
		if (!strncmp(Name, ".data", 6))
		{
			DsecSz = Shdr[i].sh_size;
		}
	}

out:
	munmap(Base, Statbuf.st_size);
	close(fd);
	return DsecSz;
}



void _runGC()
{
	dummy_sweep();
	//* calling a util function to see whether our sweep logic is good.
	// dummy_sweep();
	
	#ifdef DEBUG
		printf("entering _runGC()\n");
	#endif
	
	//maze();
	NumGCTriggered++;
	//unsigned *DataStart = (unsigned*)Align(((ulong64)&etext), 4);
	size_t DataSecSz = getDataSecSz();
	unsigned *DataStart;

	if (DataSecSz == -1)
	{
		DataStart = (unsigned*)Align(((ulong64)&etext), 4);
	}
	else
	{
		DataStart = (unsigned*)Align(((ulong64)(&edata - DataSecSz)), 4);
	}
	unsigned *DataEnd = (unsigned*)((ulong64)(&edata) - 7);

	/* scan global variables */
	scanRoots(DataStart, DataEnd);

	unsigned *UnDataStart = (unsigned*)Align(((ulong64)&edata), 4);
	unsigned *UnDataEnd = (unsigned*)((ulong64)(&end) - 7);

	/* scan uninitialized global variables */
	scanRoots(UnDataStart, UnDataEnd);

	
	int Lvar;
	void *Base;
	size_t Size;
	pthread_attr_t Attr;
	
	int Ret = pthread_getattr_np(pthread_self(), &Attr);
	if (Ret != 0)
	{
		printf("Error getting stackinfo\n");
		return;
	}
	Ret = pthread_attr_getstack(&Attr , &Base, &Size);
	if (Ret != 0)
	{
		printf("Error getting stackinfo\n");
		return;
	}
	unsigned *Bottom = (unsigned*)(Base + Size - 7);
	unsigned *Top = (unsigned*)&Lvar;
	Top = (unsigned*)Align((ulong64)Top, 4);
	/* skip GC stack frame */
	while (Top[0] != MAGIC_ADDR)
	{
		assert(Top < Bottom);
		Top++;
	}
	
	/* scan application stack */
	scanRoots(Top, Bottom);
	
	/* call scanner method for mark phase.*/
	scanner();

	/*calling sweep method for sweep phase.*/
	sweep();  
	// printf("marked: %lld\n", marked);
	// printf("freed: %lld\n", freed);
	// printf("total: %lld\n", total);
	#ifdef DEBUG
		printf("entering _runGC()\n");
	#endif
}

static void checkAndRunGC(size_t Sz)
{
	static size_t TotalAlloc = 0;

	TotalAlloc += Sz;
	if (TotalAlloc < GC_THRESHOLD)
	{
		return;
	}
	TotalAlloc = 0;
	_runGC();
}

void printMemoryStats()
{
	printf("Num Bytes Allocated: %lld\n", NumBytesAllocated);
	printf("Num Bytes Freed: %lld\n", NumBytesFreed);
	printf("Num GC Triggered: %lld\n", NumGCTriggered);
}
