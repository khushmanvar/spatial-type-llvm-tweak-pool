#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "memory.h"
#include "support.h"
// #define DEBUG
// #define DEBUG_E
	// #ifdef DEBUG
	// #endif


//* a function which returns number of fields in type from its bitmap.
int giveNumFields(unsigned long long bitmap)
{
	
	if (bitmap==0)
	{
		return 0;
	}
	for (int i=63; i>=0; i--)
	{
	  #ifdef DEBUG_E
	    printf("DEBUG: %d, %lld, %lld, %lld\n", i, bitmap, (bitmap >> i), ((bitmap >> i)&1));
	  #endif
	  if ( ((bitmap >> i)&1) == 1)
	  {
	    return i;
	  }
	}
	return 0;
}


void checkTypeInv(void *Src, unsigned long long DstType)
{
	#ifdef DEBUG
		printf("DEBUG: inside checkTypeInv, Src: %p, DstType: %lld\n", Src, DstType);	
	#endif
	unsigned long long SrcType =  GetType(Src);
	unsigned SrcSize = GetSize(Src);
    int lcm = SrcSize/8;
    int ptrB=0;
    int ptrA=0;
    int count = 0;
    unsigned long long bitmapA = SrcType;
    unsigned long long bitmapB = DstType;
    unsigned typeSatisfied = 1;
    unsigned numfA = giveNumFields(SrcType);
    unsigned numfB = giveNumFields(DstType);
    #ifdef DEBUG
      printf("DEBUG: srcsize: %d, bitmapA: %lld, bitmapB: %lld, numfA: %d, numfB: %d\n , ,",lcm, bitmapA, bitmapB, numfA, numfB);
    #endif
    while(count<lcm)
    {
      unsigned long long bitA = (bitmapA & ((unsigned long long)1<<ptrA));
      unsigned long long bitB = (bitmapB & ((unsigned long long)1<<ptrB));
      #ifdef DEBUG
        printf("DEBUG: count: %d, ptrA: %d, bitA: %lld, ptrB: %d, bitB: %lld\n", count, ptrA, bitA, ptrB, bitB);
      #endif
      if ( (bitA==0 && bitB!=0) || (bitA!=0 && bitB==0) )
      {
        typeSatisfied = 0;
        break;
      }
      ptrA+=1;
      if (ptrA==numfA)
      {
        ptrA = 0;
      } 
      ptrB+=1;     
      if (ptrB==numfB)
      {
        ptrB = 0;
      }
      count+=1;
    }
    
    if (typeSatisfied == 0)
    {
    	printf("ERROR: Type Invariant violated at runtime.");
		exit(0);
    }
}

void checkSizeInv(void *Src, unsigned DstSize) // dst is scr
{
	#ifdef DEBUG
		printf("inside checkSizeInv, Src: %p, DstSize: %d\n", Src, DstSize);
	#endif
	unsigned DstOrigSize = GetSize(Src);
	
	if (DstOrigSize < DstSize)
	{
		printf("Invalid obj size: min_required:%x current:%x\n", 
			(unsigned)DstSize, DstOrigSize);
		exit(0);
	}
}

void checkSizeAndTypeInv(void *Src, unsigned long long DstType, unsigned DstSize)
{
	#ifdef DEBUG
		printf("inside checkSizeAndTypeInv, Src: %p, DstType: %lld, DstSize: %d\n", Src, DstType , DstSize);
	#endif
	checkTypeInv(Src, DstType);
	checkSizeInv(Src, DstSize);
}

void* mycast(void *Ptr, unsigned long long Bitmap, unsigned Size)
{
	#ifdef DEBUG
		printf("inside mycast, Ptr: %p, Bitmap: %lld, Size: %d \n", Ptr, Bitmap, Size);	
	#endif
	checkSizeInv(Ptr, Size);
	SetType(Ptr, Bitmap);
	return Ptr;
}
