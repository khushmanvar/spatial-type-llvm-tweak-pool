#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/CodeGen/ValueTypes.h"
#include "llvm/CodeGen/Analysis.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Support/LowLevelTypeImpl.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <deque>

// #define DEBUG
// #define DEBUG_E
	// #ifdef DEBUG
	// #endif

using namespace llvm;

namespace {
struct TypeChecker : public FunctionPass {
  static char ID;
  TypeChecker() : FunctionPass(ID) {}

  //* a function to compute bitmap given type(struct).
  unsigned long long computeBitMap(const DataLayout &DL, Type *Ty)
  {
    SmallVector<LLT, 8> ValueVTs;
    SmallVector<uint64_t, 8> Offsets;

    computeValueLLTs(DL, *Ty, ValueVTs, &Offsets);
    unsigned long long bitmap = 0;
    int bitpos = 0;

    for (unsigned i = 0; i < ValueVTs.size(); i++)
    {
      bitpos = Offsets[i] / 64;
      assert(bitpos < 63 && "can not handle more than 63 fields!");
      if (ValueVTs[i].isPointer())
      {
        bitmap |= ((unsigned long long)1 << bitpos); //* correction.
      }
      #ifdef DEBUG_E
        dbgs() << "DEBUG: bitmap: " << bitmap << " bitpos: " << bitpos << " (1 << bitpos): " << ((unsigned long long)1 << bitpos) << "\n";
      #endif
    }

    if (bitmap)
    {
      auto Sz = DL.getTypeAllocSize(Ty);
      assert((Sz & 7) == 0 && "type is not aligned!");
      bitpos++;
      bitmap |= ((unsigned long long)1 << bitpos); //* correction. 
      #ifdef DEBUG_E
        dbgs() << "DEBUG: bitmap: " << bitmap << "bitpos: " << bitpos << "(1 << bitpos): " << ((unsigned long long)1 << bitpos) << "\n";
      #endif   
    }
    return bitmap;
  }

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
        dbgs() << "DEBUG: " << i << ", "<< bitmap << ", " << (bitmap >> i) << ", "<< ((bitmap >> i)&1)<<"\n";
      #endif
      if ( ((bitmap >> i)&1) == 1)
      {
        return i;
      }

    }
    return 0;
  }
  
  //* a function which tells whether type invariant is violated.
  int isTypeViolated(unsigned long long bitmapA, unsigned long long bitmapB, int numfA, int numfB)
  {
    assert(numfA>=numfB);
    if (numfB==0 && numfA>0)
    {
    	return 1;
    }
    int ptrB=0;
    int ptrA=0;
    while (ptrA<numfA)
    { 
      unsigned long long bitA = (bitmapA & ((unsigned long long)1<<ptrA));
      unsigned long long bitB = (bitmapB & ((unsigned long long)1<<ptrB));
      #ifdef DEBUG_E
        dbgs() << "DEBUG: ptrA(bit from right end): "<< ptrA << ", " << bitmapA << ", " << bitA << ", " << bitmapB << ", " << bitB << "\n";
      #endif
      if ( (bitA==0 && bitB!=0) || (bitA!=0 && bitB==0) )
      {
        return 1;
      }
      ptrB+=1; 
      if (ptrB==numfB)
      {
        ptrB = 0;
      }
      ptrA+=1;
    }
    return 0;
  }

  //* a helper function to compute gcd of 2 nos. a and b.
  int gcd(int a, int b)
  {
    int t;
    while(b!=0)
    {
      t = b;
      b = a%b;
      a = t;
    }
    return a;
  }

  //* a function which tells whether type invariant is proven.
  int isTypeProved(unsigned long long bitmapA, unsigned long long bitmapB, int numfA, int numfB)
  {
    if (numfA==0 && numfB==0)
    {
    	return 1;
    }
    if ((numfA==0 && numfB!=0) || (numfA!=0 && numfB==0))
    {
    	return 0;
    }
    int lcm = (numfA*numfB)/gcd(numfA,numfB);
    int ptrB=0;
    int ptrA=0;
    int count = 0;
    #ifdef DEBUG_E
      dbgs() << "DEBUG: lcm: "<< lcm << ", bitmapA: "<< bitmapA << ", bitmapB: " << bitmapB << "\n"; 
    #endif
    while(count<lcm)
    {
      unsigned long long bitA = (bitmapA & ((unsigned long long)1<<ptrA));
      unsigned long long bitB = (bitmapB & ((unsigned long long)1<<ptrB));
      #ifdef DEBUG_E
        dbgs() << "DEBUG: " << ", count: "<< count << " ptrA: "<< ptrA << ", bitA: " << bitA << ", ptrB: "<< ptrB <<", bitB: " << bitB <<"\n";
      #endif
      if ( (bitA==0 && bitB!=0) || (bitA!=0 && bitB==0) )
      {
        return 0;
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
    return 1;
  }


  bool runOnFunction(Function &F) override {
    const DataLayout &DL = F.getParent()->getDataLayout();

    for (BasicBlock &BB : F)
    {
      for (Instruction &II : BB)
      { 
        if (isa<CastInst>(&II))
        {
          CastInst *CI = dyn_cast<CastInst>(&II);
          if (CI && CI->getType()->isPointerTy())
          {
            if (CI->getOperand(0)->getType()->isPointerTy())
            {
              
              //* casting A to B.
              auto B = CI;
              auto PTyB = B->getType()->getPointerElementType();
              auto ObjSzB = DL.getTypeAllocSize(PTyB);
              unsigned long long bitmapB = computeBitMap(DL, PTyB);

              auto A = CI->getOperand(0);
              auto PTyA = A->getType()->getPointerElementType();
              auto ObjSzA = DL.getTypeAllocSize(PTyA);
              unsigned long long bitmapA = computeBitMap(DL, PTyA);

              //* getting no. of fields in objects.
              #ifdef DEBUG
                printf("DEBUG: getting no. of fields in object A.\n");
              #endif 
              int numfA = giveNumFields(bitmapA);
              #ifdef DEBUG
                printf("DEBUG: no. of fields in A is: %d\n", numfA);
                printf("DEBUG: getting no. of fields in object B.\n");
              #endif 
              int numfB = giveNumFields(bitmapB);
              
              //* trying to disprove type invariant.
              #ifdef DEBUG
                printf("DEBUG: no. of fields in B is: %d\n", numfB);
                printf("DEBUG: trying to disprove type invariant\n");
              #endif
              int disproved = 0;
              if (numfA>numfB)
              {
                disproved = isTypeViolated(bitmapA, bitmapB, numfA, numfB);
              }else
              {
                disproved = isTypeViolated(bitmapB, bitmapA, numfB, numfA);
              }
              if (disproved==1)
              {
                // printf("ERROR: type check violated at compile time\n");
                // exit(0); // doubt
                assert(false && "ERROR: type check violated at compile time\n");
              }  

              //* trying to prove the type invariant.
              #ifdef DEBUG
                printf("DEBUG: disproved = %d\n", disproved);
                printf("DEBUG: trying to prove the type invariant.\n");
              #endif
              int proved = isTypeProved(bitmapA, bitmapB, numfA, numfB);
              #ifdef DEBUG
                printf("DEBUG: proved = %d\n", proved);
              #endif

              
              //* imp debugging point.
      			  #ifdef DEBUG
      		 	  	dbgs() << "\n\n***-------------------------DUBUGGING--------------------------------***\n";
                dbgs() << "DEBUG: A: " << A << " PTyA: " << PTyA << " ObjSzA: " << ObjSzA << " bitmapA " << bitmapA << " numfA: " << numfA << "\n";
      		 	  	dbgs() << "DEBUG: B: " << B << " PTyB: " << PTyB << " ObjSzB: " << ObjSzB << " bitmapB " << bitmapB << " numfB: " << numfB << "\n";
      		 	  	dbgs() << "DEBUG: disproved: " << disproved << " proved: " << proved << "\n";
      		 	    dbgs() << "***-------------------------DUBUGGING--------------------------------***\n\n\n";
                printf("DEBUG: inserting correct dynamic checks accordingly.t\n");
              #endif

              //* inserting correct dynamic checks accordingly.
              IRBuilder<> IRB(CI);
              auto Int64Ty = IRB.getInt64Ty();
    	        auto Int32Ty = IRB.getInt32Ty();
	            Module *M = F.getParent();
              if (proved!=1)
              {
                if (ObjSzA<ObjSzB)
                {
                  //* insert checkSizeAndTypeInv.
                  //* void checkSizeAndTypeInv(void *Src, unsigned long long DstType, unsigned DstSize)
	                auto Fn = M->getOrInsertFunction("checkSizeAndTypeInv", Type::getVoidTy(F.getContext()), A->getType(), Int64Ty, Int32Ty);
	                IRB.CreateCall(Fn, {A,ConstantInt::get(Int64Ty, bitmapB) ,ConstantInt::get(Int32Ty, ObjSzB)});	
                }else
                {
                  //* insert checkTypeInv.
                  //* void checkTypeInv(void *Src, unsigned long long DstType)
	                auto Fn = M->getOrInsertFunction("checkTypeInv", Type::getVoidTy(F.getContext()), A->getType(), Int64Ty);
	                IRB.CreateCall(Fn, {A, ConstantInt::get(Int64Ty, bitmapB)});  
                }
              }else
              {
                if (ObjSzA<ObjSzB)
                {
                  //* insert checkSizeInv.
                  //* void checkSizeInv(void *Src, unsigned DstSize)
	                auto Fn = M->getOrInsertFunction("checkSizeInv", Type::getVoidTy(F.getContext()), A->getType(), Int32Ty);
	                IRB.CreateCall(Fn, {A, ConstantInt::get(Int32Ty, ObjSzB)});         
                }
              }
            }
          }
        }
      }
    }
    return false;
  }
}; // end of struct TypeChecker
}  // end of anonymous namespace

char TypeChecker::ID = 0;
static RegisterPass<TypeChecker> X("typechecker", "Type Checker Pass",
                                 false /* Only looks at CFG */,
                                 false /* Analysis Pass */);

static RegisterStandardPasses Y(
    PassManagerBuilder::EP_EarlyAsPossible,
    [](const PassManagerBuilder &Builder,
       legacy::PassManagerBase &PM) { PM.add(new TypeChecker()); });
