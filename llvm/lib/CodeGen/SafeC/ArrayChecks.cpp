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
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/CodeGen/ValueTypes.h"
#include "llvm/CodeGen/Analysis.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Support/LowLevelTypeImpl.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

namespace {
struct ArrayCheck : public FunctionPass {
  static char ID;
  Function *abort;
  ArrayCheck() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    const DataLayout &DL = F.getParent()->getDataLayout(); //doubt

    //* creating new basic block and splitting the current basic block.
    Type *returntype = F.getReturnType();
    if(abort == NULL)
    {
      FunctionType *FT = FunctionType::get(Type::getVoidTy(F.getContext()),false);
      abort = Function::Create(FT, Function::ExternalLinkage,"abort",F.getParent());
    }
    BasicBlock *bb = BasicBlock::Create(F.getContext(),"newly added",&F);
    IRBuilder<> IRB(bb);
    IRB.CreateCall(abort);
    if(!(returntype->isVoidTy()) )
    {
      Constant *nullvalue = ConstantInt::getNullValue(returntype);
      IRB.CreateRet(nullvalue);
    }
    else
    {
      IRB.CreateRetVoid();
    }

    //* actual pass starts here.
    for (BasicBlock &BB : F) 
    {
      for (Instruction &II : BB)
      {
        if (isa<GetElementPtrInst>(&II))
        {
          GetElementPtrInst * GEP = dyn_cast<GetElementPtrInst>(&II);
          Instruction *Next = II.getNextNode();
          if (isa<GetElementPtrInst>(Next) && Next->getOperand(0)==GEP)
          {
            GetElementPtrInst * GEP_Next = dyn_cast<GetElementPtrInst>(Next);

            auto base = GEP->getOperand(0);          
            ConstantInt *arrayIndex = dyn_cast<ConstantInt>(GEP->getOperand(1));
            if (!arrayIndex){
              continue;
            }
            uint64_t arrayIndexVal = arrayIndex->getZExtValue();
            //* do the following work only if array index is non zero as for 0 we do not nead spatial check in the presence of size invariant.
            if (arrayIndexVal!=0)
            {
              BasicBlock *else_block = SplitBlock(&BB, GEP_Next->getNextNode());
              BB.getTerminator()->eraseFromParent();
              IRBuilder<> IRB(&BB);
              
              //* inserting new IR instructions.
              auto castedBase = IRB.CreateBitCast(base, Type::getInt32PtrTy(F.getContext()));
              auto intToSubtract = ConstantInt::get(IRB.getInt32Ty(),-4);
              auto objHeader = IRB.CreateInBoundsGEP(castedBase, intToSubtract);
              auto objSize = IRB.CreateLoad(IRB.getInt32Ty(), objHeader);
              auto objSizeActual = IRB.CreateSub(objSize, ConstantInt::get(IRB.getInt32Ty(),16));
              auto castedBaseChr = IRB.CreateBitCast(castedBase, Type::getInt8PtrTy(F.getContext()));
              auto lastByteObj = IRB.CreateInBoundsGEP(castedBaseChr, objSizeActual);
              auto castedAccess = IRB.CreateBitCast(Next, Type::getInt8PtrTy(F.getContext()));
              
              //* logic to get correct intToAdd.
              auto PTy = GEP->getPointerOperand()->getType()->getPointerElementType();
              auto ObjSz = DL.getTypeAllocSize(PTy);
              SmallVector<LLT, 8> ValueVTs;
              SmallVector<uint64_t, 8> Offsets;
              computeValueLLTs(DL, *PTy, ValueVTs, &Offsets);
              ConstantInt *structIndex = dyn_cast<ConstantInt>(GEP_Next->getOperand(2));
              if (!structIndex)
              {
                continue;
              }
              uint64_t structIndexVal = structIndex->getZExtValue();  
              uint64_t sizeOfAccess = 0;
              if (structIndexVal == ValueVTs.size()-1)
              {
                sizeOfAccess = ObjSz - (Offsets[structIndexVal]/8);
              }else
              {
                sizeOfAccess = (Offsets[structIndexVal+1] - Offsets[structIndexVal])/8; 
              }
              auto lastByteAccess = IRB.CreateInBoundsGEP(castedAccess, ConstantInt::get(IRB.getInt32Ty(), sizeOfAccess));
              auto instComp = IRB.CreateICmpULT(lastByteObj,lastByteAccess);
              IRB.CreateCondBr(instComp, bb, else_block);
            }           
          }
        }
      }
    }
    return false;
  }
}; // end of struct ArrayCheck
}  // end of anonymous namespace

char ArrayCheck::ID = 0;
static RegisterPass<ArrayCheck> X("arraycheck", "Array Check Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);

static RegisterStandardPasses Y(
    PassManagerBuilder::EP_EarlyAsPossible,
    [](const PassManagerBuilder &Builder,
       legacy::PassManagerBase &PM) { PM.add(new ArrayCheck()); });
