//* TEAM:
//* MEMBER1: Krishna Kariya (2017060)
//* MEMBER2: Fahad Nayyar (2017049)
 
//*  This pass Implementats a data flow analysis to put minimum possible dynamic checks to catch Null Pointer dereferences.

//* TODO: think about possible memory leaks in the implementation.
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
// #include "llvm/IR/BasicBlock.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include <deque>


using namespace llvm;

namespace {
   #define SET std::set<Value *> 
   #define DEQUEUE std::deque<BasicBlock *>
   #define MAP std::map < BasicBlock *,  std::pair < std::map < Value *, int >, std::map < Value *, int > >    > 
   #define VALMAP std::map < Value *, int >
   #define PAIR std::pair < std::map < Value *, int >, std::map < Value *, int > > 
   //#define DEBUG 
struct NullCheck : public FunctionPass {

  static char ID;
  Function *abort;
  NullCheck() : FunctionPass(ID) {

  }

  //* util function to print a valmap.
  void print_map(VALMAP flow_facts)
  {
    dbgs() << "printing map" << "\n";
    for (auto valpair:  flow_facts)
    {
      Value * val = valpair.first;
      dbgs() << *(val) << ": " << flow_facts[val] << "\n";
    } 
  }

  //* util function to print flow_sets of a basic block.
  void print_bb_flow_facts(BasicBlock * BB, MAP flow_sets)
  {
    dbgs() << "flow_facts of basic block " << BB->getName() << ": \n";  
    dbgs() << "in_set: \n";
    VALMAP in_set = flow_sets[BB].first;
    print_map(in_set);
    dbgs() << "out_set: \n";
    VALMAP out_set = flow_sets[BB].second;
    print_map(out_set);
    dbgs() << "\n";
  }

  //* util function to print flow_sets of whole function.
  void print_func_flow_facts(Function * F, MAP flow_sets)
  {
    for (BasicBlock &BB: (*F))
    {
      print_bb_flow_facts(&BB,flow_sets);
    }
  }

  //* util function to see whether there was a change from old_map to new_map.
  bool is_changed(VALMAP old_map, VALMAP new_map)
  {
    for (auto valpair : new_map)
    {
        Value * val = valpair.first;
        if(old_map.find(val) == old_map.end())
        {
          return true;
        }
        else if (new_map[val] != old_map[val])
        {
          return true;
        }
    }
    return false;
  }


  bool runOnFunction(Function &F) override { 
  
  
  dbgs() << "running null pointer analysis on: " << F.getName() << "\n" << "\n"; 
 
   	 
  //* set which will contain pointers to all instructions on which we have to add dynamic check. 
  SET dynamic_check_insts;

  //* initializing flowsets.
  MAP flow_sets; // doubt: how will it get garbage collected?
  for (BasicBlock &BB: F)
  {
    VALMAP in_set;
    VALMAP out_set;
    PAIR flow_facts;
    flow_facts.first = in_set;
    flow_facts.second = out_set;
    flow_sets[&BB] = flow_facts;
  }  

  //* printing all flow sets initializations.
  #ifdef DEBUG
    dbgs() << "flow_sets at the time of initializations: ";
    print_func_flow_facts(&F, flow_sets);
  #endif

  //* getting enrty basic block.
  BasicBlock * entry_BB = &F.getEntryBlock(); 
  
  //* putting all arguments in a dummy map to initilize old_in_set of entry_bb as unsafe.
  VALMAP argument_map;
  #ifdef DEBUG
    dbgs() << "getting arguments of function: \n";
  #endif  
  for(auto arg = F.arg_begin(); arg != F.arg_end(); ++arg) 
  {
    Value * argument = (Value *) arg;  
    Type * arg_type = argument->getType(); 
    #ifdef DEBUG
      dbgs() << "argument: " <<  *argument ;
    #endif
    if (arg_type->isPointerTy())
    {
      #ifdef DEBUG
        dbgs() << " is pointer type.";
      #endif 
      argument_map[argument] = 1;
    }
    #ifdef DEBUG
      dbgs() << "\n";
    #endif
    
  }
  #ifdef DEBUG
    dbgs() << "\n";
  #endif

  //* creating worklist for data flow analysis. Putting entry basic block in work_list.
  DEQUEUE work_list;
  work_list.push_back(entry_BB);

  //* data flow analysis. 
  while(!work_list.empty())
  { 
    //* poppoing the basic block from front of work_list.
    BasicBlock * curr_bb = work_list.at(0);
    work_list.pop_front();
    #ifdef DEBUG
      dbgs() << "popped this basic block from work_list: \n" ;
      dbgs() << *(curr_bb) << "\n";
    #endif
    //* get the old_in_set, old_out_set of this basic block.
    VALMAP old_in_set = flow_sets[curr_bb].first;
    VALMAP old_out_set = flow_sets[curr_bb].second;

    //* initializing new_in_set and new_out_set.
    VALMAP new_in_set;
    VALMAP new_out_set;

    //* if curr_bb is entry_bb then put all argument values in new_in_set as 
    if (curr_bb == entry_BB)
    {
      for (auto valpair : argument_map)
      {
        Value * val = valpair.first;
        int val_safety = valpair.second;
        new_in_set[val] = val_safety;
        #ifdef DEBUG
          dbgs() << "adding argument: " << *(val) << "\n";
        #endif
      }
      //* deleting argument_map after being used.
      argument_map.clear();
    }


    //* apply meet operator.
    for (BasicBlock *pred_bb : predecessors(curr_bb))
    {
      VALMAP pred_out_set = flow_sets[pred_bb].second;
      for (auto valpair: pred_out_set)
      {
        Value * val = valpair.first;
        int val_safety = valpair.second;
        new_in_set[val] |= val_safety; // doubt: taking or.
      }
    }

    //* comparing new_in_set with old_in_set. // doubt: any use?
    // if (!is_changed(old_in_set,new_in_set))
    // {
    //   continue;
    // }

    //* copying new_in_set into new_out_set.
    for (auto valpair : new_in_set)
    {
      Value * val = valpair.first;
      int val_safety = valpair.second;
      new_out_set[val] = val_safety;
    }
    
    //* apply transfer functions to modify new_in_set into new_out_set.
    for (Instruction &I: *curr_bb)
    { 
      #ifdef DEBUG
        dbgs() << "applying transfer function on instruction: "<< (I) << "\n"; 
      #endif
       if (isa<AllocaInst>(&I))
      {
        AllocaInst*AI = dyn_cast<AllocaInst>(&I);
        Type *Ty = AI->getAllocatedType();
        if (Ty->isPointerTy())
        {
          Value * operand = (Value *)AI;
          #ifdef DEBUG
            dbgs() << "Name of alloca operand: " << *(operand) << "\n";
            dbgs() << "\n";
          #endif
          new_out_set[operand] = 2; // doubt . What to mark alloca when we get something already in it in a back loop?
          
        }else
        {
          //doubt : what to do here?
        }
      }

      if (isa<LoadInst>(&I))
      {
       LoadInst *LI = dyn_cast<LoadInst>(&I);
       Value * pointer_operand = LI->getPointerOperand();
       Value * loaded_value = (Value *)LI;

       
       #ifdef DEBUG
        dbgs() << "pointer operand: " << *(pointer_operand) << "\n";
        dbgs() << "loaded value: " << *(loaded_value) << "\n"; // so basicallt this instruction is equivalent to its value.
        dbgs() << "\n"; 
       #endif
       if (new_out_set[pointer_operand]==2 || new_out_set[pointer_operand]==3) // is pointer_operand ia alloca
       {
          if (new_out_set[pointer_operand]==2) // safe alloca.
          {
            new_out_set[loaded_value] = 0; // marking loaded value safe.
          }else
          {
            new_out_set[loaded_value] = 1; // marking loaded value unsafe. 
          }
       }else
       {
          new_out_set[loaded_value] = 1;
          if (new_out_set[pointer_operand]==1 )
          {
            dynamic_check_insts.insert(LI);
            new_out_set[pointer_operand] = 0;
          }
       }  
      }


      if (isa<StoreInst>(&I))
      {
       StoreInst *SI = dyn_cast<StoreInst>(&I);
       Value * value = SI->getValueOperand();
       Value * pointer_operand = SI->getPointerOperand();
       #ifdef DEBUG
        dbgs() << "value : "<< *(value) << "\n";
        dbgs() << "pointer operand: " << *(pointer_operand) << "\n";
        dbgs() << "\n";
       #endif 
       if (new_out_set[pointer_operand]==2 || new_out_set[pointer_operand]==3) // is pointer_operand ia alloca
       {
          if (isa<Constant>(value))
          {
            if(dyn_cast<Constant>(value)->isNullValue()){
              new_out_set[pointer_operand] = 3;
            }
            else{
              new_out_set[pointer_operand] = 2;
            }
          }
          else
          {
            if (new_out_set[value] == 0 || new_out_set[value] == 2) // doubt // 2nd doubt, what if value was not in new_out_set eg it is a constant.
            {
              new_out_set[pointer_operand] = 2;
            }else
            {
              new_out_set[pointer_operand] = 3;
            }
          }
          
            
       }else
       {
          if (new_out_set[pointer_operand] == 1)
          {
            dynamic_check_insts.insert(SI);
            new_out_set[pointer_operand] = 0;
          }
       }

      }

      if (isa<GetElementPtrInst>(&I))
      {
       GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&I);
       Value * pointer_operand = GEP->getPointerOperand();
       Value * return_address = (Value *)GEP;
       #ifdef DEBUG  
        dbgs() << "pointer operand: " << *(pointer_operand) << "\n";
        dbgs() << "return address : " << *(return_address) << "\n";
        dbgs() << "\n";
       #endif
       if (new_out_set[pointer_operand] == 2 || new_out_set[pointer_operand]==3)
       {
        new_out_set[return_address] = 0; 
       }else
       {
        if (new_out_set[pointer_operand] == 1)
        {
          dynamic_check_insts.insert(GEP);
          new_out_set[pointer_operand] = 0; 
        }
        new_out_set[return_address] = 0; // doubt?
       }
      }

      if (isa<CastInst>(&I))
      {
       CastInst *CAI = dyn_cast<CastInst>(&I);
       Value * pointer_operand = CAI->getOperand(0);
       Value * result = (Value * )CAI;
       #ifdef DEBUG
        dbgs() << "pointer operand: " << *(pointer_operand) << "\n";
        dbgs() << "result: " << *(result) << "\n";
        dbgs() << "\n";   
       #endif 
       if (new_out_set[pointer_operand] == 0 || new_out_set[pointer_operand] == 2)
       {
        new_out_set[result] = 0; // doubt: why not 2?
       }else
       {
        new_out_set[result] = 1; // doubt: why not 3?
       }    
      }

      if (isa<CallInst>(&I))
      {
       CallInst *CI = dyn_cast<CallInst>(&I);
       Value * return_value = (Value *)CI; 
       if(CI->isIndirectCall()){
         new_out_set[return_value] = 1;
         Value * pointer_operand = CI->getCalledValue();
         #ifdef DEBUG
          dbgs() << "pointer operand: " << *(pointer_operand) << "\n";
          dbgs() << "return_value: " << *(return_value) << "\n";
          dbgs() << "\n";   
         #endif 
         if (new_out_set[pointer_operand]==1 || new_out_set[pointer_operand]==3)
         {
            dynamic_check_insts.insert(CI);
            new_out_set[pointer_operand] = 0; // why not 2?
         }
       }
       else 
       {
         
         StringRef name = CI->getCalledFunction()->getName();
        
         if (name=="mymalloc") // doubt: don't compare it with string.
         {
            new_out_set[return_value] = 0;
            Value * pointer_operand = CI->getCalledValue();
            #ifdef DEBUG
              dbgs() << "pointer operand: " << *(pointer_operand) << "\n";
              dbgs() << "return_value: " << *(return_value) << "\n";
              dbgs() << "\n";   
            #endif 
         }else
         {
           new_out_set[return_value] = 1;
           Value * pointer_operand = CI->getCalledValue();
           if (new_out_set[pointer_operand]==1 || new_out_set[pointer_operand]==3)
           {
              dynamic_check_insts.insert(CI);
              new_out_set[pointer_operand] = 0; // why not 2?
          #ifdef DEBUG
            dbgs() << "pointer operand: " << *(pointer_operand) << "\n";
            dbgs() << "return_value: " << *(return_value) << "\n";
            dbgs() << "\n";   
          #endif         
         }
         }
       }
      }

      //print_map(new_out_set);
    }

    //* check if outset of curr_bb is changed. If yes, add all its successors to worklist.
    if (is_changed(old_out_set,new_out_set))
    {
      for (BasicBlock * succ_bb : successors(curr_bb))
      {
        work_list.push_back(succ_bb);
      }
    }
    flow_sets[curr_bb].second = new_out_set; 
    flow_sets[curr_bb].first = new_in_set;
  }

  //* adding dynamic checks before all the identified functions:
  dbgs() << "dynamic checks should be inserted before these instructions: \n";
  Type *returntype = F.getReturnType();
  if(abort == NULL){
    FunctionType *FT = FunctionType::get(Type::getVoidTy(F.getContext()),false);
    abort = Function::Create(FT, Function::ExternalLinkage,"abort",F.getParent());
  }
  BasicBlock *bb = BasicBlock::Create(F.getContext(),"newly added",&F);
  IRBuilder<> IRB(bb);
  IRB.CreateCall(abort);
  if(!(returntype->isVoidTy()) ){
    Constant *nullvalue = ConstantInt::getNullValue(returntype);
    IRB.CreateRet(nullvalue);
  }
  else{
    IRB.CreateRetVoid();
  }
  for (Value * dci : dynamic_check_insts)
  {
    dbgs() << *(dci) << "\n";
    Instruction *inst = (Instruction *)dci;
    BasicBlock *b = inst->getParent();
    BasicBlock *else_block = SplitBlock(b,inst);
    b->getTerminator()->eraseFromParent();
    IRBuilder<> IRB(b);
    Value *val;
    if(isa<LoadInst>(inst))
    {
      LoadInst* instruct = dyn_cast<LoadInst>(inst);
      val = instruct->getPointerOperand();
    }
    if(isa<StoreInst>(inst))
    {
      StoreInst* instruct = dyn_cast<StoreInst>(inst);
      val = instruct->getPointerOperand();
    }
    if(isa<GetElementPtrInst>(inst))
    {
      GetElementPtrInst* instruct = dyn_cast<GetElementPtrInst>(inst);
      val = instruct->getPointerOperand();
    }
    if(isa<CallInst>(inst))
    {
      CallInst* instruct = dyn_cast<CallInst>(inst);
      val = instruct->getCalledValue();
    }
    Constant *nullvalue = ConstantInt::getNullValue(val->getType());
    auto cmp = IRB.CreateICmpEQ(val,nullvalue,"comparing pointers");
    IRB.CreateCondBr(cmp,bb,else_block);
  }
  dbgs() << "\n";


    return false;
    }
    LLVMValueRef LLVMGetLastInstruction(LLVMBasicBlockRef BB) 
    {
       BasicBlock *Block = unwrap(BB);
       BasicBlock::iterator I = Block->end();
       if (I == Block->begin())
        return nullptr;
       return wrap(&*--I);
    }  
  }; //end of struct NullCheck
}  // end of anonymous namespace

char NullCheck::ID = 0;
static RegisterPass<NullCheck> X("nullcheck", "Null Check Pass",
                                 false /* Only looks at CFG */,
                                 false /* Analysis Pass */);

static RegisterStandardPasses Y(
    PassManagerBuilder::EP_EarlyAsPossible,
    [](const PassManagerBuilder &Builder,
       legacy::PassManagerBase &PM) { PM.add(new NullCheck()); });
