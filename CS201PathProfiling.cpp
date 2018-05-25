/*
 * Authors: Aaron Sanders (email: asand017@ucr.edu)
 * 
 */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/CFG.h"
#include "llvm/Analysis/DomPrinter.h"
#include "llvm/Analysis/PostDominators.h"
#include <iostream>
#include <string>
#include <vector>

using namespace llvm;
using namespace std;

int blockNum = 0;

namespace {

  static Function* printf_prototype(LLVMContext& ctx, Module *mod){
    vector<Type*> printf_arg_types;
	printf_arg_types.push_back(Type::getInt8PtrTy(ctx));

	FunctionType* printf_type = FunctionType::get(Type::getInt32Ty(ctx), printf_arg_types, true);
	Function *func = mod->getFunction("printf");
	if(!func){
	  func = Function::Create(printf_type, Function::ExternalLinkage, Twine("printf"), mod);
	}
	func->setCallingConv(CallingConv::C);
	return func;
  }

  struct CS201PathProfiling : public FunctionPass {
    static char ID;
    LLVMContext *Context;
    CS201PathProfiling() : FunctionPass(ID) {}
    GlobalVariable *bbCounter = NULL; // CS210 --- This is were we declare the global variables that will count the edges and paths
    GlobalVariable *BasicBlockPrintfFormatStr = NULL; // " "
    Function *printf_func = NULL;

    //---------------------------------- CS210 --- This function is run once at the beginning of execution. We just initialize our variables/structures here.
    bool doInitialization(Module &M) {
	  errs() << "\n----------Starting Path Profiling----------------\n";
	  Context = &M.getContext();
	  bbCounter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
	  const char *finalPrintString = "BB Count: %d\n";
	  Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
	  BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
	  printf_func = printf_prototype(*Context, &M);
	
	  // CS210 --- We don't need this line, but it returns the name of the module.	
	  //errs() << "Module: " << M.getName() << "\n";
	
      return true;
    }

    //---------------------------------- CS210 --- This function is run once at the end of execution.
    bool doFinalization(Module &M) {
	  errs() << "-----------Finished Path Profiling-------------------\n";
      return false;
    }
    
    //---------------------------------- CS210 --- This function is run for each 'function' in the input test file
	// 
    bool runOnFunction(Function &F) override {
	  errs() << "Function: " << F.getName() << "\n";

	  //construct dominator tree for function F
	  errs() << '\n';
	  DominatorTree *domTree = new DominatorTree();
	  domTree->recalculate(F);
	  domTree->print(errs());
	  errs() << '\n';

	  // CS210 --- loop iterates over each basic block in each function in the input file, calling the runOnBasicBlock function on each encountered basic block
	  for(auto &BB: F){
		//BB.setName("b");
		if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())){
		  //BasicBlock bb = BB.getTerminator().get
		  //addFinalPrintf(BB, Context, bbCounter, BasicBlockPrintfFormatStr, printf_func);
		}


		runOnBasicBlock(BB);
	  }	

	  blockNum = 0;

	  errs() << "Innermost Loops: {}\n";// << /* code */ << "}\n";
	  errs() << "Edge values: {}\n";// << /* code */ << "}\n";
	  errs() << '\n';	
      return true;
    }
	
	// CS210 --- This function is run for each "basic block" in the input test file
	bool runOnBasicBlock(BasicBlock &BB){
	  //BB.setName("b");
	  
      // CS210 --- outputting unique identifier for each encounter Basic Block
	  errs() << "BasicBlock: ";// << BB.getName() << '\n';
	  BB.printAsOperand(errs(), false);//BB.getName() << '\n';
	  errs() << '\n';
	  blockNum++;

	  // CS210 --- These 4 lines incremented bbCounter each time a basic block was accessed in the real-time execution of the input program
	  // The code to increment the edge and path counters will be very similiar to this code 
	  //
	  //IRBuilder<> IRB(BB.getFirstInsertionPt());
	  //Value *loadAddr = IRB.CreateLoad(bbCounter);
	  //Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
	  //IRB.CreateStore(addAddr, bbCounter);
	  //
	  
	  errs() << '\n';	
	  
	  // CS210 --- loop iterates over each instruction in the current Basic Block and outputs the intermediate code
	  for(auto &I: BB){
		if(isa<BranchInst>(I)){
	    	//auto *nb = new BranchInst
		}  
	 	errs() << I << "\n";	
	  }
	  //errs() << BB.getTerminator() << '\n';
	  errs() << '\n';
		
	  return true;
	}


	// CS210 --- We will have to play with these "Printf" functions to output the "profiled program" output a little later	

	//needed to print the bbCounter at end of main
	void addFinalPrintf(BasicBlock& BB, LLVMContext *Context, GlobalVariable *bbCounter, GlobalVariable *var, Function *printf_func){
	  IRBuilder<> builder(BB.getTerminator());
	  vector<Constant*> indices;
	  Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
	  indices.push_back(zero);
	  indices.push_back(zero);
	  Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);
	
	  Value *bbc = builder.CreateLoad(bbCounter);
	  CallInst *call = builder.CreateCall2(printf_func, var_ref, bbc);
	  call->setTailCall(false); 	
	}

  };
}

char CS201PathProfiling::ID = 0;
static RegisterPass<CS201PathProfiling> X("pathProfiling", "CS201PathProfiling Pass", false, false);

