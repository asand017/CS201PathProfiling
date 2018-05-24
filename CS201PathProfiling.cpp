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
    GlobalVariable *bbCounter = NULL;
    GlobalVariable *BasicBlockPrintfFormatStr = NULL;
    Function *printf_func = NULL;

    //----------------------------------
    bool doInitialization(Module &M) {
	  errs() << "\n----------Starting Path Profiling----------------\n";
	  Context = &M.getContext();
	  bbCounter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
	  const char *finalPrintString = "BB Count: %d\n";
	  Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
	  BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
	  printf_func = printf_prototype(*Context, &M);
		
	  //errs() << "Module: " << M.getName() << "\n";
	
      return true;
    }

    //----------------------------------
    bool doFinalization(Module &M) {
	  errs() << "-----------Finished Path Profiling-------------------\n";
      return false;
    }
    
    //----------------------------------
    bool runOnFunction(Function &F) override {
	  errs() << "Function: " << F.getName() << "\n";

	  for(auto &BB: F){
		if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())){
		  //addFinalPrintf(BB, Context, bbCounter, BasicBlockPrintfFormatStr, printf_func);
		  errs() << "Innermost Loops: {" << /* code */ << "}\n";
		}
		runOnBasicBlock(BB);
	  }	

	  blockNum = 0;
	  errs() << '\n';	
      return true;
    }

	bool runOnBasicBlock(BasicBlock &BB){
	  errs() << "BasicBlock: b" << blockNum << '\n';//<< BB.getName() << '\n';
	  blockNum++;
	  //IRBuilder<> IRB(BB.getFirstInsertionPt());

	  //Value *loadAddr = IRB.CreateLoad(bbCounter);
	  //Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
	  //IRB.CreateStore(addAddr, bbCounter);
	
	  errs() << '\n';	
	  for(auto &I: BB){
	    errs() << I << "\n";	
	  }
	  errs() << '\n';
		
	  return true;
	}

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

