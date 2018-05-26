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
#include "llvm/Support/GenericDomTree.h"
#include <iostream>
#include <string>
#include <vector>
#include <stack>

using namespace llvm;
using namespace std;

// CS201 --- how we represent our edges
struct Edge{
	BasicBlock *base;
	BasicBlock *end;
	int value;
};

vector<BasicBlock*> BBList; //maintain inorder list of basic blocks

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
    GlobalVariable *bbCounter = NULL; // CS201 --- This is were we declare the global variables that will count the edges and paths
    GlobalVariable *BasicBlockPrintfFormatStr = NULL; // " "
    Function *printf_func = NULL;

    //---------------------------------- CS201 --- This function is run once at the beginning of execution. We just initialize our variables/structures here.
    bool doInitialization(Module &M) {
	  errs() << "\n----------Starting Path Profiling----------------\n";
	  Context = &M.getContext();
	  bbCounter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
	  const char *finalPrintString = "BB Count: %d\n";
	  Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
	  BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
	  printf_func = printf_prototype(*Context, &M);
	
      return true;
    }

    //---------------------------------- CS201 --- This function is run once at the end of execution.
    bool doFinalization(Module &M) {
	  errs() << "-----------Finished Path Profiling-------------------\n";
      return false;
    }
 
	//CS201 Helper Function to help compute loop (Insert function from algo. in lecture slides)
	void Insert(stack<BasicBlock*> &Stack, vector<BasicBlock*> &loop, BasicBlock* m){
		//Insert Algo. :
		//
		// if m not in Loop then
		// 		Loop = Loop U {m}
		//		push m onto Stack
		// endif
		// EndInsert
		
		bool isIn = false;
		for(unsigned int i = 0; i < loop.size(); i++){
			if(m == loop[i]){
				isIn = true;
			}
		}
		
		if(!isIn){
			loop.push_back(m);
			Stack.push(m);
		}		

	}

	//CS201 Helper function to compute loops
	vector<BasicBlock*> computeLoop(Edge &backEdge){
		//Loop Algo. :
		//
		// Given a back edge, N -> D	
		//
		// Stack = empty
		// Loop = {D}
		// Insert(N)
		//
		// While stack not empty do
		//		pop m --> (top element of stack)
		// 		for each p in pred(m) do 
		//			Insert(p)
		//		endfor
		// endWhile

		vector<BasicBlock*> loop;

		stack<BasicBlock*> Stack; //empty stack
		BasicBlock* N = backEdge.base;
		BasicBlock* D = backEdge.end;
		
		loop.push_back(D);
		Insert(Stack, loop, N);
		while(!Stack.empty()){
			BasicBlock* m = Stack.top();
			Stack.pop();

			for(auto it = pred_begin(m), et = pred_end(m); it != et; ++it){
				BasicBlock* Pred = *it;
				Insert(Stack, loop, Pred);
			}
		}

		return loop;
	}

 	//CS201 Helper function to print edges with Ball_Laurus value
	void printEdge(Edge &e){
		errs() << "(";
		e.base->printAsOperand(errs(), false);
		errs() << ",";
		e.end->printAsOperand(errs(), false);
		errs() << "," << e.value;
		errs() << ")"; 
	}

	//CS201 Helper function - print dominator sets of function
	void printFuncDomSets(vector<vector<BasicBlock*>> &funcDomSet){
		//index of funcDomSet number is the owner of element dominator set
		
		//NEED to ENUMERATE Basic Block names --- HERE
		errs() << "------------Printing Dominator Sets--------------:\n" << '\n';
		for(unsigned int i = 0; i < funcDomSet.size(); i++){

			errs() << "BasicBlock: ";
			BBList[i]->printAsOperand(errs(), false);
			errs() << " Dominator Set\n";
			errs() << "{";

			for(unsigned int j = 0; j < funcDomSet[i].size(); j++){
				
				funcDomSet[i][j]->printAsOperand(errs(), false);
				if((j+1) == funcDomSet[i].size()){
					continue;
				}
				errs() << ", ";
			}

			errs() << "}\n";
			errs() << "\n";				
		}
		errs() << "----------------------END-------------------------:\n" << '\n';				
	}

	//CS201 Helper Function - computer dominator set for given node (basic block) in function
	vector<BasicBlock*> computeDomSet(Function &f, DomTreeNode *node, DominatorTree *domTree){
		vector<BasicBlock*> basicblkDomSet;

		DomTreeNode *start = node;
		for(auto &BB: f){
			DomTreeNode *bb = domTree->getNode(&BB);
			//Check if current bb dominates given "node"
			if(domTree->dominates(bb, start)){
				basicblkDomSet.push_back(&BB);
			}
		}
		

		//return dominator set for given node
		return basicblkDomSet;
	}

    //---------------------------------- CS210 --- This function is run for each 'function' in the input test file
	// 
    bool runOnFunction(Function &F) override {
	  vector<vector<BasicBlock*>> funcDomSet; // each element is dominator set of the function's BBs
	  vector<Edge> edges; //vector of edges (per function)
	  vector<vector<BasicBlock*>> loops; //will hold all the loops found in the function

	  errs() << "Function: " << F.getName() << "\n";

	  //construct dominator tree for function F
	  DominatorTree *domTree = new DominatorTree();
	  domTree->recalculate(F);
	  //domTree->print(errs());

	  //get basic block list
	  for(auto &BB: F){
		BBList.push_back(&BB);	
	  }

	  // CS201 --- loop iterates over each basic block in each function in the input file, calling the runOnBasicBlock function on each encountered basic block
	  for(auto &BB: F){		
	  	DomTreeNode *bb = domTree->getNode(&BB);
		funcDomSet.push_back(computeDomSet(F, bb, domTree));

		//finding back edges -----------------------------------------------------------------------------------------
		errs() << "Looking for backedges:\n";
		for(auto &I: BB){
			if(isa<BranchInst>(I)){
				//I is the branch instruction, need to iterate over the instructions successor to find back edge
				for(unsigned int i = 0; i < cast<BranchInst>(I).getNumSuccessors(); i++){
					Edge edge{&BB, cast<BranchInst>(I).getSuccessor(i), 0};
					edges.push_back(edge);
				}	
			}	
		}
		errs() << '\n';
		//finding back edges end ---------------------------------------------------------------------------------------


		//old code
		//if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())){
		  //BasicBlock bb = BB.getTerminator().get
		  //addFinalPrintf(BB, Context, bbCounter, BasicBlockPrintfFormatStr, printf_func);
		//}

		runOnBasicBlock(BB);
	  }	
	  
	  //store backedges here
	  vector<Edge> backEdges;
	
	  //BBList contains in order basic block
	  //finding/storing backedges ----------------------
	  errs() << "Printing edge list:\n";
	  int indBase = 0;
	  int indEnd = 0;
	  for(unsigned int i = 0; i < edges.size(); i++){
		  //printEdge(edges[i]);
		  //errs() << "\n";

		  //get heirarchy of edge base node
		  for(unsigned int y = 0; y < BBList.size(); y++){
		  	if(BBList[y] == edges[i].base){
				indBase = y;	
			}
		  }

		  //get heirarchy of edge end node
		  for(unsigned int y = 0; y < BBList.size(); y++){
		  	if(BBList[y] == edges[i].end){
				indEnd = y;	
			}
		  }

		  //if |base node| > |end node|, then edge[i] is a back edge
		  if(indBase > indEnd){
			backEdges.push_back(edges[i]);
				
		  }
	
	  }

	  errs() << "\nback edges (count: " << backEdges.size() << "):\n";
	  for(unsigned int i = 0; i < backEdges.size(); i++){
		printEdge(backEdges[i]);	
		errs() << "\n";

		//verify that 'end' dominates 'base'
		if(domTree->dominates(backEdges[i].end, backEdges[i].base)){
			//pass each backedge into helper function to compute the loop (basicblock) list
			loops.push_back(computeLoop(backEdges[i]));
		}
	  }
	  errs() << "\n";
	  //-----------------------------------------

	
	  //Output Loops
	  //errs() << "LOOP COUNT: " << loops.size() << "\n\n";

	  for(unsigned int i = 0; i < loops.size(); i++){
	  	errs() << "Innermost Loops: {";
		for(unsigned int j = 0; j < loops[i].size(); j++){
			loops[i][j]->printAsOperand(errs(), false);
			
			if((j+1) < loops[i].size()){
				errs() << ",";
			}
		}
		errs() << "}\n";

      }
		
	  if(loops.size() == 0){
		errs() << "Innermost Loops: {}\n";
	  }
	
	  errs() << "Edge values: {}\n";// << /* code */ << "}\n";
	  errs() << '\n';

	  //check that dominator sets are correct
	  //printFuncDomSets(funcDomSet);

	  //check that basic blocks stored in correct order
	  /*errs() << "BBList size(" << BBList.size() << ")\n";
	  for(unsigned int q = 0; q < BBList.size(); q++){
	  	BBList[q]->printAsOperand(errs(), false);
		errs() << '\n';		
	  }*/

	  BBList.clear();
	
      return true;
    }
	
	// CS201 --- This function is run for each "basic block" in the input test file
	bool runOnBasicBlock(BasicBlock &BB){
	  //BB.setName("b");
	  
      // CS201 --- outputting unique identifier for each encounter Basic Block
	  errs() << "BasicBlock: ";// << BB.getName() << '\n';
	  BB.printAsOperand(errs(), false);//BB.getName() << '\n';
	  errs() << '\n';

	  // CS201 --- These 4 lines incremented bbCounter each time a basic block was accessed in the real-time execution of the input program
	  // The code to increment the edge and path counters will be very similiar to this code 
	  //
	  //IRBuilder<> IRB(BB.getFirstInsertionPt());
	  //Value *loadAddr = IRB.CreateLoad(bbCounter);
	  //Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
	  //IRB.CreateStore(addAddr, bbCounter);
	  //
	  
	  errs() << '\n';	
	  
	  // CS201 --- loop iterates over each instruction in the current Basic Block and outputs the intermediate code
	  for(auto &I: BB){
		//if(isa<BranchInst>(I)){

		//}  
	 	errs() << I << "\n";	
	  }
	  //errs() << BB.getTerminator() << '\n';
	  errs() << '\n';
		
	  return true;
	}


	// CS201 --- We will have to play with these "Printf" functions to output the "profiled program" output a little later	

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

