/*
 * Authors: Aaron Sanders (email: asand017@ucr.edu), Alvin Thai (email: )
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
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <iostream>
#include <string>
#include <vector>
#include <stack>
#include <algorithm>

using namespace llvm;
using namespace std;

// CS201 --- how we represent our edges
struct Edge{
	BasicBlock *base;
	BasicBlock *end;
	int value;
};

vector<BasicBlock*> BBList; //maintain inorder list of basic blocks (per function)
vector<Edge> edges; //vector of edges (per function)
vector<Edge> old_edges;

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
	GlobalVariable *EdgeProfilePrintfFormatStr = NULL;
	vector<GlobalVariable*> edgeCounters;
    Function *printf_func = NULL;

    //---------------------------------- CS201 --- This function is run once at the beginning of execution. We just initialize our variables/structures here.
    bool doInitialization(Module &M) {
	  errs() << "\n----------Starting Path Profiling----------------\n";
	  Context = &M.getContext();
	
	  for(auto &F : M){
		for(auto &BB : F){
			for(auto &I : BB){
				TerminatorInst *TI = BB.getTerminator();
				for(unsigned int i = 0; i < TI->getNumSuccessors(); i++){
					SplitCriticalEdge(TI, i, this);		
				}		

				if(isa<BranchInst>(I)){

					for(unsigned int i = 0; i < cast<BranchInst>(I).getNumSuccessors(); i++){
						edgeCounters.push_back(new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "edgeCounter"));
						Edge edge{&BB, cast<BranchInst>(I).getSuccessor(i), 0};
						edges.push_back(edge);
					}	
				}
			}
		}
	  }	

	  //errs() << edgeCounters.size() << "\n";
	  //old_edges = edges;	

	  bbCounter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
	  //const char *finalPrintString = "BB Count: %d\n";
	  const char *finalPrintString = "Edge Counter: %d\n"; 

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


 	//CS201 Helper function to print edges with Ball_Laurus value
	void printEdge(Edge &e){
		errs() << "(";
		e.base->printAsOperand(errs(), false);
		errs() << ",";
		e.end->printAsOperand(errs(), false);
		errs() << "," << e.value;
		errs() << ")"; 
	}
 
	//CS201 Helper Function to compute Maximal Spanning Tree
	vector<Edge> computeMST(vector<Edge> &edges){
		vector<Edge> MST; // will hold the maximal spanning tree
		vector<BasicBlock*> MSTbb; //vertices of MST

		vector<Edge> S = edges; //S

		int maxVal;
		int index;
		bool addEdge = true;
		while(MSTbb != BBList){
			//travers S to find edge of maximal value
			if(S.empty())
				break;

			//errs() << "Check on size of S: " << S.size() << "\n";
			for(unsigned int i = 0; i < S.size(); i++){
				if(i == 0){
					maxVal = S[i].value;
					index = i;
					continue;
				}
					
				if(S[i].value > maxVal){
					maxVal = S[i].value;
					index = i;
				}
			}
			//after previous loop, now have candidate edge in S[index]

			//MST is initially empty, so add the edge and record used vertices
			if(MST.empty()){
				//errs() << "empty MST check\n";
				MST.push_back(S[index]);
				MSTbb.push_back(S[index].base);
				MSTbb.push_back(S[index].end);
				//remove edge from S
				S.erase(S.begin()+index);
				continue;
			}else{
				//after the first iteration, need to verify the endpoints of candidate edge not in BBList
				//errs() << "error check\n";
				//errs() << MSTbb.size() << "\n";
				for(unsigned int i = 0; i < MSTbb.size(); i++){
					//errs() << "error check2\n";
					if(S[index].base == MSTbb[i]){
						//errs() << "S[index].base: ";
						//S[index].base->printAsOperand(errs(), false);
						//errs() << "\n";

						//errs() << "MSTbb[" << i << "]: ";
						//MSTbb[i]->printAsOperand(errs(), false);
						//errs() << "\n";
						
						for(unsigned int k = 0; k < MSTbb.size(); k++){
							if(S[index].end == MSTbb[k]){
								//edge endpoints already covered in MST, so don't add edge
								addEdge = false;
							}
						}
					}
				}

				if(addEdge){
					//errs() << "candidate edge is:";
					//printEdge(S[index]);
					//errs() << "\n";				

					MST.push_back(S[index]);
					//but need to make sure we don't add the same vertex twice to MSTbb
					
					bool addBase = true;
					//check S[index].base
					for(unsigned int i = 0; i < MSTbb.size(); i++){
						if(S[index].base == MSTbb[i]){
							addBase = false;
							break;
						}
					}
					
					bool addEnd = true;
					//check S[index].end
					for(unsigned int i = 0; i < MSTbb.size(); i++){
						if(S[index].end == MSTbb[i]){
							addEnd = false;
							break;
						}
					}
	
					if(addBase){
						MSTbb.push_back(S[index].base);
					}
					
					if(addEnd){
						MSTbb.push_back(S[index].end);
					}
					
					S.erase(S.begin()+index);
				}else{//if addEdge = false
					S.erase(S.begin()+index);
					addEdge = true;
				}
				
			}
		}

		/*errs() << "Outputting Maximal Spanning Tree:\n";
		for(unsigned int i = 0; i < MST.size(); i++){
			printEdge(MST[i]);
			errs() << "\n";
		}*/

		/*errs() << "\n";
				//verify MST contains each BB in BBList. If so, break out of loop
				//vector<BasicBlock*> list; //used to check that MST spans every BB in BBList
		errs() << "MSTbb list (size = " << MSTbb.size() << "): \n";
		for(unsigned int x = 0; x < MSTbb.size(); x++){
			MSTbb[x]->printAsOperand(errs(), false);
			errs() << "\n";
		}
		errs() << "\n";*/
	    
		return MST;
	}

	//CS201 Helper Function to assign values to edges (DAG)
	void AssignVal(vector<Edge> &edges){
		//edge value assignment algorithm (Part 1 of 4 - Ball-Larus Algo.):
		//
		//for each vertex v in reverse topological order{
		//	if v is a leaf vertex {
		//		NumPaths(v) = 1
		//  } else {
		//		NumPaths(v) = 0
		//		for each edge e = v->w {
		//			Val(e) = NumPaths(v);
		//			NumPaths(v) = NumPaths(v) + NumPaths(w);
		//		}
		//	}
		//}

		vector<BasicBlock*> topOrder; //topological ordering of 'vertices'
		vector<int> numPaths; //index is aligned with 'topOrder'	

		//errs() << "new size of edges: " << edges.size() << "\n";	
		for(int i = BBList.size() - 1; i >= 0; i--){
			//errs() << i << "\n";
			topOrder.push_back(BBList[i]);	
		}				
	
		numPaths.resize(topOrder.size(), 0);
		/*errs() << "checking topological ordering:\n";
		for(unsigned int i = 0; i < topOrder.size(); i++){
			topOrder[i]->printAsOperand(errs(), false);
			errs() << "\n";
		}*/

		int w; //index for 'w' in 'v->w'
		for(unsigned int i = 0; i < topOrder.size(); i++){
			//edges[i].end is a leaf
			if(topOrder[i]->getTerminator()->getNumSuccessors() == 0){
				numPaths[i] = 1;
			}else{
				numPaths[i] = 0;

				for(unsigned int j = 0; j < edges.size(); j++){
					if(edges[j].base == topOrder[i]){

						//find index of 'end' basic block						
						for(unsigned int y = 0; y < topOrder.size(); y++){
							if(edges[j].end == topOrder[y]){
								w = y;
							}
						}

						//compute value for edge
						edges[j].value = numPaths[i];
						numPaths[i] = numPaths[i] + numPaths[w];
					}
				}
			}
		}
		//errs() << i << "\n";
		
		
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

		//reorder final loop result in descending-CFG order
		vector<BasicBlock*> o_loop; //ordered loop (initially empty)
		//o_loop.reserve(loop.size());
		bool done = false; //set to 'true' when we have ordered everything
		vector<int> BlockPlace; //inorder index of BasicBlocks in loop
		while(!done){
			
			for(unsigned int i = 0; i < loop.size(); i++){
				for(unsigned int j = 0; j < BBList.size(); j++){
					if(loop[i] == BBList[j]){
						//errs() << j << "\n";
						BlockPlace.push_back(j); //vector of indices into 'loop' vector
						break;
					}
				}
			}

			//sorting
			sort(BlockPlace.begin(), BlockPlace.end());
			
			//errs() << "size: " << BlockPlace.size() << "\n";
			for(unsigned int i = 0; i < BlockPlace.size(); i++){
				//errs() << BlockPlace[i] << "\n";
				o_loop.push_back(BBList[BlockPlace[i]]);
			}
	
			done = true;
		}

		return o_loop;
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
	 // vector<Edge> edges; //vector of edges (per function)
	  vector<vector<BasicBlock*>> loops; //will hold all the loops found in the function
	  old_edges = edges;		

	  errs() << "Function: " << F.getName() << "\n";

	  //construct dominator tree for function F
	  DominatorTree *domTree = new DominatorTree();
	  domTree->recalculate(F);
	  //domTree->print(errs());

	  //get basic block list
	  for(auto &BB: F){
		BB.setName("b");
		BBList.push_back(&BB);	
	  }

	  // CS201 --- loop iterates over each basic block in each function in the input file, calling the runOnBasicBlock function on each encountered basic block
	  for(auto &BB: F){		
	  	DomTreeNode *bb = domTree->getNode(&BB);
		funcDomSet.push_back(computeDomSet(F, bb, domTree));
		

	  	/*IRBuilder<> IRB(BB.getFirstInsertionPt()); //gets placed before the first instruction in the basic block
	  	Value *loadAddr = IRB.CreateLoad(bbCounter);
	  	Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
	  	IRB.CreateStore(addAddr, bbCounter);*/

		//FIRST PASS to find EDGES
		//finding back edges -----------------------------------------------------------------------------------------
		/*for(auto &I: BB){
			if(isa<BranchInst>(I)){
				//I is the branch instruction, need to iterate over the instructions successor to find back edge
				for(unsigned int i = 0; i < cast<BranchInst>(I).getNumSuccessors(); i++){
					Edge edge{&BB, cast<BranchInst>(I).getSuccessor(i), 0};
					edges.push_back(edge);
				}	
			}
			
		}*/
		//finding back edges end ---------------------------------------------------------------------------------------

		//SECOND PASS to increment edge counter (EDGE PROFILING DONE HERE)
		for(auto &I: BB){
			if(isa<BranchInst>(I)){

				/*if(cast<BranchInst>(I).getNumSuccessors() == 1){
						IRBuilder<> IRB(&I);
						Value *loadAddr = IRB.CreateLoad(edgeCounters[j]);
						Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
						IRB.CreateStore(addAddr, edgeCounters[j]);
				}*/

				for(unsigned int i = 0; i < cast<BranchInst>(I).getNumSuccessors(); i++){

					for(unsigned int j = 0; j < edges.size(); j++){
						
						if((edges[j].base == &BB) && (edges[j].end == cast<BranchInst>(I).getSuccessor(i))){
						
							if(cast<BranchInst>(I).getNumSuccessors() == 1){
								IRBuilder<> IRB(&I);
								Value *loadAddr = IRB.CreateLoad(edgeCounters[j]);
								Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
								IRB.CreateStore(addAddr, edgeCounters[j]);
							}else{
								IRBuilder<> IRB(cast<BranchInst>(I).getSuccessor(i)->getFirstInsertionPt());
								Value *loadAddr = IRB.CreateLoad(edgeCounters[j]);
								Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
								IRB.CreateStore(addAddr, edgeCounters[j]);
							}

						}
					}

				}
			}
		}
		//

		//FINAL OUTPUT (CHANGE BBCOUNTER)
		if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())){
		   for(unsigned int i = 0; i < edgeCounters.size(); i++){
			
				string result = "";
				if(i == 0){
					result = "EDGE PROFILING:\n";
				}	
			
				//const char *base = (edges[i].base->getName().str()).c_str();
				if(old_edges[i].base->getName().str() == "b"){
					result = result + old_edges[i].base->getName().str() + "0 -> " + old_edges[i].end->getName().str() + ": %d\n"; 
				}else if(old_edges[i].end->getName().str() == "b"){
					result = result + old_edges[i].base->getName().str() + " -> " + old_edges[i].end->getName().str() + "0: %d\n"; 
				}else{
					result = result + old_edges[i].base->getName().str() + " -> " + old_edges[i].end->getName().str() + ": %d\n"; 
				}
	
	  			const char *finalPrintString = result.c_str();//" -> : %d\n"; 
	  			Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
	  			BasicBlockPrintfFormatStr = new GlobalVariable(*(F.getParent()), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
	  			//printf_func = printf_prototype(*Context, &M);

				//addFinalPrintf(BB, Context, edgeCounters[i], BasicBlockPrintfFormatStr, printf_func);
				addFinalPrintf(BB, Context, edgeCounters[i], BasicBlockPrintfFormatStr, printf_func);
		   }
		}

		runOnBasicBlock(BB);
	  }	
	  
	  //store backedges here
	  vector<Edge> backEdges;
	
	  //BBList contains in order basic block
	  //finding/storing backedges ----------------------
	  //errs() << "Printing edge list:\n";
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
	  //errs() << "\n";

	  //errs() << "\nback edges (count: " << backEdges.size() << "):\n";
	  for(unsigned int i = 0; i < backEdges.size(); i++){
		//printEdge(backEdges[i]);	
		//errs() << "\n";

		//verify that 'end' dominates 'base'
		if(domTree->dominates(backEdges[i].end, backEdges[i].base)){
			//pass each backedge into helper function to compute the loop (basicblock) list
			loops.push_back(computeLoop(backEdges[i]));
		}
	  }
	  //errs() << "\n";
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


		
	  //edge value code
		
	  //These 2 lines effectively add basicblocks to function
	  //BasicBlock *entry = BasicBlock::Create(*Context, "ENTRY", &F, &(F.getEntryBlock()));
	  //BasicBlock *exit = BasicBlock::Create(*Context, "EXIT", &F, &(F.getEntryBlock()));

	  //CURRENTLY NEED TO CONVERT CFG TO DAG (LOOK AT NOTES, TABS) TO COMPUTE THE EDGE VALUES
	  BasicBlock *entry = &(F.front()); //value = 99
	  BasicBlock *exit = &(F.back()); //value = 100 (to help distinguish between ENTRY and EXIT dummy edges
	  for(unsigned int i = 0; i < backEdges.size(); i++){
			//add dummy ENTRY edge
			Edge Entry{entry, backEdges[i].end, 99};
			edges.push_back(Entry);

			//add dummy EXIT edge
			Edge Exit{backEdges[i].base, exit, 100};
			edges.push_back(Exit);

			//remove back edge for edge list (graph)
			for(unsigned int j = 0; j < edges.size(); j++){
				if((((backEdges[i].base == edges[j].base) && (backEdges[i].end == edges[j].end))) && ((edges[j].value != 99) && (edges[j].value != 100))){
					edges.erase(edges.begin()+(j));
				}
			}
	  }

	  
	  //'edges' vector now represents the DAG representation of the function
	  AssignVal(edges);
	   
	  /*errs() << "Printing DAG edges:\n";
	  for(unsigned int i = 0; i < edges.size(); i++){
		printEdge(edges[i]);
		errs() << "\n";
	  }
	  errs() << "\n";*/

	  //print out edge values with Ball-Larus values
	  bool printedComma = false;
	  for(unsigned int i = 0; i < loops.size(); i++){
	  	errs() << "Edge Values: {";
		for(unsigned int j = 0; j < loops[i].size(); j++){
			
			for(unsigned int v = 0; v < edges.size(); v++){
				if(loops[i][j] == edges[v].base){
					
					for(unsigned int q = 0; q < loops[i].size(); q++){
					
						if(edges[v].end == loops[i][q]){					
							printEdge(edges[v]);
							if((q+1) < loops[i].size()){
								errs() << ",";
								printedComma = true;
							}
						}
	
					}
				}
			}			

			if(((j+1)) < loops[i].size() && !printedComma){
				errs() << ",";
			}
			printedComma = false;
		}
		errs() << "}\n\n";

      }
		
	  if(loops.size() == 0){
		errs() << "Edge values: {}\n\n";
	  }
		
	  //need to compute maximal cost ST of (DAG) edges
	  vector<Edge> MST = computeMST(edges);
 	  //any edge from 'edges' not in MST are in the 'chord'
	  vector<Edge> chords;
	  for(unsigned int i = 0; i < edges.size(); i++){
		bool notHere = true;
	  	for(unsigned int j = 0; j < MST.size(); j++){
			if((edges[i].base == MST[j].base) && (edges[i].end == MST[j].end) && (edges[i].value == MST[j].value)){
				notHere = false;
			}
		}	
		
		if(notHere){
			chords.push_back(edges[i]);	
		}	
	  }
	
	  /*
	  errs() << "Outputting Maximal Spanning Tree:\n";
	  for(unsigned int i = 0; i < MST.size(); i++){
		  printEdge(MST[i]);
	  	  errs() << "\n";
  	  }
	  errs() << "\n";

	  errs() << "Outputting chord of Maximal Spanning Tree:\n";
	  for(unsigned int i = 0; i < chords.size(); i++){
		  printEdge(chords[i]);
	  	  errs() << "\n";
  	  }
	  errs() << "\n";*/

	  /*for(unsigned int i = 0; i < edges.size(); i++){
		  printEdge(edges[i]);
		  errs() << "\n";
	  }
	  errs() << "\n";*/
	

	  //check that dominator sets are correct
	  //printFuncDomSets(funcDomSet);

	  //check that basic blocks stored in correct order (Use the below commented code to see the BasicBlock identifer mappings)
	  /*errs() << "BBList size (" << BBList.size() << ")\n";
	  for(unsigned int q = 0; q < BBList.size(); q++){
	  	BBList[q]->printAsOperand(errs(), false);
		errs() << " -> b" << q << "\n";		
	  }*/

	  //empty BBList for use in next function
	  BBList.clear();
	  edges.clear();
	  old_edges.clear();
	
      return true;
    }
	
	// CS201 --- This function is run for each "basic block" in the input test file
	bool runOnBasicBlock(BasicBlock &BB){
      // CS201 --- outputting unique identifier for each encounter Basic Block
	  errs() << "BasicBlock: ";// << BB.getName() << '\n';
	  BB.printAsOperand(errs(), false);//BB.getName() << '\n';
	  errs() << '\n';

	  // CS201 --- These 4 lines incremented bbCounter each time a basic block was accessed in the real-time execution of the input program
	  // The code to increment the edge and path counters will be very similiar to this code 
	  

	  /*IRBuilder<> IRB(BB.getFirstInsertionPt()); //gets placed before the first instruction in the basic block
	  Value *loadAddr = IRB.CreateLoad(bbCounter);
	  Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
	  IRB.CreateStore(addAddr, bbCounter);*/
	  
	  
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

