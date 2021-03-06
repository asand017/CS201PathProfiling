/*
 * Authors: Aaron Sanders (email: asand017@ucr.edu), Alvin Thai (email: athai005@ucr.edu)
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
vector<vector<BasicBlock*>> loops; //will hold all the loops found in the function

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
	vector<GlobalVariable*> edgeCounters; //for edge profiliing
	GlobalVariable* r = NULL;
	//vector<GlobalVariable*> R; //for path profiling instrumentation	
	vector<GlobalVariable*> pathCounters; //for path profiling

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

		return MST;
	}

	//CS201 Helper Function to compute path between successors of head of path and predecessors of the exit node
	bool getPath(vector<Edge> &path, BasicBlock* succ_source, vector<BasicBlock*> &successors, BasicBlock* pred_source, vector<BasicBlock*> &predeccesors){
		//when computing path, find edge from succ_source to pred[i]=succ[y], add it and add edge from pred[i]=succ[y] to pred_source

		bool isPath = false;
		
		//the base case for recursion
		for(unsigned int i = 0; i < edges.size(); i++){
			//this means the path between sources is one edge, push back that one edge and return true
			if(edges[i].base == succ_source && edges[i].end == pred_source){
				path.push_back(edges[i]);
				isPath = true;
				return isPath;
			}
		}


		//For the case when the first edge checked is the chord we're searching for a path for
		//first iterate over exit's predeccesors
		for(unsigned int i = 0; i < predeccesors.size(); i++){
			for(unsigned int y = 0; y < successors.size(); y++){
				if(predeccesors[i] == successors[y]){ // there is a direct path, create
					isPath = true;
					for(unsigned int g = 0; g < edges.size(); g++){
						if(edges[g].base == succ_source && edges[g].end == predeccesors[i]){
							//succ_source --> pred[i]
							path.push_back(edges[g]);

							//pred[i] --> pred_source
							for(unsigned int k = 0; k < edges.size(); k++){
								if(edges[k].base == predeccesors[i] && edges[k].end == pred_source){
									path.push_back(edges[k]);
									return isPath;
									//break;
								}
							}
							//break;
						}
				
						//case when succ source and pred source dont share an edge
						//source --> succ[i]
						for(unsigned int v = 0; v < edges.size(); v++){
							if(edges[v].base == succ_source && edges[v].end == successors[y]){
								path.push_back(edges[v]);
							}						
						}

						//pred[i] --> source	
						for(unsigned int v = 0; v < edges.size(); v++){
							if(edges[v].base == predeccesors[i] && edges[v].end == pred_source){
								path.push_back(edges[v]);
							}						
						}
						return isPath;
					}
					//break;
				}
			}
		}
	
		//if there is no match predeccesors[i] == successors[y], then we need to start a new iteration
		//successors will not chance, predecessors will

		//MAY NEED TO ERROR CHECK FOR COMPLICATION DUE TO DUMMY BACK EDGE (EXIT --> ENTRY)

		//compute new predecessors
		//for each predeccessors, compute a set of their predecessors and call this function with the new data. the first recursive call to return true is the path
		for(unsigned int i = 0; i < predeccesors.size(); i++){
			
			//cross reference BBList
		    int a, b;
			bool skip = false;
			for(unsigned int j = 0; j < BBList.size(); j++){
				if(BBList[j] == predeccesors[i]){
					a = j;
					for(unsigned int l = 0; l < BBList.size(); l++){
						if(BBList[l] == succ_source){
							b = l;
							break;
						}
					}
					
					if(a < b){
						skip = true;
						break;
					}
				}
			}
			
			if(skip)
				continue;
		
			vector<BasicBlock*> new_pred;
			for(unsigned int x = 0; x < edges.size(); x++){
				if(edges[x].end == predeccesors[i]){
					new_pred.push_back(edges[x].base);
				}	
			}
			
			//if there is a path
			if(getPath(path, succ_source, successors, predeccesors[i], new_pred)){
				
				//need to connect pred source to the predeccesor
			
				for(unsigned int x = 0; x < edges.size(); x++){
					if(edges[x].base == predeccesors[i] && edges[x].end == pred_source){
						path.push_back(edges[x]);
					}
				}
								
				/*errs() << "output path (mid algo):\n";
				for(unsigned int x = 0; x < path.size(); x++){
					printEdge(path[x]);
					errs() << "\n";
				}
				errs() << "\n";*/

				isPath = true;
				return isPath;
			}
	
		}

		//return True if there exists a path (putting the path into "path" vector) or false is no path exists
	
		return isPath;
	}

	//CS201 Helper Function to compute part 2 of ball larus algo.
	vector<int> getChordIncs(vector<Edge> &chords, vector<Edge>& edges, vector<Edge>& MST){
		BasicBlock* entry = BBList[0];
		BasicBlock* exit = BBList[BBList.size() - 1];

		vector<BasicBlock*> exitPreds; //vector of the exit node's predecessors
		//have to iterate over the edges to get the exit block predecessors
		for(unsigned int i = 0; i < edges.size(); i++){
			if(edges[i].base == exit && edges[i].end == entry){
				continue;
			}
			
			if(edges[i].end == exit){
				exitPreds.push_back(edges[i].base);
			}
		}

		vector<BasicBlock*> entrySuccs; //same as above but for entry node
		for(unsigned int i = 0; i < edges.size(); i++){
			if(edges[i].base == exit && edges[i].end == entry){
				continue;
			}
				
			if(edges[i].base == entry){
				
				if(entrySuccs.empty()){
					entrySuccs.push_back(edges[i].end);	
				}else{
					bool present = false;
					for(unsigned int r = 0; r < entrySuccs.size(); r++){
						if(entrySuccs[r] == edges[i].end){
							present = true;	
						}
					}
					
					if(!present){
						entrySuccs.push_back(edges[i].end);
					}
				}
			}
		}
			
		/*errs() << "printing exit block's predecessors:\n";	
		for(unsigned int i = 0; i < exitPreds.size(); i++){
			exitPreds[i]->printAsOperand(errs(), false);
			errs() << "\n";
		}
		errs() << "\n";
	
		errs() << "printing entry block's successors:\n";	
		for(unsigned int i = 0; i < entrySuccs.size(); i++){
			entrySuccs[i]->printAsOperand(errs(), false);
			errs() << "\n";
		}
		errs() << "\n";*/


		vector<int> chordIncs; //index matches index of "chords" (ie. Inc(chords[i]) = chordIncs[i]) --> what will be returned
		vector<Edge> spanCycle;
		bool usingChord = false; //presume we are not using chord at begin of algo

		for(unsigned int i = 0; i < chords.size(); i++){
			
			//if the current chord is EXIT --> ENTRY, break out of loop (we done)
			if(chords[i].base == exit && chords[i].end == entry){
				break;
			}

			//errs() << "current chord: \n";
			//printEdge(chords[i]);
			//errs() << "\n\n";			

			for(unsigned int x = 0; x < edges.size(); x++){
				if(spanCycle.empty()){
					//first case: first edge in "edges" is the chord, so need to seach for the path to the chord
					if(edges[x].base == chords[i].base && edges[x].end == chords[i].end && edges[x].value == chords[i].value){
						//set flag that using chord, so revert to default path finding (to 'exit' node)
						usingChord = true;

						//add edge to spanning Cycle
						spanCycle.push_back(edges[x]);

						//compute rest of cycle
						vector<Edge> path;
						
						//get successor options after adding the edge to spanCycle
						vector<BasicBlock*> end_succ;
						BasicBlock* handle = spanCycle.back().end;//endpoint basicblock at the back of the current spanCycle	
						for(unsigned int u = 0; u < edges.size(); u++){
							if(edges[u].base == handle){
								end_succ.push_back(edges[u].end);	
							}	
						}

						/*errs() << "checking successors of last added edge's endpoint (when we already have the chord we need):\n";
						for(unsigned int u = 0; u < end_succ.size(); u++){
							end_succ[u]->printAsOperand(errs(), false);
							errs() << "\n";
						}
						errs() << "\n";*/

						getPath(path, handle, end_succ, exit, exitPreds);
						spanCycle.insert(spanCycle.end(), path.begin(), path.end()); //append path to spanCycle

						//add the backedge from "EXIT --> ENTRY" to finish spanCycle
						for(unsigned int u = 0; u < edges.size(); u++){
							if(edges[u].base == exit && edges[u].end == entry){ //at the dummy backedge
								spanCycle.push_back(edges[u]);
								
								//output path (to check)
								/*errs() << "Checking computed spanning cycle:\n";
								for(unsigned int a = 0; a < spanCycle.size(); a++){
									printEdge(spanCycle[a]);
									errs() << "\n";
								}
								errs() << "\n";*/

								break;
							}
						}

						//spanCycle complete
						break;
					}
					
					//if spanCycle is empty, but the first edge is not the chord.
					//need to find path from "entry" to chord[i].base, then a path from chord[i].end to "exit"
					vector<Edge> path1; //ENTRY to chord[i].base
					vector<Edge> path2; //chord[i].end to EXIT

					vector<BasicBlock*> chordBasePred; //chord[i].base's preds
					for(unsigned int f = 0; f < edges.size(); f++){
						if(edges[f].end == chords[i].base){
							chordBasePred.push_back(edges[f].base);
						}
					}

					vector<BasicBlock*> chordEndSucc; //chord[i].end's succs
					for(unsigned int f = 0; f < edges.size(); f++){
						if(edges[f].base == chords[i].end){
							chordEndSucc.push_back(edges[f].end);
						}
					}

					//'exitPreds' holds Exit block's predecessors
					//'entrySuccs' holds Entry block's successors
					
					//a path exist, add it to the spanCycle
					//ENTRY to chord[i].base
					if(getPath(path1, entry, entrySuccs, chords[i].base, chordBasePred)){
						spanCycle.insert(spanCycle.end(), path1.begin(), path1.end());
					}
	
					spanCycle.push_back(chords[i]);

					//chord[i].end to EXIT
					if(getPath(path2, chords[i].end, chordEndSucc, exit, exitPreds)){	
						spanCycle.insert(spanCycle.end(), path2.begin(), path2.end());
					}

					//add the backedge from "EXIT --> ENTRY" to finish spanCycle
					for(unsigned int u = 0; u < edges.size(); u++){
						if(edges[u].base == exit && edges[u].end == entry){ //at the dummy backedge
							spanCycle.push_back(edges[u]);
							
							//output path (to check)
							/*errs() << "Checking computed spanning cycle:\n";
							for(unsigned int a = 0; a < spanCycle.size(); a++){
								printEdge(spanCycle[a]);
								errs() << "\n";
							}
							errs() << "\n";*/

							break;
						}
					}
					
				}//else if(!spanCycle.empty() && !usingChord){
					//...
				//}
				break;
			} 
		
			//compute chordIncs using spanCycle (add up values of each edge in spanCycle), store in "chordIncs" vector
			
			/*errs() << "Checking computed spanning cycle:\n";
			for(unsigned int a = 0; a < spanCycle.size(); a++){
				printEdge(spanCycle[a]);
				errs() << "\n";
			}
			errs() << "\n";*/
			
			//increment over spanCycle, add the value of each edge to "inc", the push back inc to chordIncs
			int inc = 0;
			for(unsigned int d = 0; d < spanCycle.size(); d++){
				inc += spanCycle[d].value;
			}
			chordIncs.push_back(inc);

			//each chord will have it's own spanCycle to compute, so clear it when done with chords[i]
			spanCycle.clear();
		}
		//errs() << "---------------------------------\n\n";

	
		return chordIncs;
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
	 // vector<vector<BasicBlock*>> loops; //will hold all the loops found in the function
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

	  //attempts to fine tune basic block name for 'b0'
	  for(auto &BB: F){
		if(BB.getName() == "b"){
			BB.setName("b0");
			for(unsigned int i = 0; i < BBList.size(); i++){
				if(BBList[i]->getName() == "b"){
					BBList[i]->setName("b0");
					break;
				}
			}
			break;
		}	
	  }
	  
	  for(auto &BB: F){	
		runOnBasicBlock(BB);
			
	  }

	  // CS201 --- loop iterates over each basic block in each function in the input file, calling the runOnBasicBlock function on each encountered basic block
	  for(auto &BB: F){		
	  	DomTreeNode *bb = domTree->getNode(&BB);
		funcDomSet.push_back(computeDomSet(F, bb, domTree));
		
	  	/*IRBuilder<> IRB(BB.getFirstInsertionPt()); //gets placed before the first instruction in the basic block
	  	Value *loadAddr = IRB.CreateLoad(bbCounter);
	  	Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
	  	IRB.CreateStore(addAddr, bbCounter);*/

		//FIRST PASS to find EDGES (now done at Initialization
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
		   for(unsigned int i = 0; i < edgeCounters.size() + 1; i++){
				string result = "";				

				if(i == edgeCounters.size()){
					result = "PATH PROFILING:\n";
				}else{
				
					//string result = "";
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
					
					if(i == edgeCounters.size() - 1){
						result = result + "\n";
					}
				}
		
	  			const char *finalPrintString = result.c_str();//" -> : %d\n"; 
	  			Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
	  			BasicBlockPrintfFormatStr = new GlobalVariable(*(F.getParent()), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
	  			//printf_func = printf_prototype(*Context, &M);

				//addFinalPrintf(BB, Context, edgeCounters[i], BasicBlockPrintfFormatStr, printf_func);
				if(i < edgeCounters.size()){
					addFinalPrintf(BB, Context, edgeCounters[i], BasicBlockPrintfFormatStr, printf_func);
				}else{
					addFinalPrintf(BB, Context, edgeCounters[i-1], BasicBlockPrintfFormatStr, printf_func);
				}
		   }
		}

		//runOnBasicBlock(BB);
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
			
			//need edge from exit to entry for part 2 of ball larus algo
			Edge Need{exit, entry, 0};
			edges.push_back(Need);

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
	  //bool printedComma = false;
	  bool done = false;
	  vector<BasicBlock*> seen;
	  for(unsigned int i = 0; i < loops.size(); i++){
	  	errs() << "Edge Values: {";
		for(unsigned int j = 0; j < loops[i].size(); j++){
			
			for(unsigned int v = 0; v < edges.size(); v++){
				if(loops[i][j] == edges[v].base){
					
					for(unsigned int q = 0; q < loops[i].size(); q++){
					
						if(edges[v].end == loops[i][q]){					
							printEdge(edges[v]);

							if(seen.size() == 0){
								seen.push_back(edges[v].base);
								seen.push_back(edges[v].end);
							}else{
								bool here = false;
								for(unsigned int e = 0; e < seen.size(); e++){
									if(edges[v].base == seen[e]){
										here = true;
										break;
									}
								}
								
								if(!here)
									seen.push_back(edges[v].base);

								here = false;
								for(unsigned int e = 0; e < seen.size(); e++){
									if(edges[v].end == seen[e]){
										here = true;
										break;
									}
								}
								
								if(!here)
									seen.push_back(edges[v].end);
							}

							//errs() << ",";
							if(seen.size() == loops[i].size()){
								done = true;
							}

							//if(!done){
							//errs() << "seen size: " << seen.size() << "\n";
							errs() << ",";
								//printedComma = true;
							//}
						}
	
					}
				}
			}			

			//errs() << "j: " << j << "\n";
			//if((j+1) < loops[i].size() && !done){// && !printedComma){
			//	errs() << ",";
				//printedComma = false;
			//}
		}
		errs() << "}\n\n";

      }
		
	  if(loops.size() == 0){
		errs() << "Edge values: {}\n\n";
	  }
		
	  //Ball Larus part 2
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

	  //vector of 'chord' increments
	  vector<int> chordInc = getChordIncs(chords, edges, MST); //index matches with chord index

	  //output chordIncs
	  /*errs() << "Inc(chords): \n";
	  for(unsigned int i = 0; i < chordInc.size(); i++){
		errs() << "Inc(";
		printEdge(chords[i]);
		errs() << "): " << chordInc[i] << "\n";
	  }
	  errs() << "\n";*/


      //Part 3 Ball-Larus: Instrumentation
	  
	  //Register Initialization Code
	  //
      //WS.add(ENTRY); /*'WS' --> Working Set<BasicBlock*> */
	  //while not WS.empty() {
	  //	vertex v = WS.remove();
	  //	for each edge e = v->w
	  //		if e is chord edge
	  //			instrument(e, 'r=Inc(e)'));
	  //		else if e is the only incoming edge of w
	  //			WS.add(w);
	  //		else instrument(e, 'r=0');
	  //}


	  vector<BasicBlock*> WS;

	  vector<Edge> instrumentedChords;
	  vector<int> instrumentationR; //holds instrumentation data to be used when we add code to program, 'r=#'
	  for(unsigned int i = 0; i < edges.size(); i++){
		instrumentationR.push_back(0);
	  }

	  //vector<Edge> corresEdgeR;

	  vector<int> instrumentationM; // 'count[...]++'
	  for(unsigned int i = 0; i < edges.size(); i++){
		instrumentationM.push_back(0);
	  }
	  //vector<Edge> corresEdgeM;

	  WS.push_back(BBList[0]); //WS.add(ENTRY)
	  while(!WS.empty()){
	  	BasicBlock* v = WS.back();
		WS.pop_back();
	
		//bool done = false;
		bool isChord = false;
		int chordIndex = 0;
		for(unsigned int i = 0; i < edges.size(); i++){
			if(edges[i].base == v){	
				//if e is chord edge
				for(unsigned int y = 0; y < chords.size(); y++){ //dont want to count dummy backedge
					if(edges[i].base == chords[y].base && edges[i].end == chords[y].end && edges[i].value == chords[y].value){
						//instrumentation[y] = chordInc[y];
						instrumentedChords.push_back(chords[y]);
						isChord = true;
						chordIndex = y;
					}
				}
				
				if(isChord){
					instrumentationR[i] = (chordInc[chordIndex]);
					//corresEdgeR.push_back(edges[i]);
					continue;
				}
				
				//if e is the only incoming edge of w
				int numW = 0;
				for(unsigned int h = 0; h < edges.size(); h++){
					if(edges[h].end == edges[i].end){
						numW++;
					}
				}
				
				if(numW == 1){
					WS.push_back(edges[i].end);
					continue;
				}
			
				//instrumentationR.push_back(0);
				//corresEdgeR.push_back(edges[i]);
				//else instrument (e, 'r=0')
				//instrumentation,
			}
		}

      } //by default if edge is not a chord, assign r=0


	  //Memory Increment Code
	  //
	  //WS.add(EXIT)
	  //while not WS.empty() {
	  //	vertex w = WS.remove();
	  //	for each edge e = v->w
	  // 		if e is a chord edge {
	  //			if e's instrumentation is 'r=Inc(e)'
	  //				instrument(e, 'count[Inc(e)]++');
	  //			else
	  //				instrument(e, 'count[r+Inc(e)]++');
	  //		} else if e is the only outgoing edge of v
	  //			WS.add(v);
	  //		else instrument(e, 'count[r]++');
	  //}
	 
	  WS.push_back(BBList[BBList.size()-1]); //WS.add(EXIT)
	  while(!WS.empty()){
		BasicBlock*	w = WS.back();
		//errs() << "selected w: ";
		//w->printAsOperand(errs(), false);
		//errs() << "\n\n";	

		//errs() << "size of working set: " << WS.size() << "\n\n";

		WS.pop_back();
		
		bool isChord = false;
		int chordIndex = 0;
		for(unsigned int i = 0; i < edges.size(); i++){
			if(edges[i].end == w){	
				//if e is chord edge
				for(unsigned int y = 0; y < chords.size(); y++){ //dont want to count dummy backedge
					if(edges[i].base == chords[y].base && edges[i].end == chords[y].end && edges[i].value == chords[y].value){
						//instrumentation[y] = chordInc[y];

						instrumentedChords.push_back(chords[y]);
						isChord = true;
						chordIndex = y;
					}
				}
				
				if(isChord){
					//instrumentationR[chordIndex] = chordInc[chordIndex];
					/*for(unsigned int n = 0; n < edges.size(); n++){
						//find edges[i]'s instrumentation
						if(edges[n].base == edges[i].base && edges[n].end == edges[i].end && corresEdgeR[n].value == edges[i].value){
							//use 'n' to index instrumentationR
							if(instrumentationR[n] == chordInc[chordIndex]){
								instrumentationM[i] = (chordInc[chordIndex]);
								//corresEdgeM.push_back(edges[i]);
							}else{
								instrumentationM[i] = (instrumentationR[n] + chordInc[chordIndex]);
								corresEdgeM.push_back(edges[i]);
							}
						}
					}*/
					if(instrumentationR[i] == chordInc[chordIndex]){
						instrumentationM[i] = chordInc[chordIndex]; 
					}else{
						instrumentationM[i] = instrumentationR[i] + chordInc[chordIndex];
					}
	
					continue;
				}
				
				//errs() << "w: ";
				//edges[i].base->printAsOperand(errs(), false);
				//errs() << "\n";
				//if e is the only outgoing edge of v
				int num = 0;
				for(unsigned int h = 0; h < edges.size(); h++){
					if(edges[h].base == edges[i].base){
						num++;
					}
				}
					
				//errs() << "num: " << num << "\n";
				if(num == 1){
					WS.push_back(edges[i].base);
					continue;
				}

				//errs() << "corresEdgeR.size(): " << corresEdgeR.size() << "\n";			
				
				//errs() << "current edge: ";
				//printEdge(edges[i]);
				//errs() << "\n";


				/*for(unsigned int n = 0; n < corresEdgeR.size(); n++){
					printEdge(corresEdgeR[n]);
					errs() << "\n";				

					//find edges[i]'s instrumentation
					if(corresEdgeR[n].base == edges[i].base && corresEdgeR[n].end == edges[i].end && corresEdgeR[n].value == edges[i].value){
						errs() << "\ncorresEdgeR: ";
						printEdge(corresEdgeR[n]);
						errs() << "\n";
						errs() << "r = " << instrumentationR[n] << "\n\n";
						
						instrumentationM[i] = (instrumentationR[n]);
						//corresEdgeM.push_back(edges[i]);
						break;
					}
				}*/
				//instrumentationM[i] = instrumentationR[i];
			}
			//errs() << "instrumentions m[" << i << "] = " << instrumentationM[i] << "\n";
		}
		
	  }//by default

	  // Register increment code
	  //
	  //for all uninstrumented chords c
	  //	instrument(c, 'r+=Inc(c)')
	  if(!chords.empty()){	
		  for(unsigned int i = 0; i < chords.size(); i++){
			bool instrmd = false;
			for(unsigned int j = 0; j < instrumentedChords.size(); j++){
				if(chords[i].base == instrumentedChords[j].base && chords[i].end == instrumentedChords[j].end && chords[i].value == instrumentedChords[j].value){
					instrmd = true;	
				}
			}	

			if(!instrmd){
				for(unsigned int k = 0; k < edges.size(); k++){
					if(edges[k].base == chords[i].base && edges[k].end == chords[i].end && edges[k].value == chords[i].value){
						instrumentationR[k] += chordInc[i];
					}
				}
			}
		  }
	  }
	  /*int chordIndex = 0;
	  vector<Edge> chordsToInstr;
	  errs() << "chords size: " << chords.size() << "\n";
	  if(chords.size() != 0){
		  for(unsigned int x = 0; x < chords.size()-1; x++){
			  bool chordInstrumented = false;
			  for(unsigned int i = 0; i < corresEdgeM.size(); i++){
				if(corresEdgeM[i].base == chords[x].base && corresEdgeM[i].end == chords[x].end && corresEdgeM[i].value == chords[x].value){
					chordInstrumented = true;
					chordIndex = x;
				}
			  }
					
			  if(!chordInstrumented){
				for(unsigned int i = 0; i < corresEdgeR.size(); i++){
					if(corresEdgeR[i].base == chords[x].base && corresEdgeR[i].end == chords[x].end && corresEdgeR[i].value == chords[x].value){
						instrumentationR[i] = instrumentationR[i] + chordInc[x];
						break;
					}
				}
			  }
		  }
	  }*/

	  //accesible data: edges, chords, chordInc (1 viewer members in chordInc than in chords), we dont use chords[chords.size()-1] 

	
	  //bbCounter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
	  /*for(unsigned int i = 0; i < corresEdgeR.size(); i++){

	  }*/
 		
	  //errs() << "corresEgdeR size: " << corresEdgeR.size() << "\n";
	  //errs() << "instrumentationM size: " << instrumentationM.size() << "\n";
	  //errs() << "instrumentationR size: " << instrumentationR.size() << "\n";

	
	  //Module* module = F.getParent();
	  //for(unsigned int i = 0; i < edges.size(); i++){
		//pathCounters.push_back(new GlobalVariable(*module, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "pathCounter"));
	  //}


	  //errs() << "path counters size: " << pathCounters.size() << "\n";

	  /*for(unsigned int i = 0; i < edges.size(); i++){
		errs() << instrumentationM[i] << "\n";
	  }
	  errs() << "\n";
	  */

	  //for(unsigned int i = 0; i < edges.size(); i++){
		//errs() << instrumentationR[i] << "\n";
	  //}
	  //errs() << "\n";

	  int i = 0;
	  for(auto &BB: F){
		//runOnBasicBlock(BB);
		if(&BB == BBList[0]){	
		  //Module* module = F.getParent();
		  //for(unsigned int i = 0; i < edges.size(); i++){
			//errs() << "i: " << i << "\n";
			//pathCounters.push_back(new GlobalVariable(*module, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "pathCounter"));
		  //}
			
		  //r = new GlobalVariable(*module, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "register");

		}
		
		//if(r
		
		for(auto &I: BB){
			//at each edge, 
			if(isa<BranchInst>(I)){
				for(unsigned int i = 0; i < cast<BranchInst>(I).getNumSuccessors(); i++){
					for(unsigned int j = 0; j < edges.size(); j++){
						//bool skip = false;
						//we are at the edge
						if((edges[j].base == &BB) && (edges[j].end == cast<BranchInst>(I).getSuccessor(i))){
							
							//for(unsigned int z = 0; z < chords.size()-1; z++){
							//	if(chords[z].base == edges[j].base && chords[z].end == edges[j].end && chords[z].value == edges[j].value){
									
									/*IRBuilder<> IRB(&I);
									Value *loadAddr = IRB.CreateLoad(r);
									Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), chordInc[j]), loadAddr);
									IRB.CreateStore(addAddr, r);
									skip = true;*/
							//	}
							//}
							//if(edges[j].base =
							//if(skip){
							//	continue;
							//} 
							
							
							/*if(cast<BranchInst>(I).getNumSuccessors() == 1){
								IRBuilder<> IRB(&I);
								Value *loadAddr = IRB.CreateLoad(pathCounters[j]);
								Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), instrumentationR[j]), loadAddr);
								IRB.CreateStore(addAddr, pathCounters[j]);
							}else{
								IRBuilder<> IRB(cast<BranchInst>(I).getSuccessor(i)->getFirstInsertionPt());
								Value *loadAddr = IRB.CreateLoad(pathCounters[j]);
								Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), instrumentationR[j]), loadAddr);
								IRB.CreateStore(addAddr, pathCounters[j]);
							}*/

						}
					}

				}
			}
		}

		if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())){
		   //for(unsigned int i = 0; i < pathCounters.size(); i++){
		
				/*vector<int> distinct;
				for(unsigned int t = 0; t < instrumentationR.size(); t++){
					if(distinct.empty()){
						distinct.push_back(instrumentationR[t]);
						continue;
					}
					
					bool add = true;
					for(unsigned int a = 0; a < distinct.size(); a++){
						if(instrumentationR[t] == distinct[a]){
							add = false;	
						}
					}

					if(add){
						distinct.push_back(instrumentationR[t]);
					}
				}	
				//need to reconstruct path - part 4 of ball larus
				//int R
				for(unsigned int t = 0; t < edges.size(); t++){
					if(edges[t].base == BBList[0]){//starting at entry node
							
					}
				}*/
	
				/*string result = "";
				if(i == 0){
					result = "PATH PROFILING:\n";
				}*/	
			
				//const char *base = (edges[i].base->getName().str()).c_str();
				//if(loops[0][0]->getName().str() == "b"){
				//	result = result + "Path_" + loops[0][0]->getName().str() + "0_0: "; 
				//}/*else if(old_edges[i].end->getName().str() == "b"){
				//	result = result + old_edges[i].base->getName().str() + " -> " + old_edges[i].end->getName().str() + "0: %d\n"; 
				//}else{
				//	result = result + old_edges[i].base->getName().str() + " -> " + old_edges[i].end->getName().str() + ": %d\n"; 
				//}*/
				
				//if(instrumentationR[i] != 0){
				//if(!loops.empty()){
				//	errs() << "loops size: " << loops.size() << "\n";
				//	for(unsigned int i = 0; i < loops.size(); i++){
			
				//result = result + "%d\n";
					//}
				//}

				/*const char *finalPrintString = result.c_str();//" -> : %d\n"; 
				Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
				BasicBlockPrintfFormatStr = new GlobalVariable(*(F.getParent()), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
				//printf_func = printf_prototype(*Context, &M);

				//addFinalPrintf(BB, Context, edgeCounters[i], BasicBlockPrintfFormatStr, printf_func);
				addFinalPrintf(BB, Context, r, BasicBlockPrintfFormatStr, printf_func);*/
				
		   //}
		}

		i++;
	  }
	  
	  /*errs() << "Outputting Maximal Spanning Tree:\n";
	  for(unsigned int i = 0; i < MST.size(); i++){
		  printEdge(MST[i]);
	  	  errs() << "\n";
  	  }
	  errs() << "\n";*/

	  /*errs() << "Outputting chords: \n";
	  for(unsigned int i = 0; i < chords.size(); i++){
		  printEdge(chords[i]);
	  	  errs() << "\n";
  	  }
	  errs() << "\n";

	  errs() << "Printed out DAG edges" << "\n";
	  for(unsigned int i = 0; i < edges.size(); i++){
		  printEdge(edges[i]);
		  errs() << "\n";
	  }
	  errs() << "\n";
	

	  //check that dominator sets are correct
	  //printFuncDomSets(funcDomSet);*/

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
	  loops.clear();
	
      return true;
    }
	
	// CS201 --- This function is run for each "basic block" in the input test file
	bool runOnBasicBlock(BasicBlock &BB){
      // CS201 --- outputting unique identifier for each encounter Basic Block
	  errs() << "BasicBlock: ";
	  BB.printAsOperand(errs(), false);
	  errs() << '\n';

	  // CS201 --- These 4 lines incremented bbCounter each time a basic block was accessed in the real-time execution of the input program
	  // The code to increment the edge and path counters will be very similiar to this code 
	  

	  errs() << '\n';	
	  
	  // CS201 --- loop iterates over each instruction in the current Basic Block and outputs the intermediate code
	  for(auto &I: BB){
	 	errs() << I << "\n";	
	  }
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
