//===-- Searcher.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Searcher.h"

#include "CoreStats.h"
#include "Executor.h"
#include "PTree.h"
#include "StatsTracker.h"

#include "klee/ExecutionState.h"
#include "klee/Statistics.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/ADT/DiscretePDF.h"
#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/System/Time.h"
#include "klee/Internal/Support/ErrorHandling.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#else
#include "llvm/Constants.h"
#include "llvm/Instructions.h"
#include "llvm/Module.h"
#endif
#include "llvm/Support/CommandLine.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/CallSite.h"
#else
#include "llvm/IR/CallSite.h"
#endif

#include <cassert>
#include <fstream>
#include <climits>

using namespace klee;
using namespace llvm;

namespace {
  cl::opt<bool>
  DebugLogMerge("debug-log-merge");
}

namespace klee {
  extern RNG theRNG;
}

Searcher::~Searcher() {
}

///

ExecutionState &DFSSearcher::selectState() {
  return *states.back();
}

void DFSSearcher::update(ExecutionState *current,
                         const std::vector<ExecutionState *> &addedStates,
                         const std::vector<ExecutionState *> &removedStates) {
  states.insert(states.end(),
                addedStates.begin(),
                addedStates.end());
  for (std::vector<ExecutionState *>::const_iterator it = removedStates.begin(),
                                                     ie = removedStates.end();
       it != ie; ++it) {
    ExecutionState *es = *it;
    if (es == states.back()) {
      states.pop_back();
    } else {
      bool ok = false;

      for (std::vector<ExecutionState*>::iterator it = states.begin(),
             ie = states.end(); it != ie; ++it) {
        if (es==*it) {
          states.erase(it);
          ok = true;
          break;
        }
      }

      assert(ok && "invalid state removed");
    }
  }
}

///

ExecutionState &BFSSearcher::selectState() {
  return *states.front();
}

void BFSSearcher::update(ExecutionState *current,
                         const std::vector<ExecutionState *> &addedStates,
                         const std::vector<ExecutionState *> &removedStates) {
  // Assumption: If new states were added KLEE forked, therefore states evolved.
  // constraints were added to the current state, it evolved.
  if (!addedStates.empty() && current &&
      std::find(removedStates.begin(), removedStates.end(), current) ==
          removedStates.end()) {
    assert(states.front() == current);
    states.pop_front();
    states.push_back(current);
  }

  states.insert(states.end(),
                addedStates.begin(),
                addedStates.end());
  for (std::vector<ExecutionState *>::const_iterator it = removedStates.begin(),
                                                     ie = removedStates.end();
       it != ie; ++it) {
    ExecutionState *es = *it;
    if (es == states.front()) {
      states.pop_front();
    } else {
      bool ok = false;

      for (std::deque<ExecutionState*>::iterator it = states.begin(),
             ie = states.end(); it != ie; ++it) {
        if (es==*it) {
          states.erase(it);
          ok = true;
          break;
        }
      }

      assert(ok && "invalid state removed");
    }
  }
}

///

ExecutionState &RandomSearcher::selectState() {
  return *states[theRNG.getInt32()%states.size()];
}

void
RandomSearcher::update(ExecutionState *current,
                       const std::vector<ExecutionState *> &addedStates,
                       const std::vector<ExecutionState *> &removedStates) {
  states.insert(states.end(),
                addedStates.begin(),
                addedStates.end());
  for (std::vector<ExecutionState *>::const_iterator it = removedStates.begin(),
                                                     ie = removedStates.end();
       it != ie; ++it) {
    ExecutionState *es = *it;
    bool ok = false;

    for (std::vector<ExecutionState*>::iterator it = states.begin(),
           ie = states.end(); it != ie; ++it) {
      if (es==*it) {
        states.erase(it);
        ok = true;
        break;
      }
    }
    
    assert(ok && "invalid state removed");
  }
}

///

WeightedRandomSearcher::WeightedRandomSearcher(WeightType _type)
  : states(new DiscretePDF<ExecutionState*>()),
    type(_type) {
  switch(type) {
  case Depth: 
    updateWeights = false;
    break;
  case InstCount:
  case CPInstCount:
  case QueryCost:
  case MinDistToUncovered:
  case CoveringNew:
    updateWeights = true;
    break;
  default:
    assert(0 && "invalid weight type");
  }
}

WeightedRandomSearcher::~WeightedRandomSearcher() {
  delete states;
}

ExecutionState &WeightedRandomSearcher::selectState() {
  return *states->choose(theRNG.getDoubleL());
}

double WeightedRandomSearcher::getWeight(ExecutionState *es) {
  switch(type) {
  default:
  case Depth: 
    return es->weight;
  case InstCount: {
    uint64_t count = theStatisticManager->getIndexedValue(stats::instructions,
                                                          es->pc->info->id);
    double inv = 1. / std::max((uint64_t) 1, count);
    return inv * inv;
  }
  case CPInstCount: {
    StackFrame &sf = es->stack.back();
    uint64_t count = sf.callPathNode->statistics.getValue(stats::instructions);
    double inv = 1. / std::max((uint64_t) 1, count);
    return inv;
  }
  case QueryCost:
    return (es->queryCost < .1) ? 1. : 1./es->queryCost;
  case CoveringNew:
  case MinDistToUncovered: {
    uint64_t md2u = computeMinDistToUncovered(es->pc,
                                              es->stack.back().minDistToUncoveredOnReturn);

    double invMD2U = 1. / (md2u ? md2u : 10000);
    if (type==CoveringNew) {
      double invCovNew = 0.;
      if (es->instsSinceCovNew)
        invCovNew = 1. / std::max(1, (int) es->instsSinceCovNew - 1000);
      return (invCovNew * invCovNew + invMD2U * invMD2U);
    } else {
      return invMD2U * invMD2U;
    }
  }
  }
}

void WeightedRandomSearcher::update(
    ExecutionState *current, const std::vector<ExecutionState *> &addedStates,
    const std::vector<ExecutionState *> &removedStates) {
  if (current && updateWeights &&
      std::find(removedStates.begin(), removedStates.end(), current) ==
          removedStates.end())
    states->update(current, getWeight(current));

  for (std::vector<ExecutionState *>::const_iterator it = addedStates.begin(),
                                                     ie = addedStates.end();
       it != ie; ++it) {
    ExecutionState *es = *it;
    states->insert(es, getWeight(es));
  }

  for (std::vector<ExecutionState *>::const_iterator it = removedStates.begin(),
                                                     ie = removedStates.end();
       it != ie; ++it) {
    states->remove(*it);
  }
}

bool WeightedRandomSearcher::empty() { 
  return states->empty(); 
}

///

RandomPathSearcher::RandomPathSearcher(Executor &_executor)
  : executor(_executor) {
}

RandomPathSearcher::~RandomPathSearcher() {
}

ExecutionState &RandomPathSearcher::selectState() {
  unsigned flips=0, bits=0;
  PTree::Node *n = executor.processTree->root;
  
  while (!n->data) {
    if (!n->left) {
      n = n->right;
    } else if (!n->right) {
      n = n->left;
    } else {
      if (bits==0) {
        flips = theRNG.getInt32();
        bits = 32;
      }
      --bits;
      n = (flips&(1<<bits)) ? n->left : n->right;
    }
  }

  return *n->data;
}

void
RandomPathSearcher::update(ExecutionState *current,
                           const std::vector<ExecutionState *> &addedStates,
                           const std::vector<ExecutionState *> &removedStates) {
}

bool RandomPathSearcher::empty() { 
  return executor.states.empty(); 
}

///

BumpMergingSearcher::BumpMergingSearcher(Executor &_executor, Searcher *_baseSearcher) 
  : executor(_executor),
    baseSearcher(_baseSearcher),
    mergeFunction(executor.kmodule->kleeMergeFn) {
}

BumpMergingSearcher::~BumpMergingSearcher() {
  delete baseSearcher;
}

///

Instruction *BumpMergingSearcher::getMergePoint(ExecutionState &es) {  
  if (mergeFunction) {
    Instruction *i = es.pc->inst;

    if (i->getOpcode()==Instruction::Call) {
      CallSite cs(cast<CallInst>(i));
      if (mergeFunction==cs.getCalledFunction())
        return i;
    }
  }

  return 0;
}

ExecutionState &BumpMergingSearcher::selectState() {
entry:
  // out of base states, pick one to pop
  if (baseSearcher->empty()) {
    std::map<llvm::Instruction*, ExecutionState*>::iterator it = 
      statesAtMerge.begin();
    ExecutionState *es = it->second;
    statesAtMerge.erase(it);
    ++es->pc;

    baseSearcher->addState(es);
  }

  ExecutionState &es = baseSearcher->selectState();

  if (Instruction *mp = getMergePoint(es)) {
    std::map<llvm::Instruction*, ExecutionState*>::iterator it = 
      statesAtMerge.find(mp);

    baseSearcher->removeState(&es);

    if (it==statesAtMerge.end()) {
      statesAtMerge.insert(std::make_pair(mp, &es));
    } else {
      ExecutionState *mergeWith = it->second;
      if (mergeWith->merge(es)) {
        // hack, because we are terminating the state we need to let
        // the baseSearcher know about it again
        baseSearcher->addState(&es);
        executor.terminateState(es);
      } else {
        it->second = &es; // the bump
        ++mergeWith->pc;

        baseSearcher->addState(mergeWith);
      }
    }

    goto entry;
  } else {
    return es;
  }
}

void BumpMergingSearcher::update(
    ExecutionState *current, const std::vector<ExecutionState *> &addedStates,
    const std::vector<ExecutionState *> &removedStates) {
  baseSearcher->update(current, addedStates, removedStates);
}

///

MergingSearcher::MergingSearcher(Executor &_executor, Searcher *_baseSearcher) 
  : executor(_executor),
    baseSearcher(_baseSearcher),
    mergeFunction(executor.kmodule->kleeMergeFn) {
}

MergingSearcher::~MergingSearcher() {
  delete baseSearcher;
}

///

Instruction *MergingSearcher::getMergePoint(ExecutionState &es) {
  if (mergeFunction) {
    Instruction *i = es.pc->inst;

    if (i->getOpcode()==Instruction::Call) {
      CallSite cs(cast<CallInst>(i));
      if (mergeFunction==cs.getCalledFunction())
        return i;
    }
  }

  return 0;
}

ExecutionState &MergingSearcher::selectState() {
  // FIXME: this loop is endless if baseSearcher includes RandomPathSearcher.
  // The reason is that RandomPathSearcher::removeState() does nothing...
  while (!baseSearcher->empty()) {
    ExecutionState &es = baseSearcher->selectState();
    if (getMergePoint(es)) {
      baseSearcher->removeState(&es, &es);
      statesAtMerge.insert(&es);
    } else {
      return es;
    }
  }
  
  // build map of merge point -> state list
  std::map<Instruction*, std::vector<ExecutionState*> > merges;
  for (std::set<ExecutionState*>::const_iterator it = statesAtMerge.begin(),
         ie = statesAtMerge.end(); it != ie; ++it) {
    ExecutionState &state = **it;
    Instruction *mp = getMergePoint(state);
    
    merges[mp].push_back(&state);
  }
  
  if (DebugLogMerge)
    llvm::errs() << "-- all at merge --\n";
  for (std::map<Instruction*, std::vector<ExecutionState*> >::iterator
         it = merges.begin(), ie = merges.end(); it != ie; ++it) {
    if (DebugLogMerge) {
      llvm::errs() << "\tmerge: " << it->first << " [";
      for (std::vector<ExecutionState*>::iterator it2 = it->second.begin(),
             ie2 = it->second.end(); it2 != ie2; ++it2) {
        ExecutionState *state = *it2;
        llvm::errs() << state << ", ";
      }
      llvm::errs() << "]\n";
    }

    // merge states
    std::set<ExecutionState*> toMerge(it->second.begin(), it->second.end());
    while (!toMerge.empty()) {
      ExecutionState *base = *toMerge.begin();
      toMerge.erase(toMerge.begin());
      
      std::set<ExecutionState*> toErase;
      for (std::set<ExecutionState*>::iterator it = toMerge.begin(),
             ie = toMerge.end(); it != ie; ++it) {
        ExecutionState *mergeWith = *it;
        
        if (base->merge(*mergeWith)) {
          toErase.insert(mergeWith);
        }
      }
      if (DebugLogMerge && !toErase.empty()) {
        llvm::errs() << "\t\tmerged: " << base << " with [";
        for (std::set<ExecutionState*>::iterator it = toErase.begin(),
               ie = toErase.end(); it != ie; ++it) {
          if (it!=toErase.begin()) llvm::errs() << ", ";
          llvm::errs() << *it;
        }
        llvm::errs() << "]\n";
      }
      for (std::set<ExecutionState*>::iterator it = toErase.begin(),
             ie = toErase.end(); it != ie; ++it) {
        std::set<ExecutionState*>::iterator it2 = toMerge.find(*it);
        assert(it2!=toMerge.end());
        executor.terminateState(**it);
        toMerge.erase(it2);
      }

      // step past merge and toss base back in pool
      statesAtMerge.erase(statesAtMerge.find(base));
      ++base->pc;
      baseSearcher->addState(base);
    }  
  }
  
  if (DebugLogMerge)
    llvm::errs() << "-- merge complete, continuing --\n";
  
  return selectState();
}

void
MergingSearcher::update(ExecutionState *current,
                        const std::vector<ExecutionState *> &addedStates,
                        const std::vector<ExecutionState *> &removedStates) {
  if (!removedStates.empty()) {
    std::vector<ExecutionState *> alt = removedStates;
    for (std::vector<ExecutionState *>::const_iterator
             it = removedStates.begin(),
             ie = removedStates.end();
         it != ie; ++it) {
      ExecutionState *es = *it;
      std::set<ExecutionState*>::const_iterator it2 = statesAtMerge.find(es);
      if (it2 != statesAtMerge.end()) {
        statesAtMerge.erase(it2);
        alt.erase(std::remove(alt.begin(), alt.end(), es), alt.end());
      }
    }    
    baseSearcher->update(current, addedStates, alt);
  } else {
    baseSearcher->update(current, addedStates, removedStates);
  }
}

///

BatchingSearcher::BatchingSearcher(Searcher *_baseSearcher,
                                   double _timeBudget,
                                   unsigned _instructionBudget) 
  : baseSearcher(_baseSearcher),
    timeBudget(_timeBudget),
    instructionBudget(_instructionBudget),
    lastState(0) {
  
}

BatchingSearcher::~BatchingSearcher() {
  delete baseSearcher;
}

ExecutionState &BatchingSearcher::selectState() {
  if (!lastState || 
      (util::getWallTime()-lastStartTime)>timeBudget ||
      (stats::instructions-lastStartInstructions)>instructionBudget) {
    if (lastState) {
      double delta = util::getWallTime()-lastStartTime;
      if (delta>timeBudget*1.1) {
        klee_message("increased time budget from %f to %f\n", timeBudget,
                     delta);
        timeBudget = delta;
      }
    }
    lastState = &baseSearcher->selectState();
    lastStartTime = util::getWallTime();
    lastStartInstructions = stats::instructions;
    return *lastState;
  } else {
    return *lastState;
  }
}

void
BatchingSearcher::update(ExecutionState *current,
                         const std::vector<ExecutionState *> &addedStates,
                         const std::vector<ExecutionState *> &removedStates) {
  if (std::find(removedStates.begin(), removedStates.end(), lastState) !=
      removedStates.end())
    lastState = 0;
  baseSearcher->update(current, addedStates, removedStates);
}

/***/

IterativeDeepeningTimeSearcher::IterativeDeepeningTimeSearcher(Searcher *_baseSearcher)
  : baseSearcher(_baseSearcher),
    time(1.) {
}

IterativeDeepeningTimeSearcher::~IterativeDeepeningTimeSearcher() {
  delete baseSearcher;
}

ExecutionState &IterativeDeepeningTimeSearcher::selectState() {
  ExecutionState &res = baseSearcher->selectState();
  startTime = util::getWallTime();
  return res;
}

void IterativeDeepeningTimeSearcher::update(
    ExecutionState *current, const std::vector<ExecutionState *> &addedStates,
    const std::vector<ExecutionState *> &removedStates) {
  double elapsed = util::getWallTime() - startTime;

  if (!removedStates.empty()) {
    std::vector<ExecutionState *> alt = removedStates;
    for (std::vector<ExecutionState *>::const_iterator
             it = removedStates.begin(),
             ie = removedStates.end();
         it != ie; ++it) {
      ExecutionState *es = *it;
      std::set<ExecutionState*>::const_iterator it2 = pausedStates.find(es);
      if (it2 != pausedStates.end()) {
        pausedStates.erase(it2);
        alt.erase(std::remove(alt.begin(), alt.end(), es), alt.end());
      }
    }    
    baseSearcher->update(current, addedStates, alt);
  } else {
    baseSearcher->update(current, addedStates, removedStates);
  }

  if (current &&
      std::find(removedStates.begin(), removedStates.end(), current) ==
          removedStates.end() &&
      elapsed > time) {
    pausedStates.insert(current);
    baseSearcher->removeState(current);
  }

  if (baseSearcher->empty()) {
    time *= 2;
    klee_message("increased time budget to %f\n", time);
    std::vector<ExecutionState *> ps(pausedStates.begin(), pausedStates.end());
    baseSearcher->update(0, ps, std::vector<ExecutionState *>());
    pausedStates.clear();
  }
}

/***/

InterleavedSearcher::InterleavedSearcher(const std::vector<Searcher*> &_searchers)
  : searchers(_searchers),
    index(1) {
}

InterleavedSearcher::~InterleavedSearcher() {
  for (std::vector<Searcher*>::const_iterator it = searchers.begin(),
         ie = searchers.end(); it != ie; ++it)
    delete *it;
}

ExecutionState &InterleavedSearcher::selectState() {
  Searcher *s = searchers[--index];
  if (index==0) index = searchers.size();
  return s->selectState();
}

void InterleavedSearcher::update(
    ExecutionState *current, const std::vector<ExecutionState *> &addedStates,
    const std::vector<ExecutionState *> &removedStates) {
  for (std::vector<Searcher*>::const_iterator it = searchers.begin(),
         ie = searchers.end(); it != ie; ++it)
    (*it)->update(current, addedStates, removedStates);
}

MCTSSearcher::MCTSSearcher(Executor &_executor, MCTSType _type):executor(_executor){
  tree = MCTSTree();
  type = _type;
}

MCTSSearcher::~MCTSSearcher(){
}

ExecutionState &MCTSSearcher::selectState() {
  // return ExecutionState ,which is has max coverage
  if ((tree.current->state == NULL)) {
    //std::set<BasicBlock*> bbset;
    //std::set<BasicBlock*> bbqueue;
    BasicBlock *bb = firstState->bb;
    // *aa << "add" << " " << firstState << " " << firstState->bb << '\n';
    //go(bb,bbset);
  }
  MCTSNode* node = tree.select_node();
  return *(node->state);
}
/*void MCTSSearcher::go (BasicBlock *bb, std::set<BasicBlock*> bbset) {
	while (bb != NULL){
        if(bbset.find(bb) != bbset.end()) {
          break;
        } else {
          bbset.insert(bb);
          if (bbset.size()%10==0){
            *aa << "temp size " << bbset.size() << '\n';
            (*aa).flush();
          }
        }
        const TerminatorInst* TInst = bb->getTerminator();
        if (TInst->getNumSuccessors() > 0){
          for (unsigned int i =0; i < TInst->getNumSuccessors(); i++){
            go(TInst->getSuccessor(i),bbset);
          }
        }
        else
          break;
    }
}*/

void MCTSSearcher::update(ExecutionState *current,
                         const std::vector<ExecutionState *> &addedStates,
                         const std::vector<ExecutionState *> &removedStates) {
  //klee will use the selectState() to select one state and execute one instruction.

  //1. when meet branch it will change the current state and fork a new state
  //both of states I think as new states in MCTS

  //2. when meet branch end it kill remove state from stucture
  //I will denote this state "Terminated" in MCTS
  //here is very slow

  //if any change in the MCTS I need to refresh_tree() or just keep klee to explore most coverage node

  if (addedStates.size() > 0){
    // *aa << "mcts" << current << '\n';
    if (current == tree.current->state){
      tree.current->clean_node();
    } else {
      tree.delet_dead_node(current);
    }
    for (std::vector<ExecutionState *>::const_iterator it = addedStates.begin() ; it != addedStates.end(); ++it) {
      add_child(*it);
    }
    if (current != NULL){
      // if current at the root current, root null pointer don't have to keep in the MCTSTree
      add_child(current);
    } else {
      firstState = *(addedStates.begin());
    }
    tree.refresh_tree(tree.current);
  }
  if (removedStates.size() > 0){
    for (std::vector<ExecutionState *>::const_iterator it = removedStates.begin() ; it != removedStates.end(); ++it) {
      // I do nothing here because I mark "change"
      // If it has no child refresh_tree() will mark "Terminated" in MCTS
      if (*it == tree.current->state){
        tree.current->clean_node();
        tree.refresh_tree(tree.current);
      } else {
        tree.delet_dead_node(*it);
        tree.refresh_tree(tree.current);
      }
    }
  }
}

void MCTSSearcher::add_child(ExecutionState *state){
  double value =0;
  bool cal_coverage = false;
  bool cal_cost = false;
  switch(type){
  default:
  case CoverageCP:
  case Coverage:
    cal_coverage = true;
    if (type == Coverage)
      break;
  case CoveringNew:
    cal_cost = true;
  }
  double coverage =0;
  if (cal_coverage) {
    double avgCount =0;
    double totalCount =0;
    int simulateTimes =10;
    for (int times =0; times < simulateTimes; times++){
      totalCount +=_simulate_future(state);
    }
    //*aa << state->pc->info->file << ' ' << state->pc->info->line << '\n';
    avgCount = totalCount / simulateTimes;
    coverage = avgCount;
  }
  uint64_t md2u =0;
  int pastCovNew =0;
  if (cal_cost) {
      md2u = computeMinDistToUncovered(state->pc,
                                            state->stack.back().minDistToUncoveredOnReturn);

      pastCovNew = std::max(1, (int) state->instsSinceCovNew - 1000);
  }
  switch(type){
  default:
  case CoverageCP:
  case Coverage:
    // TODO: cal coverage as MCTS-AMAF
    if (type == Coverage){
      value = coverage;
      break;
    }
  case CoveringNew:
    if (type == CoveringNew){
      double invMD2U = 1. / (md2u ? md2u : 10000);
      double invCovNew = 0.;
      if (state->instsSinceCovNew)
        invCovNew = 1. / pastCovNew;

      double invCost = (invCovNew * invCovNew + invMD2U * invMD2U);
      value = invCost;
      break;
    } else {
      int cost = (md2u + pastCovNew) ? (md2u + pastCovNew) : 1;
      value = coverage / cost;
      break;
    }
  }
  tree.add_child(state, "", value);
}

int MCTSSearcher::_simulate_future (ExecutionState *state){
  // traverse in this function first, use basic block
  // then go in into function call, use call instruction
  int count =500;
  std::set<BasicBlock*> bbset;
  std::map<BasicBlock*, int> bbmap;
  std::set<BasicBlock*> bbqueue;
  BasicBlock *bb = state->pc->inst->getParent();
  bbqueue.insert(bb);
  while (bbqueue.size() != 0 && count >= 0){
    bb = *(bbqueue.begin());
    bbqueue.erase(bbqueue.begin());
    while (bb != NULL && count >= 0){
      // new BasicBlock come in
      bbset.insert(bb);
      if (!bbmap[bb])
	      bbmap[bb] = count/2;

      //check if have function call
      for (BasicBlock::iterator BI=bb->begin(),BE=bb->end(); BI!=BE; BI++) {
        Instruction* inst = BI;
        if (isa<CallInst>(inst)) {
          CallInst* ci = (CallInst*) inst;
          if (ci->getCalledFunction()!=NULL) {
            Function *fc = ci->getCalledFunction();
            if (fc->size() > 0){
              Function::iterator FI=fc->begin();
              BasicBlock *newbb = FI;
              bbqueue.insert(newbb);
            }
          }
        }
      }

      // traverse in this function
      const TerminatorInst* TInst = bb->getTerminator();
      if (TInst == NULL){
        continue;
      }
      if (TInst->getNumSuccessors() > 0){
        // chose random successor to simulate
        int chosePath = theRNG.getInt32() % (TInst->getNumSuccessors());
        bb = TInst->getSuccessor(chosePath);
      } else {
        // no successor, the end
        break;
      }
      count--;
    }
  }
  std::set<BasicBlock*> newbbset;
  std::set_difference(bbset.begin(), bbset.end(), executor.bbset.begin(), executor.bbset.end(), std::inserter(newbbset, newbbset.begin()));

  int traversedCount = bbset.size();
  int newTraversedCount = newbbset.size();

  for (std::set<BasicBlock*>::iterator bi = newbbset.begin(); bi != newbbset.end(); bi++){
    newTraversedCount +=bbmap[*bi];
  }
  //*aa << "traversedCount " << traversedCount << '\n';
  //*aa << "newTraversedCount " << newTraversedCount << '\n';
  return newTraversedCount;
}

namespace klee {
MCTSTree::MCTSTree () {
	this->root = new MCTSNode(NULL, 0, NULL, "Root");
	this->current = this->root;
	this->root->type = "Visited";
}

void MCTSTree::__bfs (MCTSNode* tnode, int depth) {
        //this __bfs is use as count all live node
	if (tnode == NULL or tnode->child.empty())
		return;
	for (MCTSNode::MCTSNodeVector::iterator it = tnode->child.begin() ; it != tnode->child.end(); ++it)
		this->count_node(*it, depth+1);
	for (MCTSNode::MCTSNodeVector::iterator it = tnode->child.begin() ; it != tnode->child.end(); ++it)
		this->__bfs(*it, depth+1);
}

void MCTSTree::__bfs (MCTSNode* tnode, ExecutionState* state) {
	//this __bfs is use as delete specified node
	if (tnode == NULL || tnode->child.empty())
		return;
	for (MCTSNode::MCTSNodeVector::iterator it = tnode->child.begin() ; it != tnode->child.end(); ++it)
		if (this->delet_node(*it, state))
			return;
	for (MCTSNode::MCTSNodeVector::iterator it = tnode->child.begin() ; it != tnode->child.end(); ++it)
		this->__bfs(*it, state);
}

MCTSNode* MCTSTree::select_node() {
	//從MCTSTree中挑選最好的Node (TreePolicy)
	MCTSNode* node = this->root;
	while (!node->is_terminated()) {
		if (node->is_expandable()) {
			this->current = node;
			return node;
		} else {
			node = node->best_child(1/sqrt(2));
			// print "Pick: %s" % node.data
		}
	}
	return NULL;
}

void MCTSTree::add_child(ExecutionState* state, std::string data, double coverage) {
	//加入child到current selected node中
	if (this->current != NULL)
		this->current->child.push_back(new MCTSNode(this->current, coverage, state, data));
}

void MCTSTree::refresh_tree(MCTSNode* tnode) {
	//更新current node的狀態
	while (tnode != NULL) {
		tnode->refresh_coverage();
		tnode = tnode->parent;
	}
}

void MCTSTree::count_node(MCTSNode* tnode, int depth) {
	if (tnode->is_expandable())
		this->live_count += 1;
}

int MCTSTree::count_living_node() {
	this->live_count = 0;
	this->__bfs(this->root,0);
	return this->live_count;
}

bool MCTSTree::delet_node(MCTSNode* tnode, ExecutionState* state) {
	if (tnode->is_expandable() && tnode->state == state) {
		this->current = tnode;
		tnode->clean_node();
		return true;
        }
	return false;
}

void MCTSTree::delet_dead_node(ExecutionState* state) {
        this->__bfs(this->root, state);
}

MCTSNode::MCTSNode (MCTSNode* parent, int coverage, ExecutionState* state, std::string data) {
	this->parent = parent;
	this->coverage = coverage;

	this->state = state;
	this->data = data;
	this->type = "Expandable";
	this->visit = 0;
}

bool MCTSNode::is_expandable () {
	return this->type == "Expandable";
}

bool MCTSNode::is_terminated () {
	//this node and its child is all been traverse
	// and denote this by its child
	return this->type == "Terminated";
}

void MCTSNode::refresh_coverage () {
	//calculate average coverage from children
	this->visit++;
	if (this->child.size() != 0) {
		double _sum =0;
		bool somebody_alive = false;
		for (MCTSNodeVector::iterator it = this->child.begin() ; it != child.end(); ++it) {
			MCTSNode* child = *it;
			_sum += child->coverage;
			if (!child->is_terminated())
				somebody_alive = true;
		}
		this->coverage = _sum / (double)(this->child.size());
		this->type = somebody_alive ? "Visited" : "Terminated";
	} else {
		this->coverage =0;
		this->type = "Terminated";
	}
}

MCTSNode* MCTSNode::best_child (float c) {
	double max_child_val = -1;
	MCTSNode* max_child = NULL;
	double max_coverage = 1;
	for (MCTSNodeVector::iterator it = this->child.begin() ; it != child.end(); ++it) {
		MCTSNode* child = *it;
		if (max_coverage < child->coverage)
			max_coverage = (child->coverage);
	}
	for (MCTSNodeVector::iterator it = this->child.begin() ; it != child.end(); ++it) {
		MCTSNode* child = *it;
		if (child->is_terminated())
			continue;
		// float val = child->visit != 0 ? (child->coverage/float(max_coverage) + c * sqrt(2 * log10(child->visit) / float(child->visit))) : 999999;
		// I make some change here, because the origin equation will select first non-traverse child node when one of child node are never trsverse.
		// The origin way do MCTS in the most of tree, but do bfs at leaf node.
		float val = (child->visit != 0) ? (child->coverage/float(max_coverage) + c * sqrt(2 * log10(child->visit) / float(child->visit))) : (child->coverage/float(max_coverage) + 100);
		if (val > max_child_val){
			max_child_val = val;
			max_child = child;
		}
	}
	return max_child;
}
void MCTSNode::clean_node () {
	this->state = NULL;
	this->data = "";
	if (this->is_expandable())
		this->type = "Visited";
}

}
