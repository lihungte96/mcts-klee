//===-- MCTS.h ----------------------------------------------*- C++ -*-===//
#include <vector>
#include <string>

namespace klee {  
  class MCTSTree;
  class MCTSNode;
  class ExecutionState;
}

namespace klee {
	class MCTSTree {
		// store node in MCTS Tree
		public:
			MCTSNode* root;
			MCTSNode* current;
			int live_count;
			MCTSTree ();
			void __bfs (MCTSNode* tnode, int depth);
			void __bfs (MCTSNode* tnode, ExecutionState* state);
			MCTSNode* select_node();
			void add_child(ExecutionState* state, std::string data, double coverage);
			void refresh_tree(MCTSNode* tnode);
			void count_node(MCTSNode* tnode, int depth);
			int count_living_node();
			bool delet_node(MCTSNode* tnode, ExecutionState* state);
			void delet_dead_node(ExecutionState* state);
	};
	class MCTSNode {
		public:
			typedef std::vector<MCTSNode*> MCTSNodeVector;
			MCTSNode* parent;
			double coverage;
			ExecutionState* state;
			std::string data;
			std::vector<MCTSNode*> child;
			std::string type;
			int visit;
			MCTSNode (MCTSNode* parent, int coverage, ExecutionState* state, std::string data);
			bool is_expandable ();
			bool is_terminated ();
			void refresh_coverage ();
			MCTSNode* best_child (float c);
			void clean_node();
	};
}
