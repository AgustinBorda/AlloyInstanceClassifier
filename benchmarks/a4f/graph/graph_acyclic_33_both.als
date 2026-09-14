/* 
Each node has a set of outgoing neighbours. The graph is simple: there is
at most one directed edge between any given ordered pair of nodes.
*/
sig Node {
	adj : set Node
}

/*
The graph is undirected: whenever there is an edge from one node to another,
the reverse edge also exists.
*/
pred undirected {
	adj = ~adj
}

/*
The graph is weakly connected: if we ignore the direction of edges, every node
can reach every other node by following some path.
*/
pred weaklyConnected {
	all n:Node | Node = n.*(adj+~adj)
}

/*
The graph is acyclic: no node can be reached from itself by following one or
more directed edges (i.e., there are no directed cycles).
*/
pred acyclic {
 iden not in (*adj - adj) 
}

/*
The graph is complete: every possible ordered pair of nodes (including a node
paired with itself) is directly connected by a directed edge.
*/
pred complete {
	adj = Node -> Node
}

/*
The graph has no loops: no node has a directed edge pointing to itself.
*/
pred noLoops {
	no adj & iden
}

/*
The graph is oriented: for any two distinct nodes, there is at most one 
directed edge between them (i.e., no pair of nodes has edges in both 
directions). This also implies that there are no self-loops, since a 
self-loop would be its own reverse and would violate the condition.
*/
pred oriented {
	no adj & ~adj
}

/*
The graph is strongly connected: by following the direction of edges, every node
can reach every other node (including itself) through some directed path.
*/
pred stronglyConnected {
	all n:Node | Node = n.*adj
}

/*
The graph is transitive: whenever a node can reach another through one or more
intermediate nodes, there is also a direct edge from the first to the last.
*/
pred transitive {
	adj = ^adj
}
