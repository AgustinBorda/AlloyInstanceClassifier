//Original model assertions.
pred test0 {
{some disj Node0: Node{
Node = Node0
(Node <: adj) = Node0->Node0
undirected[]
weaklyConnected[]
not (acyclic[])
complete[]
not (noLoops[])
not (oriented[])
stronglyConnected[]
transitive[]
}
}}
run test0 for 3 expect 1

pred test1 {
{some disj Node0, Node1: Node{
Node = Node0 + Node1
(Node <: adj) = Node0->Node1 + Node1->Node1
not (undirected[])
weaklyConnected[]
not (acyclic[])
not (complete[])
not (noLoops[])
not (oriented[])
not (stronglyConnected[])
transitive[]
}
}}
run test1 for 3 expect 1

pred test2 {
{some disj Node0, Node1: Node{
Node = Node0 + Node1
(Node <: adj) = Node1->Node1
undirected[]
not (weaklyConnected[])
not (acyclic[])
not (complete[])
not (noLoops[])
not (oriented[])
not (stronglyConnected[])
transitive[]
}
}}
run test2 for 3 expect 1

pred test3 {
{some disj Node0, Node1: Node{
Node = Node0 + Node1
no (Node <: adj)
undirected[]
not (weaklyConnected[])
acyclic[]
not (complete[])
noLoops[]
oriented[]
not (stronglyConnected[])
transitive[]
}
}}
run test3 for 3 expect 1

pred test4 {
{some disj Node0, Node1, Node2: Node{
Node = Node0 + Node1 + Node2
(Node <: adj) = Node1->Node2 + Node2->Node1
undirected[]
not (weaklyConnected[])
not (acyclic[])
not (complete[])
noLoops[]
not (oriented[])
not (stronglyConnected[])
not (transitive[])
}
}}
run test4 for 3 expect 1

pred test5 {
{no Node
no (Node <: adj)
undirected[]
weaklyConnected[]
acyclic[]
complete[]
noLoops[]
oriented[]
stronglyConnected[]
transitive[]
}}
run test5 for 3 expect 1

pred test6 {
{some disj Node0, Node1, Node2: Node{
Node = Node0 + Node1 + Node2
(Node <: adj) = Node1->Node2 + Node2->Node0
not (undirected[])
weaklyConnected[]
acyclic[]
not (complete[])
noLoops[]
oriented[]
not (stronglyConnected[])
not (transitive[])
}
}}
run test6 for 3 expect 1

pred test7 {
{some disj Node0, Node1, Node2: Node{
Node = Node0 + Node1 + Node2
(Node <: adj) = Node0->Node2 + Node1->Node0 + Node2->Node1
not (undirected[])
weaklyConnected[]
not (acyclic[])
not (complete[])
noLoops[]
oriented[]
stronglyConnected[]
not (transitive[])
}
}}
run test7 for 3 expect 1

pred test8 {
{some disj Node0, Node1, Node2: Node{
Node = Node0 + Node1 + Node2
(Node <: adj) = Node0->Node1 + Node0->Node2 + Node1->Node0 + Node1->Node2 + Node2->Node0 + Node2->Node1 + Node2->Node2
undirected[]
weaklyConnected[]
not (acyclic[])
not (complete[])
not (noLoops[])
not (oriented[])
stronglyConnected[]
not (transitive[])
}
}}
run test8 for 3 expect 1

pred test9 {
{some disj Node0, Node1, Node2: Node{
Node = Node0 + Node1 + Node2
(Node <: adj) = Node2->Node1
not (undirected[])
not (weaklyConnected[])
acyclic[]
not (complete[])
noLoops[]
oriented[]
not (stronglyConnected[])
transitive[]
}
}}
run test9 for 3 expect 1

