sig List  {
header: set Node
}

sig Node {
link: set Node,
elem: set Int
}

// Correct
fact CardinalityConstraints {
all l: List | lone l.header
all n: Node | lone n.link
all n: Node | one n.elem
}

// Correct
pred Loop(This: List) {
no This.header || one n: This.header.*link | n in n.link
}

// Correct
pred Sorted(This: List) {
all n: This.header.*link | some n.link => n.elem <= n.link.elem
}

pred RepOk(This: List) {
Loop[This]
Sorted[This]
}

// Correct
pred Count(This: List, x: Int, result: Int) {
RepOk[This]
#{n: This.header.*link | n.elem = x} = result
}

abstract sig Boolean {}
one sig True, False extends Boolean {}

// Fixed Contains predicate to ensure result is False when the list does not contain x.
pred Contains(This: List, x: Int, result: Boolean) {
RepOk[This]
(result = True and some n: This.header.*link | n.elem = x) or (result = False and no n: This.header.*link | n.elem = x)
}

fact { some Node }

assert repair_assert_1{
all l:List | all x:Int | all res:Boolean |
Contains[l, x, res] <=>
{
RepOk[l]
{some n: l.header.*link | n.elem = x } <=> True = res
}
}


pred repair_pred_1{
all l:List | all x:Int | all res:Boolean |
Contains[l, x, res] <=>
{
RepOk[l]
{some n: l.header.*link | n.elem = x } <=> True = res
}
}


fact IGNORE {
one List
List.header.*link = Node
}