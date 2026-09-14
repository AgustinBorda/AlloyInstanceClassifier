sig List {
    header : set Node
}

sig Node {
    link: set Node,
    elem: one Int
}

// Correct
fact CardinalityConstraints {
    all l: List | lone l.header
    all n: Node | lone n.link
    all n: Node | one n.elem
}

// Underconstraint.  Should disallow header = l1 -> n1, no link
pred Loop(This: List) {
    no This.header.link && all n: This.header.*link | n.link = n
}

// Overconstraint.  Should allow no n.link
pred Sorted(This: List) {
    all n: This.header.*link | all m: n.link | n.elem <= m.elem
}

assert repair_assert_1 {
    all l: List | Sorted[l] <=> { all n: l.header.*link | all m: n.link | n.elem <= m.elem }
}


pred repair_pred_1 {
    all l: List | Sorted[l] <=> { all n: l.header.*link | all m: n.link | n.elem <= m.elem }
}


pred RepOk(This: List) {
    Loop[This]
    Sorted[This]
}

// Underconstraint.  Should be && instead of ||
pred Count(This: List, x: Int, result: Int) {
    RepOk[This]
    result = #{n: Node | n in This.header.*link && n.elem = x}
}

abstract sig Boolean {}
one sig True, False extends Boolean {}

// Correct
pred Contains(This: List, x: Int, result: Boolean) {
    RepOk[This]
    {some n: This.header.*link | n.elem = x} => result = True else result = False
}

fact IGNORE {
    one List
    List.header.*link = Node
}