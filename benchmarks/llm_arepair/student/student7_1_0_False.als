sig List {
    header: set Node
}

sig Node {
    link: set Node,
    elem: one Int
}

fact CardinalityConstraints {
    all l: List | #l.header <= 1
    all n: Node | #n.link <= 1
    all n: Node | #n.elem = 1
}

pred Loop(This: List) {
    all n: Node | n in This.header.link.^(link)
    #This.header > 0
}

pred Sorted(This: List) {
    all n: Node | all m: n.link | n.elem <= m.elem
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

pred Count(This: List, x: Int, result: Int) {
    RepOk[This]
    result = #(x.~(elem) & This.header.*link)
}

abstract sig Boolean {}
one sig True, False extends Boolean {}

pred Contains(This: List, x: Int, result: Boolean) {
    RepOk[This]
    some (x.~(elem) & This.header.*link) => result = True else result = False
}

fact IGNORE {
    one List
    List.header.*link = Node
}