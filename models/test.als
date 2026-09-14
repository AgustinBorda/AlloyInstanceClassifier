open util/ordering[A] as ord
sig A {
}

lone sig B extends A {
rel: A
} //Atoms should be of type B

one sig C extends A{} //Atoms should be of type C



