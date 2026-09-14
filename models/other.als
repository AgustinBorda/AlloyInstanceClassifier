sig Person {
   member_of : some Group
}

pred CanEnter(p: Person, r:Room) {
	p.member_of in r.located_in
}

sig Group {}
one sig alas extends Group {}  
one sig peds extends Group {}

sig Room {
  located_in: set Group
}
one sig seclab extends Room {}

fact {
  // Should synthesize alas + peds = seclab.located_in
  alas + peds = seclab.located_in
}

// assertion
assert no_thief_in_seclab {
   all p : Person | CanEnter[p, seclab] implies alas in p.member_of or peds in p.member_of
}
check no_thief_in_seclab
