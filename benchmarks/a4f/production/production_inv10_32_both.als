sig Workstation {
	workers : set Worker,
	succ : set Workstation
}
one sig begin, end in Workstation {}

sig Worker {}
sig Human, Robot extends Worker {}

abstract sig Product {
	parts : set Product	
}

sig Material extends Product {}

sig Component extends Product {
	workstation : set Workstation
}

sig Dangerous in Product {}

// Specify the following properties
// You can check their correctness with the different commands and
// when specifying each property you can assume all the previous ones to be true

	// Every worker is either a human or a robot.
pred inv1 {
	Worker = Human + Robot	
}

	// Every workstation has exactly one worker assigned to it.
pred inv2 {
	workers in Workstation one -> some Worker
}

	// Every component is assembled in exactly one workstation.
pred inv3 {
	all c : Component | one c.workstation
}

	// Every component has at least one part, and no material has any parts.
pred inv4 {
	(all c : Component | some c.parts) and (all m : Material | no m.parts)	

}

	// In any workstation, it is not allowed to have both human and robot workers; each workstation may have only humans, only robots, or no workers.
pred inv5 {
	all c : Workstation | no (c.workers & Human) or no (c.workers & Robot)
}

	// No component is a part of itself, either directly or indirectly (no cycles in the parts hierarchy).
pred inv6 {
	no c : Component | c in c.^parts
}

	// If a component contains at least one dangerous part, then that component is also dangerous.
pred inv7 {
	all c : Component | some c.parts & Dangerous implies c in Dangerous
}

	// No dangerous component may be assembled at a workstation that has any human workers.
pred inv8 {
	all c : Component & Dangerous | no c.workstation.workers & Human
}

	// All workstations are arranged in a single linear sequence from begin to end: each workstation except end has exactly one successor, end has none, and all workstations are reachable from begin via successor steps.
pred inv9 {
	(all w : Workstation - end | one w.succ) and (no end.succ) and (Workstation in begin.*succ)
}

	// For any component, each of its parts must be assembled at a workstation that is a strict successor (downstream) of the component's own workstation.
pred inv10 {
  	all c: Component | all p: c.parts | c.workstation in p.workstation.^succ 
}
