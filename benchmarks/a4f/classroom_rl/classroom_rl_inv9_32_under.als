/**
 * Relational logic revision exercises based on a simple model of a 
 * classroom management system.
 * 
 * The model has 5 unary predicates (sets), Person, Student, Teacher,
 * Group and Class, Student and Teacher a sub-set of Person. There are 
 * two binary predicates, Tutors a sub-set of Person x Person, and 
 * Teaches a sub-set of Person x Teaches. There is also a ternary 
 * predicate Groups, sub-set of Class x Person x Group.
 *
 * Solve the following exercises using Alloy's relational logic, which
 * extends first-order logic with:
 *	- expression comparisons 'e1 in e2' and 'e1 = e2'
 *	- expression multiplicity tests 'some e', 'lone e', 'no e' and 'one e'
 *	- binary relational operators '.', '->', '&', '+', '-', ':>' and '<:' 
 *	- unary relational operators '~', '^' and '*'
 *	- definition of relations by comprehension
 **/

/* The registered persons. */
sig Person  {
	/* Each person tutors a set of persons. */
	Tutors : set Person,
	/* Each person teaches a set of classes. */
	Teaches : set Class
}

/* The registered groups. */
sig Group {}

/* The registered classes. */
sig Class  {
	/* Each class has a set of persons assigned to a group. */
	Groups : Person -> Group
}

/* Some persons are teachers. */
sig Teacher in Person  {}

/* Some persons are students. */
sig Student in Person  {}

//Every person is a student
pred inv1 {
	Person in Student
}
//For every class and every student, that student belongs to at least one group in that class.
pred inv10 {
	all c:Class,s:Student | some s.(c.Groups)
}
//If a class has any group assignments (i.e., at least one person is assigned to a group in that class), then that class has at least one teacher.
pred inv11 {
	all c:Class | some c.Groups implies some Teacher&Teaches.c
}
//Every teacher teaches at least one class that has some group assignments.
pred inv12 {
	all x:Teacher | some x.Teaches.Groups
}
//Tutoring only happens from a teacher to a student; the tutor must be a teacher and the person being tutored must be a student.
pred inv13 {
	Tutors in Teacher -> Student
}
//For any class, if a person is assigned to a group in that class, then every teacher of that class tutors that person.
pred inv14 {
	all c:Class,s:Student | s in (c.Groups).Group implies (Teacher&Teaches.c) -> s in Tutors
}
//Every person is directly or indirectly tutored by some teacher (i.e., reachable via a chain of tutoring relationships from at least one teacher).
pred inv15 {
	all p:Person | some Teacher&(^Tutors).p
}
//There are no teachers at all.
pred inv2 {
	no Teacher
}
//No person is simultaneously a student and a teacher; the two groups are disjoint.
pred inv3 {
	no Student & Teacher
}
//Every person is either a student, a teacher, or both.
pred inv4 {
	Person in Student + Teacher
}
//At least one teacher teaches some class.
pred inv5 {
	some Teacher.Teaches
}
//Every teacher teaches at least one class.
pred inv6 {
	all t:Teacher | some t.Teaches
}
//Every class is taught by at least one teacher.
pred inv7 {
	all c:Class | some Teacher&Teaches.c
}
//No teacher teaches more than one class.
pred inv8 {
	all t:Teacher | lone t.Teaches
}
//No class is taught by more than one teacher.
pred inv9 {
 no (Class . Teaches) 
}
