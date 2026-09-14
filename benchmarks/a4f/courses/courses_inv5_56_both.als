open util/ordering[Grade]

sig Person {
	teaches : set Course,
	enrolled : set Course,
	projects : set Project
}

sig Professor,Student in Person {}

sig Course {
	projects : set Project,
	grades : Person -> Grade
}

sig Project {}

sig Grade {}

// Specify the following properties
// You can check their correctness with the different commands and
// when specifying each property you can assume all the previous ones to be true

	// Every person who is enrolled in a course must be a student.
pred inv1 {
	enrolled in Student -> Course
}

	// Every person who teaches a course must be a professor.
pred inv2 {
	teaches in Professor -> Course
}

	// Every course has at least one teacher.
pred inv3 {
	teaches in Person some -> Course
}

	// Every project is associated with exactly one course.
pred inv4 {
	all p : Project | one (Course <: projects).p
}

	// Every project has at least one person working on it, and all persons working on any project are students.
pred inv5 {
  	 	(all p: Person | some proj: Project | proj in p.projects implies p in Student) 	and 	Project in Student.projects 
}

	// For any person, the projects they work on must belong to some course they are enrolled in.
pred inv6 {
	all p : Person | p.projects in p.enrolled.projects
}

	// For any person and any course, that person works on at most one project belonging to that course.
pred inv7 {
	all p : Person, c : Course | lone p.projects & c.projects
}

	// No person can be both teaching and enrolled in the same course.
pred inv8 {
	(all p : Person | no p.teaches & p.enrolled)
}

	// For any person, none of their co‑teachers (other teachers who share a course with them) can be enrolled in a course that this person teaches.
pred inv9 {
	all p : Person | no (p.teaches.~teaches - p) & p.teaches.~enrolled
}

	// Only students can have a grade recorded.
pred inv10 {
	Course.grades.Grade in Student
}

	// In any course, every person who has a grade must also be enrolled in that course.
pred inv11 {
	all c : Course | c.grades.Grade in enrolled.c
}

	// For any person and any course, that person can have at most one grade in that course.
pred inv12 {
	all p : Person, c : Course | lone p.(c.grades)
}

	// If a person obtains the highest possible grade in a course, then that person must have worked on at least one project of that course.
pred inv13 {
	all c : Course, p : Person | last in p.(c.grades) implies some p.projects & c.projects
}

	// For any person, no other person can be a collaborator on two or more distinct projects with them; i.e., a person cannot work with the same colleague on more than one project.
pred inv14 {
	all p : Person, disj x,y : p.projects | no ((Person <: projects).x & projects.y) - p
}

	// For any course, any two distinct students who work on the same project of that course and both have a grade in the course must have grades that are either equal or consecutive in the grade ordering.
pred inv15 {
	all c : Course, p : c.projects, disj x,y : (Person <: projects).p | some c.grades[x] and some c.grades[y] implies c.grades[x] in c.grades[y].(prev+iden+next)
}
