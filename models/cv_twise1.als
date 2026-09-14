//Original model assertions.
pred test0 {
{some disj User0, Institution0: Source{
some disj User0: User{
some disj Institution0: Institution{
some disj Id0: Id{
some disj Work0, Work1, Work2: Work{
Source = User0 + Institution0
User = User0
(User <: profile) = User0->Work0 + User0->Work1 + User0->Work2
(User <: visible) = User0->Work0 + User0->Work1 + User0->Work2
Institution = Institution0
Id = Id0
Work = Work0 + Work1 + Work2
(Work <: ids) = Work0->Id0 + Work1->Id0 + Work2->Id0
(Work <: source) = Work0->User0 + Work1->User0 + Work2->User0
Inv1[]
Inv2[]
not (Inv3[])
not (Inv4[])
}
}
}
}
}
}}
run test0 for 3 expect 1

pred test1 {
{some disj User0, User1: Source{
some disj User0, User1: User{
some disj Id0: Id{
some disj Work0, Work1, Work2: Work{
Source = User0 + User1
User = User0 + User1
(User <: profile) = User0->Work1 + User0->Work2 + User1->Work0
(User <: visible) = User0->Work2 + User1->Work0 + User1->Work1
no Institution
Id = Id0
Work = Work0 + Work1 + Work2
(Work <: ids) = Work0->Id0 + Work1->Id0 + Work2->Id0
(Work <: source) = Work0->User0 + Work1->User1 + Work2->User0
not (Inv1[])
not (Inv2[])
Inv3[]
not (Inv4[])
}
}
}
}
}}
run test1 for 3 expect 1

pred test2 {
{some disj User0, Institution0: Source{
some disj User0: User{
some disj Institution0: Institution{
some disj Id0, Id1, Id2: Id{
some disj Work0, Work1, Work2: Work{
Source = User0 + Institution0
User = User0
(User <: profile) = User0->Work0 + User0->Work1 + User0->Work2
(User <: visible) = User0->Work0 + User0->Work1 + User0->Work2
Institution = Institution0
Id = Id0 + Id1 + Id2
Work = Work0 + Work1 + Work2
(Work <: ids) = Work0->Id2 + Work1->Id1 + Work2->Id0
(Work <: source) = Work0->User0 + Work1->User0 + Work2->Institution0
Inv1[]
Inv2[]
Inv3[]
Inv4[]
}
}
}
}
}
}}
run test2 for 3 expect 1

pred test3 {
{some disj Id0: Id{
no Source
no User
no (User <: profile)
no (User <: visible)
no Institution
Id = Id0
no Work
no (Work <: ids)
no (Work <: source)
Inv1[]
Inv2[]
Inv3[]
Inv4[]
}
}}
run test3 for 3 expect 1

pred test4 {
{some disj User0, Institution0: Source{
some disj User0: User{
some disj Institution0: Institution{
Source = User0 + Institution0
User = User0
no (User <: profile)
no (User <: visible)
Institution = Institution0
no Id
no Work
no (Work <: ids)
no (Work <: source)
Inv1[]
Inv2[]
Inv3[]
Inv4[]
}
}
}
}}
run test4 for 3 expect 1

