sig User {
	follows : set User,
	sees : set Photo,
	posts : set Photo,
	suggested : set User
}

sig Influencer extends User {}

sig Photo {
	date : one Day
}
sig Ad extends Photo {}

sig Day {}

// Specify the following properties
// You can check their correctness with the different commands and
// when specifying each property you can assume all the previous ones to be true

	// Every photo is posted by exactly one user.
pred inv1 {
	all p : Photo | one posts.p
}

	// No user follows themselves.
pred inv2 {
	all p : User | p not in p.follows
}

	// An user only sees (non ad) photos posted by followed users. 
	// Ads can be seen by everyone.
pred inv3 {
	all p : User | p.sees - Ad in p.follows.posts
}

	// If a user has posted at least one ad, then every photo they post is an ad. 
pred inv4 {
		all u : posts.Ad | u.posts in Ad
}

	// Every influencer is followed by all other users (every user except the influencer themselves).
pred inv5 {
	all i : Influencer | follows.i = User - i
}

	// Every influencer posts at least one photo on every day.
pred inv6 {
	all i : Influencer, d : Day | some i.posts & date.d
}

	// For each user, the suggested users are exactly those users who are followed by at least one user the original user follows, excluding the original user themselves and anyone they already follow directly.
pred inv7 {
	all u : User | u.suggested = u.follows.follows - u.follows - u
}

	// For any user, any ad they see must be posted by either a user they follow or a user from their suggested set.
pred inv8 {
  all x:User, t:User-x, a:Ad| x->a in sees and t->a in posts implies x->t in follows or x->t in suggested 
}
