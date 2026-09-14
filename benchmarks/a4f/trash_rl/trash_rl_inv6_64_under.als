/**
 * Relational logic revision exercises based on a simple model of a 
 * file system trash can.
 * 
 * The model has 3 unary predicates (sets), File, Trash and
 * Protected, the latter two a sub-set of File. There is a binary 
 * predicate, link, a sub-set of File x File.
 *
 * Solve the following exercises using Alloy's relational logic, which
 * extends first-order logic with:
 *	- expression comparisons 'e1 in e2' and 'e1 = e2'
 *	- expression multiplicity tests 'some e', 'lone e', 'no e' and 'one e'
 *	- binary relational operators '.', '->', '&', '+', '-', ':>' and '<:' 
 *	- unary relational operators '~', '^' and '*'
 *	- definition of relations by comprehension
 **/

/* The set of files in the file system. */
sig File {
  	/* A file is potentially a link to other files. */
	link : set File
}
/* The set of files in the trash. */
sig Trash in File {}
/* The set of protected files. */
sig Protected in File {}

/* No file is in the trash; the trash is empty. */
pred inv1 {
	no Trash
}

/* Every file is in the trash; all files have been deleted. */
pred inv2 {
	File in Trash
}

/* At least one file is in the trash; some file is deleted. */
pred inv3 {
	some Trash
}

/* No file is both protected and in the trash; a protected file cannot be deleted. */
pred inv4 {
	no Trash & Protected
}

/* The set of all files equals the union of the trash and the protected files; every file is either deleted or protected, meaning all unprotected files are deleted.*/
pred inv5 {
	File = Trash + Protected
}


/* Every file links to at most one file. */
pred inv6 {
 all f:File | some f1,f2:File | f->f1 in link and f->f2 in link and f1!=f implies f1=f2 
}


/* No file that is the target of any link is in the trash; no file in the trash is linked to. */
pred inv7 {
	no File.link & Trash
}


/* There are no links at all; no file links to any file.*/
pred inv8 {
	no link
}


/* No file that is the target of some link itself has any outgoing links; there is no twoâ±step chain of links.*/
pred inv9 {
	no link.link
}


/* If a file is in the trash, then every file it links to is also in the trash. */
pred inv10 {
	all f : File | f in Trash implies f.link in Trash
}

