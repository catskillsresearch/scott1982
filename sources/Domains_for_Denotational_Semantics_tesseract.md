---
source_pdf: Domains_for_Denotational_Semantics.pdf
title: "Domains for Denotational Semantics"
author: Dana Scott
year: 1982
citation_key: Sco82
alias: "Information systems presentation (ICALP 1982)"
bibliography: "Scott, D. Domains for Denotational Semantics. ICALP 1982, LNCS 140, pp. 577–613."
pages: 34
extraction_method: "ocr (all pages)"
verification_status: draft
verified_by: null
verified_date: null
---

# Domains for Denotational Semantics

**Author:** Dana Scott (1982)  
**Source file:** `Domains_for_Denotational_Semantics.pdf`  
**Also known as:** Information systems presentation (ICALP 1982)

> **Human verification required.** This file is a machine-generated *draft*.
> Compare each `<!-- page N -->` block to the PDF. Correct OCR errors, restore
> mathematical notation, and check off items below. When done, set
> `verification_status: verified` in the YAML front matter and record your name
> and date.

## Bibliography

Scott, D. Domains for Denotational Semantics. ICALP 1982, LNCS 140, pp. 577–613.

## Verification checklist

- [ ] p.3: DEFINITION 2.1. An information sysiem is a structure
- [ ] p.5: DEFINITION 2.2. For u,v € Con we write uf v to mean that u}-X forall X Ev. @
- [ ] p.5: PROPOSITION 2.3. For allu,v,w,u',v' € Con, we have:

---

## Transcription


<!-- page 1 (ocr) -->

DOMAINS FOR DENOTATIONAL SEMANTICS

by
Dana S. Scott
Department of Computer Science
Carnegie-Mellon University
Pittsburgh, Pennsylvania 15213

Abstract. The purpose of the theory of domains is to give models for spaces on which to define
computable functions. The kinds of spaces needed for denotational sematics involve not only spaces
of higher type (e.g. function spaces) but also spaces defined recursively (e.g. reflexive domains). Also
required are many special domain constructs (or functors) in order to create the desired structures.
There are several choices of a suitable category of domains, but the basic one which has the simplest
properties is the one sometimes called consistently complete algebraic cpo’s. This category of domains
is studied in this paper from a new, and it is to be hoped, simpler point of view incorporating
the approaches of many authors into a unified presentation. Briefly, the domains of elements are
represented set theoretically with the aid of structures called information systems. These systems are
very familiar from mathematical logic, and their use seems to accord well with intuition. Many things
that were done previously axiomatically can now be proved in a straightfoward way as theorems.
The present paper discusses many examples in an informal way that should serve as an introduction
to the subject.

1. Introduction. I would like to begin with some personal remarks. When I think of the
number of headaches I have caused people in Computer Science who have tried to figure out the
mathematical details of the Theory of Domains, I have to cringe. The difficulty in the presentation
of the subject is in justifying the level of abstraction used in comparison with the payoff: too often
the effort needed for understanding the abstractions does not seem worth the trouble—especially
if the notions are unfamiliar or excessively general.

For example, Category Theory, which is much used in discussions of the Theory of Domains,
seems far too abstract to many people. On the other hand, Automata Theory—which has often
benefited from some use of Category Theory—is quite abstract and, in many aspects perhaps,
quite useless, but the level of abstraction is fairly low and the reasons for the definitions are
usually evident. Thus, the subject has become by now a standard topic even for undergraduate
courses. 1 believe that Michael Rabin and I had much to do with influencing the subsequent
development of the theory by formulating some years ago some basic concepts (many previously
known) in a way that made sense to anyone who had been exposed to a little Abstract Algebra,
Logic and Set Theory. This expository part: of our paper did not require originality, but rather
a certain frame of mind and a certain style of writing to put the ideas and problems in sharp
relief. (The original paper is Rabin~Scott [1959]; see the excellent historical review of the subject
in Greibach [1981].)

Domain Theory has fared less well. I feel I made a mistake in 1969 in using Lattice Theory
as a mode of presentation—a mistake as far as Computer Science is concerned. Lattices are
very familiar to logicians and those interested in Universal Algebra, and I liked very much the
structures I found. But it takes some time to learn the special terminology and to become
comfortable with the necessary examples. Indeed, without a stock of examples, it is impossible
to have sufficient intuition for making the required constructions. True, some people took to
the approach, and the lattice-theoretic definitions were simple enough to motivate. But a much

<!-- page 2 (ocr) -->

578

greater percentage of people ] came in contact with found the large number of things to leary
a definite roadblock to understanding. And the Lattice Theory was only partly standard, since
this approach to the theory has to employ complete lattices and topological notions in order to
explain limits and continuity adequately. In fact, Topology of a rather mathematically simple
set-theoretical kind could have been used as the whole foundation much as in Scott [1972], but
that kind of mathematics seems even less attractive to computer scientists. Again, it is a matter
of background, I think, and it is unreasonable to expect people to know everything. Nevertheless,
the lattice-theoretic approach has great consistency and coherence; it has been carried out in ful]
detail in Gierz, et al. [1980], which also gives the topological connections. That book contains a
large number of references to the mathematical literature to show the connections of the theory to
many other topics. What we had to miss out there is a clear hook-up with computability theory,
owing simply to a lack of space and time to be able to cover everything.

In Scott [1981], I tried out another, different presentation (which is also explained in Scott
[1982].) However, I have found that the use of neighborhood systems causes confusion in people
not used to thinking in terms of sets of sets of sets of sets. . . , even though the set theory
required is quite simple. My purpose in the present Jecture, then, is to go back once more to the
very beginning to try out another plan for making the story easy and natural. The notion to be
used I call an information system. This is a “static” notion appropriate to bodies of information
about coherent groups of elements. The “dynamic” ideas enter in the ways different systems can
be related and in the semantical definitions about meanings of programming language constructs,
(For discussions of semantical definitions see Stoy [1977], Gordon [1979], and Tennent [1981].)
Neighborhood systems are, in a precise sense, equivalent to information systems, but there seems
to be an interesting trade-off between what properties of structures are aziomatized and what are
implicit in the form of the structure. Perhaps, despite their simplicity, neighborhoods leave too
much implicit, too much to be extracted by definition; information systems, on the other hand,
do seem to be more flexible in doing several of the important constructions. It all comes down to
just where one imposes the closure conditions on the structures. I have a feeling that I now have
found just about the right mix of axioms vs. definitions.

Another word about Category Theory: I actually feel that it is particularly significant and
important for the theory and for the whole area of semantics. But it must be approached with
great caution, for the sheer number of definitions and axioms can try the most patient reader.
It seems to me to be especially necessary in discussing applications of abstract mathematical
ideas to keep the motivation strongly in mind. This is often hard to do if the categories get
too thick, but of course it all depends on the writer. Category Theory is especially useful in
stating general properties of structures and in characterizing constructions uniquely; however,
there often is a problem actually justifying the ezistence of certain constructions, and a direct
approach can be quicker than quoting lots of theorems. But, man cannot live by construction
alone: theorems have to be proved in order to get the proper value out of the work. Domain Theory
must also be convenient for demonstrating the soundness of various proof rules for properties of
recursively defined objects and recursively defined domains, and I think that Category Theory
can be helpful here. A step in the right direction has been made in the LCF system (see Gordon-
Milner- Wadsworth [1979]), which, however, does not take advantage of general Category Theory;
but the whole area needs much more development in my opimion.

The main purpose of the Theory of Domains in Denotational Semantics, as I see it, is to
give a mathematical model of a system of types—-including function-space types—and to explain

<!-- page 3 (ocr) -->

579

a notion of computability with respect to these types. There are many possible theories of
types, but the construction of domains is meant to justify recursive definitzons at all types,
and—most essentially—to justify recursive definitions of types. Pursuing these goals has certain
consequences, as we shall see. The model presented here is only one approach, and some
comparisons with other methods will be made in Section 8. Again some help from Category
Theory would be welcome in comparing the different kinds of modelling.

One benefit of Domain Theory is that it is possible to make sense of types containing infinite
elements. The cost required seems to be that the domains therefore have to contain partial
elements as well as total elements. And this is where the lattice-theoretic definitions entered in
the earlier presentations: the partial ordering with relations like z CL y was used to express the
fact that the element x was “less defined” (7.e. more partial) than y but “contained in” y. The
relation [., however, must be subjected to many axioms to have a theory suitable to the desired
applications. Instead of such a big group of axioms, I wish to put forward here a construction
where the “skeleton” (or better: “backbone”) of a domain is introduced by just a few axioms.
Then the domain itself is defined as a certain construct from the backbone in order to define the
appropriate notion of element. There are several advantages I can see to the new approach:

e Simple definitions of the basic concepts can be given.

Detailed properties are proved as theorems rather than assumed as axioms.

Emphasis can be given to the constructive nature of the definitions.
e Domains can be made more wiszble.

e The theory of domains is made more available for applications, because it is easier
to produce the needed complex domains.

It is to be hoped that the reader can judge the validity of these claims from the perhaps too brief
exposition to follow.

2. Information systems. Intuitively, an information system is a set of “propositions” that can
be made about “possible elements” of the desired domain. We will assume that sufficiently many
propositions have been supplied to distinguish between distinct elements; as a consequence, an
element can be constructed abstractly as the set of all the propositions that are true of it. Partial
elements have “small” sets; while total elements have “large” sets (even: maximal). To make this
somewhat rough idea precise, we have to explain—by a suitable, but small choice of axioms—how
the collection of all propositions relevant to the domain hangs together, or better, is structured
as a set of abstract propositions. Fortunately, the axioms for this structure are very simple and
familiar, which is a great help in making up examples.

DEFINITION 2.1. An information sysiem is a structure
(D,A,Con, +),

where D is a set (the set of data objects or propositions), where A is a distinguished member of
D (the least informative member), where Con is a set of finite subsets of D (the consistent sets
of objects), and where | is a binary relation between members of Con and members of D (the

<!-- page 4 (ocr) -->

580

entailment relation for objects). Concerning Con, the following axioms must be satisfied for a}j
finite subsets u,v C D:

(i) u€ Con, whenever u C v € Con;
(ii) {X} € Con, whenever X € D; and
(iii) wl {X} € Con, whenever u+ X.
Concerning |~, the following axioms must be satisfied for all u,v € Con, and all X € D:
(iv) uk A;
(v) ul X, whenever X € u; and
(vi) if v/-Y for all Y €u and u}-X, then vf-X.

In words we may say of Con that, as a set of sets, (i) it is closed under subsets, (ii) it contains
all singletons, and (iii) adjunction of an entailed object to a consistent set preserves consistency,
Concerning |, which should be viewed as a “multiary” relation, we may say that (iv) A is
entailed by anything, (v) |- is reflexive, and (vi) |- is transitive. (The last two properties are
both expressed in a way appropriate to a multiary relation on members of DD.) &

The best advice is to think of the members of D as consisting of fintte data objects, some of
which are more informative than others. The word “finite” should be taken here in the sense of
“fully circumscribed” —as regards what is given in A these data objects can be comprehended in
“one step.” It is of course possible to introduce information systems where the data objects are
infinite sets, but relative to A they are finite as data objects.

The member that provides zero information is A. Data objects are intended to give infor-
mation about possible elements of the domain to be constructed, so if we were to use A alone,
we would be describing the the least defined element usually written as |.

Not just any combination of data objects will describe a possible element, however; hence,
the need for the notion of consistency. If u € Con is false, then the “propositions” in u cannot all
be applied to the same element at the same time. Finally we have to agree that, in general, the
propositions to be allowed are rarely mutually independent. It follows that an entailment relation
must be imposed to record the dependencies that do hold among the propositions. With these
informal understandings, the axioms chosen should all be self-evident.

A first example. Suppose we let D be the set of non-negative integers, where we think of an
integer n as an abbreviation of the proposition n < x. Here z is a yet-to-be-determined element,
about which one proposition gives only a little information. We can identify A with 0, and take
Con to be the set of all finite subsets of D. The entailment relation can be defined formally in
the way suggested by the intuitive reading of the data objects:

{no,--.,%—-1}/- m iff either m=0 or m < n; for some 1 < k.

(Remember to think of the same possible z on both sides of the }~.) That |~ is an entailment
relation in the sense of our axioms is clear. 4

<!-- page 5 (ocr) -->

581

A second erample. The first example is possibly misleading because all (finite) sets of data
objects were allowed to be consistent. The example can be modified in a natural way so this is not
so; of course, quite a different system will be obtained. The idea is to let D be the set of all pairs
(n, m) of integers with n < m, where such a pair stands now for the proposition n < x < m.
Clearly the two data objects (0,2) and (3,7) taken together are inconsistent. (Why?)

Oh, I see, I have left out A from D; we must therefore include the somewhat artificial pair
(0, oo) with the obvious interpretation. When I say “obvious interpretation” here I mean that
u € Con can be defined by saying that there must be an integer satisfying all the “propositions” in
u. Further, u}- X can be defined by saying that whenever an integer satisfies all the propositions
in u, then it must satisfy X. The notion of “satisfy” really should be obvious from the intuitive
reading given to the data objects, and the reader can verify easily that all the axioms hold for
this example of an information system. 48

A third example. Let A and B be two fixed sets, and let D as a set consist of the ordered
pairs (a,b), with a € A and b € B, plus the extra object A. Here the “information” contained in
(a,b) is that a is mapped to b by a yet-to-be-determined function. With this thought in mind, we
will know that a finite set of data objects is consistent just in case it is possible. that they can all
belong to the same function. Formally, we can assert:

{(a0, bo), .- +) (@e—1, 64 —1)} € Con iff for all 2,7 < k whenever a; = a,, then b; = b,.

It is something of a bother having to throw in A in this case, but all we have to say is that if u
is consistent under the above rule, then so also will uU {A}; and these are the only consistent
sets of data objects for this example. Perhaps it would make more sense to use {(a,b)} in place
of the simpler (a,b), and then we could set A = © more naturally. From this point of view we
can regard each data object as a (very small!) fragment of the graph of a function; the consistent
sets then point to larger fragments of graphs.

The definition of the entailment relation is the minimal one:
ul X iff either X =A or X Eu.

These examples show that sometimes the main part of the structure is in Con, sometimes it is in
}- , and sometimes it is in the interplay between the two notions. The object A is not in itself
very important, but it is sometimes useful to have an object there that can always be counted
upon to act in the same way in every system. J§

Already in formulating the axiom about the transitivity of } a relation between sets in Con
was suggested; we now make this official.

DEFINITION 2.2. For u,v € Con we write uf v to mean that u}-X forall X Ev. @
PROPOSITION 2.3. For allu,v,w,u',v' € Con, we have:

(i) Ot {4};

(ii) ul v implies uUv E Con;

(iii) why;

<!-- page 6 (ocr) -->

582

(iv) ub v anduv- w imply uf- w;
(v) ui Du,ub-v, andy D v' imply u' + v’; and
(vi) ub vandu} vw! implyub vu’.

Proof. Obvious. §

Remark. It is not worth formulating a formal result at this point, but it should be clear that
the properties in 2.3 could have been used as axioms. That is to say, we could have taken | as
a binary relation on the set Con, used 2.1 (i)-(ii) and 2.3 (i)-(vi) as axioms. (Actually, 2.3(ii) is
redundant.) The old-style entailment relation would then be definable by:

uke X iff ub {X}.

The previous axioms in 2.1 are then easily proved from the new ones. J

Some notation. As it is not always clear what structure is meant if we refer to a domain
simply by naming its underlying set of data objects, it will be better if we use a letter to refer to
an information system as a whole. We shall therefore write:

A= (Da, Aa, Cona, Ka),

and say that A is an information system—with its parts as indicated. For a more informal
discussion, the notation without subscripts can suffice, but there can be problems when several
different systems are involved. J

So much for the definition of what a system is as a mathematical structure. The next question
is: What is it good for? More precisely, if information systems are the backbones of domains,
then where are the elements? That is the topic of the next section.

3. The elements of a system. Let A be an information system, and suppose we already had a
concept of being an element of A. The data objects are meant to be propositions about elements,
so if X is in Da, and if z is an element, then we can be expected to know what it means to say
that X is true of x. Since all we are given is the set of data objects Da, we have to assume that
it contains enough objects to distinguish between distinct elements. (If there were not enough of
them, we would have to change the set D4.) Formally, we can write of two elements a and y:

x=y iff all X € Da, which are true of z are also true of y, and conversely.

If this principle is accepted, then the elements can be :dentzfied with the sets of propositions true
of them; formally we can assert:

z= {X € Da |X is true of x}.

There can be no confusion injected here in identifying elements that ought to be distinct, since
we are assuming that there are enough data objects in the system. If for some reason we felt we
ought to have more of them to distinguish between more elements, then we would have to pass to
a larger and different information system. By agreement, then, the above equation is a tautology.

<!-- page 7 (ocr) -->

583

So, for the sake of simplicity, elements can be taken to be sets of data objects. But, we
hasten to ask, which sets? The question is really: What are the properties of truth? The answers
are well known, and, in fact, we have already used them in our examples in the last section. In
words, the set of true propositions about a possible element must be (i) consistent in itself, and
(ii) closed under entailment (or deductively closed, for short). Condition (i) is clear because we
are talking about a possible element, not an impossible one. Condition (ii) is acceptable, because,
by the very meaning of the word, entailment should be truth preserving. In addition, we are also
saying the converse: any set having properties (i) and (ii) corresponds to a (partial) element. Here
is the formal statement:

DEFINITION 3.1. The elements of the information system A = (Da, Aa, Con,, ka) are those
subsets x of Ds where:

(i) all finite subsets of z are in Con; and
(ii) whenever u C x and u}~ aX, then X Ea.

We write z € \A| to mean z is an element of the system. This set of elements is the domain
determined by the given system, An element that is not included in any strictly larger element
in the domain is called a total element; the set of total elements is denoted by Tota. 4

Remarks. Any subset of Da satisfying 3.1 (i) can be called consistent, and every consistent set
generates an element by closing it under entailment. Note, too, that every element contains A,
as a member, because the least informative proposition is true of all elements. Moreover, every
domain has a Jeast element contained in all other elements. We call it |, and write formally:

La = {X € Da | {Aa}b aX}.

In the above we could just as well have used the empty set @ in place of {A,}; and often we can
write simply |~- 4X.

The element |, is often called the bottom element of the domain. There need be no top
or maximal element, Ta. Such an element is possible if, and only if, all finite subsets of Da are
consistent, in which case, as a set, Ta = Da. The possibility is not excluded—rather, it is not,
required. In case T, exists, it is the unique total element of the domain, and conversely. 4g

Returning to our question of the balance between axiomatizaton and construction, what
we have done is first to axiomatize the properties of (D4, A,,Cona,/-a), then to construct
the domain |A| from this structure. The principal claimed advantages are that the axioms for
consistency and entailment are already essentially familiar, and that the definition of elementhood
is direct and natural from our understanding of the properties of truth.

The examples. Let us look again at the three examples of information systems of the last
section. (1) In the first we see that the elements, by the formal definition, are cither the finite sets
{n | n < m} or the whole set: (z.e. T). Intuitively, this corresponds to the fact that the chosen
propositions only give lower bounds on a possible element; thus, no element is “finished” until it
becomes infinite. (2) In the second example there is no top, and the elements are the sets of the
form:

{(n,g)Ingm<p<g},

<!-- page 8 (ocr) -->

584

where m <p are given, and where g = oo is allowed. The total elements here correspond to the
(non-negative) integers, and the partial elements to situations where the lower and upper bounds
have not come exactly together. (3) In the third example, the elements are Just the graphs (i.e,
sets of ordered pairs) of partial functions from A into B (with the object A adjoined to the graph),
Total elements correspond to total functions (7.e. functions well defined on allof the set A). 4

The reader should be able to obtain some more examples of information systems from his
own experience and should then consider what the corresponding domain is like. Examples are
really quite easy to make up. Needless to say, Mathematical Logic provides a host of information
systems, but logicians do not often consider the domains determined by the the systems they know
to be worthy of study in themselves. In particular, it does not seem to be widely recognized that
the domains obtained from information systems form a rich category, as we shall show later. The
word “category” is definitely being used here in the precise technical sense of Category Theory,
and the application of the notion is very appropriate since the category of domains has very good
closure properties.

4. Domains as lattices and as topological spaces. _I will attempt to keep this section as informal
as possible—especially as Sections 2 and 3 were quite formal (7.e. mathematical) enough. The
main purpose of the discussion of this section is to relate the new presentation of the Theory of
Domains to previously published ones. (Some alternatives are discussed at the end of the paper.)

Lattice-theoretic considerations. Let A be an information system. Because the elements of
|A| are introduced as sets, these elements can be given structure from what we know already
about ordinary sets. For instance, the set-theoretic inclusion relation between sets can certainly
be applied to elements. The question is: What does z C y mean intuitively? In fact, we have
already mentioned this relationship before. It means that every proposition (among the ones given
by the information system) true of z is also true of y (though not necessarily conversely). In other
words, x is perhaps only partially determined, while y is more fully determined in a way that
includes everything true of z. Clearly, then, if we grant the interest of partial elements, then this
relation is a natural and basic one. We often read “xz C y” as “x approximates y”.

Now here is one of the main points of the new exposition: Because z C y is defined in
terms of a familiar mathematical notion, then as a relation between elements it inherits all the
well-known properties of the set-theoretical relation. It should not be necessary to write them
out, for everyone who can read this far knows that C is in particular reflexive and transitive.
We say that the domain |A| is a partially ordered set under inclusion. We note that this (trivial)
result is proved from the definition rather than assumed as an axiom.

Let us try out another notion. Elements are consistent, deductively closed sets of data
objects. Right? Every subset of a consistent set is consistent, but not every subset is closed under
entailment, in general. Right? But suppose that z and y are two elements. It can easily be seen
that their intersection xy is again consistent.and deductively closed (by a 2 nanosecond proof).
Therefore, the set of elements of a domain is closed under intersection. This means that, as a
partially ordered set, |A| is an inf semilatiice.

Well, the exact terminology is quite unimportant, but the properties of when combined
with the properties of C are pleasantly “algebraic” (and run to several] lines when written out).
We all know them: / is idempotent, commutative, and associative. The element |, being the

<!-- page 9 (ocr) -->

585

smallest element of the domain, is a zero element for ]. The operation ( is monotonic with
respect to C, and we have the connection:

zCy if cNy=z.

What has just been alluded to in words is the standard mathematical axiomatization of the
properties of an infimum (or meet) operation in a partially ordered set. (Remember, however,
to have an operation well defined within a set it is necessary also to have closure under that,
operation.)

What about infs of subsets? No problem. For any non-empty subfamily of [A], it is just as
easy to prove that the set-theoretical intersection of all the elements in the subfamily is again
an element of the domain. This makes |A| a (conditionally) complete inf semilattice. Even if
you do not have any idea what I am talking about, it does not matter because the properties of
the domain are built in by the very definition; you do not have to worry at the start about their
formulation, for you can prove them when you need them (if ever).

What about suprema (or sups or joins)? Here there is a slight problem, because in the way
we set things up they do not always have to exist. Consider what happens with just two elements
zg and y. The set-theoretical union of the two elements as subsets of Da need be neither consistent
nor deductively closed; and even if zUy is consistent, it need not be closed under entailment. So
if we want sups within |A|, we cannot get by as cheaply as we can with a domain of arbitrary sets
for which the simple union is the answer.

Let us write the sup (supposing it exists in [|A|) as tL] y. What do we have when we actually
have it? By the lore of partially ordered sets, x] y must be the least element in |A| which includes
(in the sense of C) both z and y. Now we have just spoken about infs of families of elements:
they exist if the family is non empty. This indicates that x | y exists exactly when there is at
least one element z in |A| such that z C z andy C z. This turns out to be a way to say—entirely
inside |A|-—that zU y is consistent. In other words (and more generally) a sup of a subfamily
exists if, and only if, the union of the family is consistent. (And in that case the sup is just
the deductive closure of the union—that is, it is generally larger than the simple set-theoretical
union.) This has an axiomatic version, but it is slightly complicated by the fact that sups do not
always exist. In case Ta exists, then we always have all the sups, and |A| is a complete lattice.
(This is discussed in full axiomatic splendor in Gierz, et al. [1980].) But, let it hasten to be added,
not every complete lattice is isomorphic to a domain. The lattices that correspond to domains
are the so-called algebrazc lattices. (See the discussion loc. cit. for the additional axiomatics
required.) When the top is missing, the partially ordered structures corresponding to domains are
called conditionally complete, algebraic cpo’s.

There is, however, an important case in |A| where the union is consistent and is, in fact, the
sup in the domain. Suppose we have a sequence of elements such that

ty Cty Cp C+ Can C tga Co

As n increases, we can say that the elements z, are getting “better and better”; thus, they must
be approaching something even more desirable in the limit. Let

oo
y= U Zn;

n=0

<!-- page 10 (ocr) -->

586

then there is no question that y is a subset of Da. But is it an element? Consistency, recall,
means that every finite subset is in Con,. The trick is that a finite subset of y must be a subset
of one of the z,,, because the sequence of elements z,, is increasing. But all the terms of our given
sequence are elements, and so, consistent; therefore, every finite subset of y is consistent.

The same argument also shows that the set y of data objects is closed under entailment,
because | q is defined as a relation between finite (consistent) sets and data objects. It follows
that since each z,, is a set closed under | 4, then so is y. In other words, y is indeed an element.
Otherwise said, the domain |A| is closed under the formation of unions of increasing chains of
elements, and the union is, of course, the sup in the sense of the partial ordering. Again we have
proved closure rather than assuming it, and the necessary properties of the sup follow from its
definition as a union.

This last argument can be generalized—as is well known to mathematicians—to the case
of directed families of elements. The word “directed,” or better “upward-directed,” means that
every finite number of elements in the family is included in some further element of the family;
chains always have this property. A good example of the use of directed sets of elements figures
in the discussion of the finite elements of the domain.

As we have remarked several times, any consistent set of data objects generates an element
by closing it up under the entailment relation; thus, in particular, any set u € Con generates ap
element. Let us write

u={X € Dal uk aX}

for the closure of u under entailment. (This notation could be used for any consistent subset of D,
but the case of finitely generated elements is especially important.) Such a @ is always an element
of |A|; the totality of such elements form, by definition, the finite elements of the domain. The
notation @ should of course be decorated with a subscript A, but, as there is no good place to
write it in, we leave it out.

We have for all elements z of the domain the basic formula:
x = J{a | u € Con, and u C z}.

This can be read intuitively as saying that every element of the domain 1s the limit of tts finite
approzimations. And, having used the word “limit” so often, we ought now to say something
about how to make the meaning of this word correct mathematically. Note that in the limit
representation for z, the union is a directed one. (Why?)

Topological considerations. Geometrically speaking, a topological space is a collection of
“points” which group themselves in various “neighborhoods” providing thereby a sense of “near-
ness.” More specifically, a neighborhood of a point in a metric space consists of all those points
within a certain positive “distance” from the given point; that is, nearness is limited, but it is not
pushed to zero. The major reason for leaving some “breathing space” around the point comes
out in defining continuity of functions.

A function f from one topological space to another is said to be continuous provided that, for
every point x of the first space, and for every neighborhood in the second space around f(z), it is

<!-- page 11 (ocr) -->

587

possible to find—in the first space—a neighborhood around z with the following property. If the
function is restricted to this neighborhood, then its values lie entirely in the given neighborhood
around f(z). In the metric case we can say that if we do not want the function to wander any
great distance from f(x), then there is a restricted distance around z giving a neighborhood over
which the function values stay as close to f(z) as specified. This keeps the function from jumping
around wildly, since small variations in z lead to only small variations in f(z).

The intuition about continuity is no doubt very clear in the more geometric examples, and
gometric intuition can carry us quite far. But the spaces obtained from domain theory are not
really geometric spaces, so we need to make some shifts in our metaphors. The geometric notion
of a point usually implies that two points are perfectly distinguishable: if z and y are different,
then they have disjoint neighborhoods. This is certainly true in the metric case, where, if two
points are different, then they are at a positive distance apart. Early on in the study of topological
spaces, however, it was found that not all spaces were metric, and weaker separation properties
of pairs of distinct points were uncovered. One of the very weak versions of such a condition is
called the “To-axiom.” The best way to put it is that if two points have the same neighborhoods,
then they are the same. The contrapositive statement sounds odd: if two points are distinct, then
there is a neighborhood that contains one but not the other. The oddity of this statement lies in
the feeling that you cannot make up your mind over which is the better point.

In our domains there is already a notion of “betterness” which proves to be very closely
related to the implicit neighborhood structure. The reason why our domains, as spaces of points,
are not “geometric” in the familiar sense is that they contain partial elements. A geometric point
on the other hand is “perfect” or totally determined; it cannot be made better than it already
is. The metric in common spaces is measuring something other than betterness, for there are
competing notions of approximation afoot here. Thus, we must keep our special goals in defining
domains clearly in mind to avoid confusion.

Consider an information system A. For each u € Conga, we define a corresponding neighbor-
hood of |A| by the equation:

[ula = {x € JA] | u C oz}.

The neighborhoods of an element x are all those sets [u], where u C z. Note that this is the same
as saying U.C =z or U approximates x. Indeed, the neighborhoods are in a one-one correspondence
with the finite elements of |A|. A neighborhood collects together all those elements sharing the
same finite amount of information.

If both u C z and v C zg, then it is easy to see that the intersection of the two neighborhoods
is again a neighborhood of z by virtue of the formula:

[ula N [ula = [uU aa.

In case u and v are inconsistent with each other, then the intersection will be the empty set @.
Because every element of our domain |A| is the union of the finite elements it contains, it is trivial
to prove that two elements with exactly the same neighborhoods are the same. For these reasons,
then, it follows that |A] is a To-topological space. The immediate reaction to this intelligence is:
So what?

The answer to this scepticism will appear in the best light when we discuss in the next section
the notion of function or mapping appropriate to our domains. The argument will be based on the

<!-- page 12 (ocr) -->

588

extremely elementary form of the definition that characterizes the general continuous function
together with the fact that the geometric intuition is suggestive of theorems to prove. In Section
6. we will find that the space of all continuous functions between two given domains is also a
domain, a most useful result that is interesting topologically. But further interest for Domain
Theory comes from the circumstance that there is a connection between geometry and domains.
We cannot go into the full details here, but I can make some brief remarks.

Before continuing that discussion, though, it should be remarked that once the topology of
the domain has been uncovered, then the unions of chains of elements (or directed sets of elements)
are topological limits according to accepted general definitions. Thus, what we felt intuitively
was a limiting process (the getting better and better up to the union) is in fact a limit formation
in a precise mathematical sense. This helps convince us that we are on the right track.

Total elements as a space. In any domain it can be proved that any element z can be extended
to a total element t, which is characterized by the property that it is a mazimal element of the
partial ordering. (Perhaps there are many such t, but there is always at least one with x C 1.)
Recall that the set of all total elements of |A| is denoted by Tota. Because the set Tota C |Al,
it is a topological space itself. Suppose s and f¢ are two distinct total elements, then they must
be inconsistent with each other—but we shall prove more. If every finite consistent u C ¢ also
satisfied u C t, then s C ¢ would follow. But this is impossible, because s is maximal. Let, then,
u € Con with u C s be chosen so that u C ¢ fails. Now u must be inconsistent with ¢, since
otherwise there would be an element containing them both. It follows that u must be inconsistent
with some v € Con, with v C ¢. In this way we show that the neighborhoods [u], and [v], are
disjoint.

This argument proves that Tot, is a Hausdorff space (or To—-space). We cannot go further into
the details here, but it is also a totally disconnected, compact Hausdorff space. (These spaces—
well known from studies of Logic and the Theory of Boolean Algebras—are also zero-dimensional.)
Assuming the countability of Con,, which is not such a bold assumption, all such spaces can be
conveniently embedded into the real line so as to preserve the topological structure. Perhaps this
does not seem so surprising, but it shows that the topological nature of Tota, the uppermost
level of the To space |A|, is indeed quite geometric. And it can also be shown that any arbitrary
continuous function on Tot, into any topological space can be extended to a continuous function
on |A|, so the whole domain proves to be quite a “roomy” space with many good connections to
more usual topological spaces.

A note on neighborhood structures. Topological spaces can be defined in several ways, and in
general they do not carry a preferred neighborhood structure. (For example,there is no topological
significance to the the usual rational intervals we use to define neighborhoods for the real line: any
similarly dense set of points would do in place of the rational numbers.) Domains, the way we have
defined them, however, do have preferred neighborhoods. The set of finite elements of |A| can
be defined topologically, and as we have seen they determine a convenient set of neighborhoods.
(The reason for all this is the so-called zero-dimensonal character of the domains. There is a
higher-dimensional theory, but this leads to continuous lattices and can only be explained using
the kind of presentation in Gierz, et al.[1980]. It is too long-winded a story for the present paper.
The higher-dimensonal domains do not have a preferred set of neighborhoods, however.)

Having realized this, it is a short step to giving an algebraic axiomatization of the neigh-
borhood structure. Smyth [1975] contains a presentation in terms of the equivalent notion of

<!-- page 13 (ocr) -->

589

finite element. Scott [1981] turns the story around and defines a set-theoretical representation
of a neighborhood as just a family of sets containing a largest “neighborhood” and closed under
forming the intersection of any two sets in the family that contain a third. The set-theoretical
form of this definition is very simple, and Scott [1981] spells out the details of how the theory of
domains can be based on this starting point. Subsequent investigation, however, has convinced
the author that the present approach through information systems is even simpler and better for
a number of the essential constructions. The theory introduced by Ersov [1970] of F-spaces is
another axiomatization somewhat intermediate between the topological and the lattice theoretic.
Domains in the present sense then become complete F-spaces. There are many interesting aspects
to this method, but the author feels that information systems are about as elementary and familiar
as we can get, and they are therefore more suggestive of new constructions.

5. Approximable mappings between domains. Once a general notion of set or domain has
been defined mathematically, the next major issue is: How are the different domains to be related
one to another? The answer to this important question can many times be given by defining
an appropriate concept of mapping between domains. The answer need not be unique; the same
collection of domains may support more than one idea of function depending on the special aspects
of the domains that need to be brought out. In the case of the kinds of domains being studied
here, there are two principal answers, one of which is to be explained in this section.

In order to understand an appropriate notion of a mapping or a function between domains
constructed from information systems, we have to refer back to the way in which elements are
introduced. As we have seen in Section 3, an element is a consistent, closed set of data objects.
To generate an element, one has to generate more and more of the finite consistent subsets of the
element. Note that the separate data objects have to be grouped into these finite consistent sets,
because the entailment relation may require a finite set of arbitrary size on the left in making the
necessary entailments for closure. It is this kind of passage from a finite set to its closure that is
to be generalized in defining mappings.

Consider two domains. To map from one to another, some information about a possible
element of the first is presented as input to the function f. Then as output the function f starts
generating an element. If the input were u, a consistent set of the first domain, then part of
the output in the second domain might be a consistent set v. We could say that there is an
input/output relationship set up by f, and indicate by u f v that this relation holds going from u
in the first domain to v in the second. Of course to get the full effect of f, it is necessary to take
all the v’s related to a given u, because even a small finite amount of input may cause an infinite
amount of output. But every element of a domain is just the sum total of its finite subsets (finite
approximations), so it is sufficient to make the mapping relationship go between finite sets. Here
is the formal definition with the exact conditions that the relation f must satisfy.

DEFINITION 5.1. Let A and B be two given information systems. An approximable mapping
f: A— Bis a binary relation between the two sets Con, and Cong such that:

(i) OF;
(ii) uf and u fv’ always imply u f (v Uv’); and

(iii) ul Ka u,u fv, and vb, v! always imply u’ f v’,

<!-- page 14 (ocr) -->

590

We say that A is the source of f and Bis the target. 48

Intuitively the relationship u f v is an input/output passage which can be read informally as:
“f you are willing to give at least u amount of information about the argument, then the mapping f
is willing to give at least v amount of information about the value (and possibly even more—tf you
are pattent).” Condition (i) means that no (non-trivial) information about the input merits no
information about the output. Condition (ii) implies that all the contributions to the output from
a fixed input are consistent, and in fact the union of two of the output sets is again an output set.
Output corresponding to a fixed input is cumulative. Condition (iii) assures us that the mapping
relation f works in harmony with the two entailment relations: if a certain relationship holds,
and if the left-hand side is strengthened while the right-hand side is weakened, then the mapping
relation must continue to hold. What we must discuss next is what this means for elements.

Before defining the notion of function value, however, it is useful to remark that in the
definition of approximable mapping the form of the statement could be simplified by reducing
sets on the right to their elements. Specifically, we note the equivalence:

ufviffu f {Y} for all Y Ev.

In other words an approximable mapping is completely determined by the relation set up between
consistent sets on the left and single data objects on the right.

DEFINITION 5.2. If f : A — B is an approximable mapping between information systems, and
if z € |A| is an element of the first, then we define the image (or function value) of x under f by
the formula:

f(x) = {Y € Dp |u f {Y} for some u C zs}.
Alternatively, we could use the equivalent formula:

f(z) = Uf{e € Cong | uf vforsomeuCz}. &

Note that, under Definition 5.2, it has to be proved that the image of an element in [A| lies in
[B| in order to justify the use of the ordinary function-value notation. But both the consistency
and the closure under entailment of f(z) are direct consequences of the properties in the definition
of approximable mapping.

PROPOSITION 5.3. Let f,g : A — B be two approzimable mappings between two information
systems. Then

(i) f always maps elements to elements under Definition 5.2;
(ii) f=g wf f(x) = 9(2) for alle |Al; and
(ii) $ Co iff F(z) C ofa) for all ze Al,

Moreover, the approzimable mappings are monotone in the sense that
(iv) 2 Cy in |Al always implies f(x) C fly) mm |BI.

All these results foliow from the observation that

<!-- page 15 (ocr) -->

591

(v) ufo iff oC f@,
forallu€ Con, andallvu € Cong. 4

The proof is straightforward, and it completely justifies the use of the function-value notation.
Consequently, the question arises as to whether the characterization of approximable mappings
could not have been given in terms of elements in the first place. The answer is yes. Indeed,
approximable mappings correspond exactly to functions on elements preserving unions of chains
(this, in the case of countable information systems; directed unions must be used in general).
This characterization has also been called “continuity,” because it is equivalent to saying that
the mappings between elements are continuous mappings in the topological sense, when |A| and
|B| are regarded as topological spaces, as explained in the last section. The reason for the word
“approximable” is explained in Section 7.

Having justified the idea of an approximable mapping as a transformation on elements,
the next step is to combine mappings. It is hardly surprising to learn that compositions of
approximable mappings are approximable, which in mathematical terms means that the domains
together with the approximable mappings form a category. The interesting part starts when
we want to combine domains. But, to fix ideas, it is useful to spell out how compositions take
place on the level of the data objects and consistent sets. For instance, it was noted that in
any information system | — is transitive on Con, and in Definition 5.1 a transitivity condition
comes in. There is a perfectly good reason for the parallelism, for,.as we see next, the first idea
(entailment) is a special case of the second (approximable mapping).

PROPOSITION 5.4. Let A be an information system. Then the following formula defines an
approximable mapping I, : A— A:

(i) ul,av if uk ay,
for allu,v € Cony. And we have:

(ii) Ia(z) =a,
forallxE|Al. 4

In other words, the given entailment relation itself defines the identity function on the domain
in question; and of course, the identity function is an approximable mapping.

PROPOSITION 5.5. Let f: A — B andg: B ~— C be two approzimable mappings. Then the
following formula defines an approzimable mapping go f: AC:

(i) u(gof)w @fufv andvg w for some v € Cong,
for allu € Con, and w € Cong. And we have:

(i) (0 f(z) = of f(a),
foralizE|Al. 4g

In other words, composition of input/output relations is effected by putting the input into the
first, getting some output, and then putting that in as input to the second. The correctness of this

<!-- page 16 (ocr) -->

592

recipe on elements (7.e. formula 5.5(ii)) follows from the basic formula 5.3(v). Because the class of
allsets and arbitrary mappings forms a category-—in the formal meaning of the word—the above
three propositions show that the totality of information systems and approximable mappings also
forms a category: a sub-category of the category of sets. We have given a special representation to
the category by our use of data objects and consistent sets, and we have thereby put the elements
into a secondary position—-for a good reason. But the elements are there to use. The axioms
for a category could also be verified directly using the basic definitions like 5.4(i) and 5.5(i); the
details are bland. The more interesting topic is: what are the closure conditions on our domains;
how do we construct new domains given old ones?

Before we go on to the first basic constructs of sums and products of domains, we remark on
some other easy examples of approximable mappings: constant maps.

PROPOSITION 5.6. Given information systems A, B, C, andD, and given a fired element b € |B|,
then there is a unique approzimable mapping constb: A — B such that:

(i) (const b)(x) = 5,

for alla € |A|. Moreover, we have:
(ii) 7 o.(const b) = const f(d),

for all approzimable mappings f : B+ C; and
(iii) (const 6) o g = const b,

for all approtimable mappingsg: DA. 4

The proof is immediate, since we need only interpret the input/output relation u (const b) v
as:meaning v C b. We note that our notation is somewhat ambiguous since, for example, in
5.6(iii) we are using const} in two senses: once as a mapping from A, and once as a mapping
from D. In fact, we should hang two subscripts on the thing to fix both the source and the target
of the mapping. This is too painful, however, and we generally rely on context to make the
meaning clear. (Formal rules of type checking can be given, so on a computer-based system all
the necessary subscripts could be put back in. Thus, the kind of ambiguity we are dealing with
here is not very serious.)

6. Products and sums of domains. In the category of sets, the product (the cartesian product)
of two sets is by definition just the set of ordered pairs of elements. We could use the same
definition in the category of domains—-provided we worked in terms of the elements of the
domains. The disadvantage is that the determination of the product domain from data objects is
lost, or at least pushed into the background. We shall therefore give a construction of products
directly in terms of the given data objects, and then show how to prove that the product is just
the one expected when we look at the elements.

The idea for the definition is a simple one. Think of two domains A and B. A data object
X € Da can be giving information about a possible element z € |A|, and a data object Y € Dp
can be giving information about a possible element y € |B]. How do we wish to give information
about the pair (x,y)? The first piece of advice is not to say all that is known all at once. For

<!-- page 17 (ocr) -->

593

example, if pressed, we can say we know X about the first coordinate of the ‘pair; only later,
if really pressed, we can say we also know Y about the second coordinate. The point is that
data objects. provide only partial information, and it does not matter if it takes several of them
to give fairly complete information about the whole element. This attitude motivates, then, the
particular form of our official definition.

DEFINITION 6.1. Let A and B be two information systems. By A X B, the product system, we
understand the system where:

(i) Daxn = {(X, Ap) |X € Da} U {(Aa, Y) | Y € Da};

(ii) Aaxp = (Aa, Ap);

(iii) u€Conayxp iff fstu € Con,and snd u € Cong;

(iv’) wkaxp(X’,Ap) iff fstu}-4 X’; and

(iv) utaxs(Aa,Y’) iff sndub-p Ys

where, in (iii), u is any finite subset of Day g, in (iv’) and (iv’”’), u € Cong yxp, and we let:

fstu = {X € Dg | (X, Ap) € u}, and
sndu = {Y € Dg |(Aa, Y) Eu}. a

Note that in 6.1(i) the two sets in the union are just two copies of Da and Dg, respectively.
There is a shared member, however, the object (Aa, Ag), which is indeed the least informative
data object—whether it is looked at from the point of view of A or of B. We could have used
all the pairs (X,Y), but if we did, the consistent set {(X,Y)} would be deductively equivalent to
the set {(X, Ap), (Aa, Y)} according to the definition of }-,, and so there is not much point
in having this redundancy. Strictly speaking, we should not make these remarks until we have
actually verified that 6.1 is indeed a proper definition.

PROPOSITION 6.2. If A andB are information systems, then so is A X B, and we have mappings
fst: AX B-—A and snd: AXB-B,

such that, for approzimable mappings
f: CA and g:C—-B,

there ts one and only one approzimable mapping (f,g): C + A X B such that

fsto(f,g) =f and sndo(f,g)=g.

Proof. Checking that 6.1 does indeed define an information system is straightforward, but there
are six things that must be proved according to Definition 2.1. We have to leave the details to the
reader. Next using the notation of 6.1, where fst and snd were applied as operations on consistent
sets u € Cona xp, we redefine matters to have approximable mappings, where, for v € Con, and
w € Cong,

<!-- page 18 (ocr) -->

594

(1) ufstu iff fstub-, v;
(2) usndw iff sndul-p, w; and
(3) s{f,g)u iff sf (fstu) and sg (sndw).

Because we defined A X B so that consistency and entailment worked independently on the two
halves of the set of data objects, it is easy to check that (1)-(3) define approximable mappings
having the desired properties.

The uniqueness of (f,g) comes out of the observation that, if z and z’ are two elements of
A X B for which

fst(z) = fst(z’) and snd(z) = snd(z’),

then z = z'. The reason is that fst and snd just divide elements into the two kinds of data
objects, and then strip off the parentheses. (Look back at Definition 6.1.) No information is lost,
so if z and z’ are transformed into the same elements both times, then they have to be the same.

That lemma treats one pair of elements at a time, but (f,g) is a function. But if (f,g)/ were
another function satisfying the conditions of the above proposition, then the two functions would
be pointwise equal. We could then quote 5.3 to assure ourselves that they are the same function.
|

Ordered pairs. By using the definition

(x, y) = (const(z), const(y))(Lc),

which invokes 6.2 on any convenient fixed domain C, it is easy to prove that |A X BJ is in a
one-one correspondence with the set-theoretical product of |A| and |B]. Indeed, it can be shown
that for z € |A| and y € |BI,

(1) (zy) = {(%, As) | X € z}U (44, ¥) | ¥ Ey} € JA x BI;
(2) fst(x,y) = 2;
(3) snd(z,y) = y;
and, for all z € |A X BI,
(4) z= (fstz, snd z).
Also, using the notation of 6.2, we can say that
(5) (Ff, 9)(t) = (F@), 9(2),
for all ¢ € |C|.

There are also remarks that could be made about the pointwise nature of the partial ordering
of |A X BI, but we will not formulate them here. We do remark, however, that there is also a
trivial product of no terms, 1, called the unit type or domain. It is such that Dy = {Aj}, and

<!-- page 19 (ocr) -->

595

that equation determines it up to isomorphism. The domain 1 has but one element, namely 1).
Note also that all approximable mappings f : 1 + A are constant, which shows how Definition
5.1 is a generalization of Definition 3.1. Note finally that there is but one approximable mapping
f:A1, namely f =0=const(1i). 0

We turn now to the definition and properties of sums of domains.

DEFINITION 6.3. Let A and B be two information systems. By A-+ B, the separated sum system,
we understand the system where, after choosing some convenient object A belonging neither to
DP, nor to Dg, we have:

(i) Daze = {(¥, 4) |X € Da} UL(A,Y) | ¥ € Da} U {(A, A)};
(ii) Aa+B = (A, A);

(iii) u€Cona+p iff either lft € Con, and rhtu=@
or lft u == @ and rhtu € Cong;

(iv’) ut a+n (X’,A) iff Iftu 4 © and lftub-, X’;
(iv’) ut-a+n(A,Y’) iff rhtu 4 @ and rhtul-, Y’; and
(iv’””) u Lap (A, A) always holds.
where, in (iii), u is any finite subset of Dap, in (iv’)-{iv’”), u € Cona+p, and we let:
lft u = {X € Dy | (X,A) € u}, and
rhtu={Y € Dp |(A,Y)Eu}. op

The plan of the sum definition is very similar to that for product, except that (1) for reasons
to be made clear in examples, the parts do not share the least informative element (i.e. the data
objects (Aq, A), (A, Ag), and (A, A) are inequivalent in this system), and (2) instead of defining
consistency and entailment in a conjunctive way, these notions are defined disjunctively. The
effect of these changes over Definition 6.1 is to produce a system A -+ B whose elements divide
into disjoint copies of those of A and B (plus an extra element |a+p). These remarks can be
made more precise in the following way:

PROPOSITION 6.4. If A and B are information systems, then so is A -+-B, and we have approzim-
able mappings

ink: A+A-+B and inr: B>A-B,
such that, for approzimable mappings
f:A—-C and g:B-C,
there ts one and only one approzimable mapping [f,g]: A+ B— C, such that

[f,gloinl=f, [f,g]oinr=g,and [f,9\(La+n) = le.

<!-- page 20 (ocr) -->

596

Proof. The proof that 6.3 defines a system satisfying the basic axioms of 2.1 has to be left to the
reader. Next using the notation of 6.1, where lft and rht were applied as operations on consistent
sets u € Conan, we redefine matters to have approximable mappings, where, for v € Con, and
w € Cong,

(1) vinlu iff {(X,A) |X E v} /- A+B U;
(2) winru iff {((A,Y)|Y € w} t+ a+p u; and

(3) ulf,g]s iff either }-c s, or lftu + @ and litu f s,
or trhtu ~ @ and rhtwug s.

Because we defined A -+ B so that consistency and entailment worked on the two halves of the
set of data objects just as they worked on A and B, respectively, it is easy to check that (1)-(3)
define approximable mappings, and that the desired properties hold.

The uniqueness of [f,g] comes from the fact that the elements of A-+ B, apart from the
bottom element of the domain, are just the elements in the ranges of inl and inr. Since the
function [f,g] takes bottom to bottom (in the indicated domains), it will be uniquely determined
by what it does on the two halves of the sum. The last equations of the theorem just say that
the function ts completely determined on these elements. 4

It can also be shown that Propositions 6.2 and 6.4 uniquely characterize the domains A X B
and A+ B up to isomorphism, and they give'us the existence of additional mappings that are
needed to show that product and sum are functors on the category of domains. We can also show
from these results that the domain

BOOL = 1+1

has two elements true and false, such that any mapping on BOOL is uniquely determined by its
action on true, false and | gooL, and the values on the first two elements may be arbitrarily
chosen.

7. The function space as a domain. Functions or mappings between domains are of basic
importance for our theory, since it is through them that we most easily transform data and relate
the structures into which the elements defined by the data objects enter. There are many possible
functions, and large groups of them can be treated in a uniform manner. For instance, if the source
and target domains match properly, any pair of functions can be composed—composition is an
operation on functions of general significance. Now, if in the theory we could combine functions
into domains themselves, then an operation like composition might become a mapping of the
theory. Indeed, this is exactly what happens: suitably construed, composition is an approximable
mapping of two arguments. Of course, for each configuration of linked source and target domains,
there is a separate composition operation.

In order to make approximable mappings elements of a suitable domain, we have to discover
first what their appropriate data objects are. In Section 5 this was hinted at already. To
determine an approximable mapping f : A — B, we have to say which pairs (u,v) with u € Da
and uv € Dg stand in the mapping relation u f v. One such pair gives a certain (finite) amount
of information about the possible functions that contain it, and an approximable mapping is

<!-- page 21 (ocr) -->

597

completely determined by such pairs. Therefore, if there are appropriate notions of consistency
and entailment for these pairs, we will be able to form a domain having functions as elements.
Let us try out a formal definition first, and then look to an explanation of how it works.

DEFINITION 7.1. Let A and B be two information systems. By A — B, the function space, we
understand the system where:

(i) Da+e = {(u,v) | ue Con, and v € Cong};
(ii) Aap = (O,@); and where,
for all n and all w = {(uo, 0),---, (Un—1,Un—1)}, we have:

(iii) wG€Conap iff whenever J C {0,...,2—1} and Uf{u; | 7 € I} € Cong,
then U{v; | 2 € I} € Cong; and

(iv) wasp (u',v’) iff Ufvi|u’ Fa u}i sv’,
for all u’ € Con, and v’ EC Cong. 8

We have already explained the choice of data objects in (i) above, and the least informative
pair in (ii) is clearly right. Remember that as a data object (u,v) should be read as meaning
that if the information in u is supplied as input, then at least v will be obtained as output. It
is pretty obvious that one such data object by itself is consistent (they make constant functions,
don’t they?), but a set of several of these pairs may not be consistent. Hence, the need for part
(iii) of the definition. It can be read informally as follows: Look for a selection J of the indices
used in setting up w where the u; for z € J are jointly consistent. Since the pairs in w are meant
as correct information about a single function, then the combined input from all these selected
u; must be allowable. The function will then be required to give as output at least all the v,; for
i € I, owing to the fact that we are given that w is true of the function we have in mind. As
a consequence, the set UJ{v; | 7 € I} has got to be consistent, because it comes as output from
consistent input for a single approximable function. What we are arguing for is the necessity of
(iii)—the word “consistency” should mean that the data objects in the set are all true of at least
one function.

Finally we have to argue that (iv) must give the right notion of entailment for these data
objects. This can be seen by noting that for a fixed consistent w the set of pairs (u’, v’) satisfying
the right-hand side of (iv) defines an approximable function. In checking this we have to remark
that, for each u’ € Cong, the set Ufv; | u’ L-a ui} is consistent, so the definition makes sense.
The transitivity properties needed for proving that we have an approximable mapping are easy
to establish. This shows in particular that w is true of at least one approximable function, since
the separate pairs (u;,v;) all satisfy the definition. But it is also simple to argue that for any
approximable function, if w is true of it, then so is any pair (u’, v’) satisfying the definition of (iv).
Consequently, what we find in (iv) is the definition of the least approximable function generated by
w. The argument we have just outlined thus shows that the relationship w |-a-+B (u’, v’) means
exactly that whenever w is true of an approximable mapping then so is (u’, v’). It follows at once
that }-,..n is an entailment relation, and that the elements of A — B are just the approximable
Mappings, as we indicate in the next theorem.

<!-- page 22 (ocr) -->

598

THEOREM 7.2. If A, B, and C are information systems, then so is A + B, and the approzimable
mappings f : A — B are exactly the elements f € |A — BI]. Moreover we have an approzimable
mapping apply : (B + C) X B-+ C such that whenever g: BC andy € |B|, then

apply(g, y) = g(y)-

Furthermore, for all approzimable mappings h: A X B — C, there is one and only one approztm-
able mapping curry h: A -+(B — C) such that

h = apply o ((curry h) o fst, snd).

Proof. We have already remarked on the essentials of the proof above. Definition 7.1 was devised
to characterize exactly in Con,-_,p the finite subsets of approximable functions, which, as binary
telations, are being regarded as sets of ordered pairs. If f: A— B and if w C f, then from the
properties of approximable functions, it can be checked directly that w satisfies the right-hand
side of 7.1(iii). Conversely, if w € Cona_.p, then, as we have said, the relation which is defined
by 7.1(iv) and may be notated by:

T= {(u,v")| wae (wv)},

is an approximable mapping, as can be proved using the right-hand side of 7.1(iv) and the usual
properties of Fa and }g. Since w C W, we see that w }- ap w’ if, and only if, for all
approximable f : A — B, w C f implies w’ C f. (This is also the same as w’ C W, of
course.) From these considerations it follows that not only is A — B an information system, but
all approximable mappings are elements. Finally, if f € |A — B], then—as a binary relation —it
must be an approximable mapping, because the properties of Definition 5.1 are built into 7.1.

The construction of the special mapping apply as an approximable mapping also uses the
idea of 7.1(iv). The consistent sets of the compound space (B — C) x B are essentially pairs of
consistent sets, say w € Cong..c and u’ € B. Now the relation we want from such pairs to
consistent sets v’ € Cong is just nothing more or less than w |-p_.c (v’,v’). Our discussion in
the previous paragraph hints at why apply does in fact reproduce functional application when we

evaluate apply(g, y).

The definition of curry h uses the same trick of regarding a binary relation with one term in
a relationship being a pair as corresponding to another relation with one coordinate of the pair
shifted to the other side. Specifically, we can think of an approximable mapping h: AX B-+C
as a relation from pairs (u, v) of consistent sets for A and B, respectively, over to consistent sets w
for C. What we want for curry h is the relationship that goes from u to the pair (v,w). Of course
(v,w) is just one data object for B+ C, but the input/output passage from the consistent sets
of A to these objects is sufficient to determine curry h as an approximable mapping. The exact
connection between the two mappings is given in terms of function values as follows:

h(z, y) = (curry h)(z)(y),

for all 2 € {Aj and y € |B]. From this equation it follows that curry h is uniquely determined.
But, from what we know about apply, this is actually the same equation as that stated at the
end of the theorem. 4

<!-- page 23 (ocr) -->

599

Approzimations to functions. Why have approximable functions been given this name? In
general, clements of domains are the limits of their finite approximations. We have just indicated
why the approximable mappings from one domain into another do form the elements of a domain
themselves. We have explicitly shown how to construct the finite approximable mappings W.
A closer examination of the definitions would emphasize the very constructive nature of this
analysis. It follows that the approximable mappings can therefore be approximated by simple
functions. It does not follow that all approximable mappings are simple or constructive, since
what takes place.in the limiting process can be very complex. But the result does show how we
can start. to make distinctions once a precise sense of approximation is uncovered. 4g

Higher-type functions and the combinators. In the above discussion we have already combined
the function-space construction with other domains by means of products. But there is nothing
now stopping us from iterating the arrow domain constructor with itself as much as we like.
This is how the so-called higher types are formed. In certain categories, such as the category of
sets, this is a non-constructive move leading to the higher cardinal numbers. In the category of
domains, however, the construct ts constructive, because we have shown how to define all the
parts of A —+ B in terms of very finite data objects (assuming, it need hardly be added, that A
and B are constructively given).

Once the higher types have been formed as spaces, it must be asked what we are to do with
them. The answer is that there are many, many mappings between these spaces that can be
defined in terms of the simple notions we have been working with. These mappings are useful for
the following reason: the higher types provide remarkabe scope for modelling notions (as those
needed in denotatonal semantics for example), but the various aspects of the models have to be
related—and this is where these mappings come into play. We have already seen a preliminary
example in the last theorem, which can be interpreted as saying why the two domains shown are
isomorphic:

AXB+C=A-—>(B+C).

We have neither the time nor the space to present a full theory of higher-type operators
here, so some further examples will have to suffice. First, we have already made use of constant
mappings. Since the construction of them is very uniform, there ought to be an associated
operator. In fact, we have already been using it notationally. We have the approximable mapping
const : B — (A — B) that takes every element of B to the corresponding constant function. (It
has to be checked that this is an approximable mapping.) Note that there is a different mapping
for each pair of domains A and B, because the resulting types of const are different.

As another example, take the pairing of functions explained in Proposition 6.2. We can think
of the operator in this case being

pair: (C + A) x (C + B) + (C > (A x B)),
where for functions of the proper type we have:

pair(f,9) = (f,9).

There will be a similar operator for the construct of Proposition 6.4.

<!-- page 24 (ocr) -->

600

Of course the most basic operator of function composition is also approximable of the
appropriate type. We can write:

comp :(B— C) x (A + B) > (A C),
where for functions of the right types we have:

comp(g, f) = 90 f.

The approximability has to be checked, of course. But once a number of the more primitive
operators have been established as being approximable, then others can be proved to be so by
writing them as combinations of previously obtained operators. §

Categories again. All of what we have been saying about operators ties in with category
theory very nicely—as the category theorists have known for a long time. The technical term
for what we have been doing in part is cartesian closed category—that is a property of the
category of domains. Without going into details, that is essentially what 6.2 and 7.2 show of
our category. But domains have many other properties beyond being a cartesian closed category.
For example the possibility of forming sums is an extra (and useful) bonus, and there are many
others. Nevertheless, the categorical viewpoint is a good way of organizing the properties, and
it suggests other things to look for from our experiences with other categories. The next result
gives a particularly important notion that can be expressed as an operator. 4g

THEOREM 7.3. Let A be an information system. Then there is a unique operator, the least
fixed-point operator, such that

(i) fix: (A A) + A; and,
for all approzimable mappings f : A— A, we have:

(i) f(Bx(f)) C fix(,); and

(iii) for all z € AI, f f(x) C 2, then fix(f) C a.
Moreover, for this operator, condition (ii) is an equality.

Proof. This is a well-known result—especially the fact that the conditions above uniquely
determine the operator. The only question is the existence of the operator. The inclusion of
condition (ii) gives the hint, for fix(f) is the least solution of f(z) C z. Suppose z is any such
element, then if u C 2 and u f v hold, it follows that v C z. Now, since @ C x always holds, if
we wish to form the least z, we start with @ and just follow it under the action of f.

Specifically, we define fix(f) to be the union of all v € Con, for which there exist a sequence
Uo,-.+,;Un, € Con, where:

(1) up = Q;
(2) Uy f Ui+1 for all ¢ <n; and

(3) un =v.

<!-- page 25 (ocr) -->

601

. Because f is approximable, it is clear that fix f is closed under entailment. To prove that it is
consistent, suppose both v and v’ belong to the sets thrown into the union. We have to show that
v Uv’ is consistent and also is thrown in. Consider the two sequences up;...,tn € Conga and
Ug’,...,Un’ € Con, that are responsible for putting v and v’ in. It is without loss of generality
that we assume they are of the same length, since we can always add lots of @’s onto the front of
the shorter one and still satisfy (1)-(3). Now one just argues by induction on 7 that the sequence
of unions u; U u,’ satisfies (1)-(3) with respect to vu Uv’.

But why is fix approximable? The method of proof is to replace f by @ in (2) above, and
to use the condition that there exists a sequence satisfying (1)-(3) as defining a relation between
sets w € Cona_.a and sets v € Cong. It is not difficult to prove that this is an approximable
mapping in the sense of the official definition. Clearly this relation determines fix as an operator.
|

The result above not only proves that every approximable mapping of the form f: A+ A
has a fixed point as an element of A, but that the association of the least fixed point is itself
an approximable operator. The formulation makes essential use of the partial ordering of the
domains, but Gordon Plotkin noticed as an exercise that the characterization of the operator can
be given entirely by equations.

PROPOSITION 7.4. The least fixed-point operator ts uniquely determined by the following three
conditions:

(i) fixg : (A A)— A, for all systems A;
(ii) fixa(S) = f(fixa(S)), for all f: A— A; and

(ili) A(fixa(S)) = fixn(g), whenever f: A> A,g: BB, h: AB,
provided that ho f =g yh and h(la)=ts. 8

Remarks on the space of strict mappings. In 7.4 and many other places we have had occasion
to make use of mappings that take the bottom element of one domain over to the bottom element
of the other domain. Such mappings are called strict mappings because they take a strict view
of having empty input. As notation we might write

f:A-,B

to mean that f is a strict approximable mapping (7.e. f(a) = 1p). The totality of domains
and strict mappings forms an interesting category in itself, but it is best used in connection with
the full category of all approximable mappings.

The collection of strict mappings forms a domain, too. The way to see this is to refer back to
Definition 7.1 and add an additional clause ruling out non-strict mappings as inconsistent. What
has to be added to 7.1(iii) is the conjunct on the right-hand side to the effect that if the condition
Ota Ufu; | 7 € I} holds, then @ fF-p U{v; | 2 € J} holds too. By the same arguments we used
before, it follows that this is the appropriate system for the domain of strict mappings. We can
denote it by (A —, B)

There is also a useful operator

strict : (A — B) > (A, B)

<!-- page 26 (ocr) -->

602

defined by the condition that for f: A — B we have:
ustrict(f)v iff eitherO}-pvor Oa uanduf v,

for all u € Con, and v € Cong. This operator converts every approximable mapping into the
largest strict mapping contained within it.

Since every strict mapping ts an approximable mapping, there is also an obvious operator
going the other way. The pair of operators shows that A —, B as a domain is what is called a
retract of A— B. There is an interesting theory of this kind of relationship between domains,
but we cannot enter into it here.

As a very small application of the use of strict mappings, we remark that the following two
domains are isomorphic:

A XA & (BOOL -, A).

The mapping from right to left is called the conditional operator, cond, and we have for all
elements x,y € |A| and t € |BOOL|

z, if t = true,
Y, ift = false.

cond(z, y)(t) = {

8. Some domain equations. Having outlined the theory of several domain constructs, the
final topic for this paper will be the discussion of the iteration of these constructs in giving
recursive, rather than direct definitions of domains. These recursively defined systems have often
been called “reflexive,” because the domains generally contain copies of themselves as a part of
their very structure. The way that this self-containment takes place is best expressed by the
so-called domain equations, which are really isomorphisms that relate the domain as a whole
to a combination of domains—usually with the main domain as a component. This description
is rough, since recursion equations for domains can be as complex as recursion equations for
functions. We will not enter into a full theory of domain equations now but will just review
some preliminary examples to illustrate how the new presentation makes the constructions more
explicit.

A domain of trees or S-expressions. This is everyone’s favorite example. And a very nice
example it is, but we should not think that it contains all the meat of the theory of domain
equations. Even if we generalize the kinds of equations to contain all iterations of the domain
constructs + and X, the full power of the method has not been exploited. We will try to make
this clear in the further examples.

Let a domain (information system) A be given. What we want to construct is a domain T
of “trees” built up from elements of A as “atoms”. For simplicity we consider unlabelled binary
trees here, but more complex trees are easy to accommodate. The domain equation we want to
“salve” is this one:

T = A+(TX 1).

<!-- page 27 (ocr) -->

603

If such a domain exists, then we can say that (up to isomorphism) the elements of the domain
T are either bottom, or elements of the given domain A, or pairs of elements from the domain T
itself. And these are the only kinds of elements that T has.

To prove that such a domain exists it is only. necessary to ask what information has to be
given about a prospective element. The answer may involve us in a regress, but the running
backwards need not be infinite—at least for the finite elements. As we shall see, the infinite
elements of T can be self-replicating; but, to define a domain fully, all we have to do is to build
up the finite elements out of the data objects in a systematic way. Fortunately, in order to satisfy
the above equation, the required closure conditions on data objects are simple to achieve.

In the first place, we need copies of all the data objects of A to put into the sum. The easy
way to do this is to take an object A not in D, and to let, by definition,

Ay = (A, A).

That gives us one member of Dy, the one we always have to have in any case. The copy of an
X € Dg is just going to be (X, A). The other members of Dy will be of the form (A,U), where
U gives us information about the other kind of elements of T. The point is that T has to be a
sum, and we are using just the scheme of Definition 6.3 to set this up.

Next we have to think what kind of information the U above should contain. Because we
want a product, we refer back to Definition 6.1 and imagine we have already defined Dp. What
6.1(i) suggests is that we throw in a bunch of other data objects into Dp. The only point that
needs care is that the data objects for the product must be copied into the overall sum. With this
in mind, the following clauses give us the inductive definition of Dr:

(1) Ag € Dy;
(2) (X,A)€ Dy whenever X € Da; and
(3) (A,(Y,Ar)) € Dy, and (A,(Az, Z)) € Dr whenever Y,Z € Dy.

Of course,when we say “inductive definition,” we mean that Dy is the least class satisfying (1)~(3).
By standard arguments it can be shown that Dy satisfies this set-theoretical equation:

Dy = {Ar}U{(X, A) | X € Da} UA, (Y, Ar) |¥ € Pr} UL(A, (At, 2)) | 2 € Dr}.

In fact, with some very mild assumptions about ordered pairs in set theory, Dy is the only solution
to the above equation.

Defining the data objects is but part of the story: the same data objects can enter into
quite different information systems. Data objects are just “tokens” and are only given “meaning”
when Cony and |-7 are defined. Let us consider the problem of consistency first. We already
understand the notion as it applies to sum and product systems, so we must merely copy over
the parts of the previous definitions in the right position for the definition of Cony. There are
two forms we could give this definition; perhaps the best is the inductive one. We have:

(4) @€Conz;

(5) uU {Ap} € Cony whenever u € Conq;

<!-- page 28 (ocr) -->

604

(6) {(X,A)|X € w} € Cony whenever w € Cong;

(7) {(A,(¥,Ar)) |¥ €u}u {(A, (Az, Z)) | Z € v} € Cone
whenever u,v € Cony.

Conditions (4)-(7) certainly make the inductive character of Cony clear—again, let us emphasize,
the set being specified is the least such. Also clear from the definition is the fact that a consistent
set of T—aside from containing Ay—is either a copy of a consistent set of A or a copy of a
consistent set of T x T. We could thus state a set-theoretical equation for Cony similar to the
one for Dry.

It remains to define entailment for T. Here are the inductive clauses which are pretty much
forced on us by our objective of solving the domain equation:

(8) uber Ap always;
(9) uUf{Ar}}-r Y whenever u}- 7 Y;
(10) {(X,A)|X €w}/ vy (W,A) whenever w/a W;

(11) {(A, (Y, Ar)) Y € u} U {(A, (Ar, Z))} Kr (A, (X, Ar))
whenever u|-7 X and v € Cony; and

(12) {(A, (Y, Ar)) | YE u} U {(A, (Ar, Z))} br (A, (Ar, X))
whenever uf}-y X and u€ Cony.

Inductive definitions engender inductive proofs. It now has to be checked that consistency and
entailment for T satisfy the axioms of 2.1. The steps needed for this check are mechanical. (The
proof may be aided by noting that the cases in (4)~(7) and in (8)-(12) are disjoint—except for a
trivial overlap between (8) and (9). The cases get invoked typically by asking, when confronted
with an entailment to prove, for the nature of the data object on the right of the [?turnstile].)

Having defined and verified that T is an information system, the validity of the domain
equation for T is secured by forming the right-hand side and noting that Tis identical to A +
(T x T). The reason is that we carefully chose the notation to match the official definitions of
sums and products. (In general, in solving domain equations some transformation might have to
take place to “re-format” data objects if things are not set up to be literally the same.)

It should be remarked that the sense can be made precise in which T is the least solution of
the given domain equation. (It is an initial algebra in a suitable category of algebras and algebra
homomorphisms.) It is pretty obvious that it is minimal in some sense, because we put into it
only what was strictly required by the problem and nothing more.

It is also fairly obvious that there are many solutions to this domain equation. A non-
constructive way to obtain non-minimal solutions is to interpret the whole construction of T in
a non-standard model of set theory. Though, in the definition of Dy, it looks like we are only
working with very finite objects, everything we did could be made abstract and could be carried
out in some funny universe. The result would be a system of “finite” data objects having all
the right formal properties but containing things not in the standard minimal system. We would
then take the notions of consistency and entailment that also exist in the funny universe and

<!-- page 29 (ocr) -->

restrict them to sets of data objects that are actually finite in the standard sense. It can be seen
from the formal properties of the construction that the resulting notions satisfy our axioms for
an information system and that the domain equation holds—BUT the system would have many
different elements beyond what we put into the original T. To make this construction work,
by the way, we would have to force A to be absolute in the model: if it is actually finite (say,
A = BOOL), then there is no problem. (Constructive methods for introducing “nonstandard”
data objects can also be given.)

Finally, we must remark on why we called T a domain of S-erpressions. The answer becomes
clear when we structure T as an algebra. First, there is an approximable mapping

atom: A—-T,

which injects A into T making the elements of A “atoms” of T. Then there is a truth-valued
predicate on T which decides whether an element is an atom:

isatom : T + BOOL.
Finally, since T X T is a part of T, we can redefine the paring functions so that:
pair: TX T—T, fst: TT, and snd: TT.

In LISP terminology, these operations are the same as the familiar cons, car, and cdr. This makes
T into an algebra where, starting from atoms, elements—expressions—-can be built up by iterated
pairing.

But why is our system different from the usual way of regarding S-expressions? The answer
is that by including partial expressions (those involving |p) and by completing the domain
with limits, infinite expressions are introduced. For instance, if a € |T|, then we can solve the
fixed-point equation:

x = pair(atom(a), z),

which is an infinite list of a’s. This is but one example; the possibilities have been discussed in
many papers too numerous to mention here.

As is common to remark, S-expressions can also be thought of as trees: the parse tree that
gives the grammatical form of the expression. What we have added to the idea of a tree is
possibility of having infinite trees, and having all these trees as elements of adomain. 4

A domain for \-claculus. A lengthy discussion with many references on -calculus models
can be found in Longo [1982]. All we wish to remark on here is how the method of construction
by solving a domain equation can be fit into the new presentation. What I have added to the
previous ideas (that in any case came out of an analysis of finite elements of models) is the genera]
view of information systems. In particular the models obtained this way are not lattices—hence,
the need for the calculations with Con. I hope that the presentation here makes it clearer how
“pure” \-calculus models can be related to other domains having other types of structures—for
instance, those needed in denotational semantics.

The domain equation we wish to solve is:

D = A+(D-—D).

<!-- page 30 (ocr) -->

606

We proceed in much the same way we did for T, except we must now put in data objects
appropriate to the function space. Here is construction, where again A is chosen outside Ds
and Ap = (A, A):

(1) Apne Dp;

(2) (X,A)€ Dp whenever X € Da;

(3) (A,(u,v)) € Dp whenever u,v € Conp;

(4) @€Conp;

(5) wi {Ap} € Conp whenever u € Conp;

(6) {(X,A)|X € w} € Conp whenever w € Cony; and

(7) {(A, (uo, v0)), ---, (A, (un—1, Un—1))} € Conp provided u,, v; € Conp
for.all 7 <n and whenever J C {0,...,n—1} and Uf{u; | + € I} € Conp,
then Uf{v; | 2 € I} € Conp.

What is different here from the definition of T is the fact that the concepts Dp and Conp are
‘mutually recursive because the data objects are themselves built from consistent sets. The scheme
is based on a combination of the sum construct and the function-space construct, but the mutual
recursion allows “feedback” to occur.

To complete the definition we have to give the clauses for the inductive definition of entail-
ment. They are:

(8) ul pAp_ always;
(9) uU{Ap}lpY whenever utp Y;
(10) {(X,A)|X € w}}-p (W,A) whenever w}-, W;

(11) {(A, (uo, v0), .--, (A, (Un—1, Un—1))} Ep (A, (u’, v’))
whenever (J{v; | u’ Kp us} Lp v’ and the set on the left is in Conp.

Obviously these definitions are much shorter if we have a domain in which all sets are consistent,
but there are many reasons for retaining the consistency concept throughout. The check that D
is an information system and satisfies the domain equation is mechanical. We cannot detail here
how this construction provides a \-calculus model.

It is clear that these definitions are constructive, and that, with a suitable Godel numbering
of the data objects, the predicates for consistency and entailment are recursively enumerable.
However, the recursion used builds up the predicates by going from less complicated data objects
to more complicated ones; therefore, the predicates must be recursive, because, for a certain size
data object, the derivation that puts it into the predicate is of a bounded length. This observation
helps in the discussion of the computability of the operators defined on these domains—another
topic we cannot discuss here. 4

<!-- page 31 (ocr) -->

607

A universal domain. As a final example of building up domains recursively, we give a
construction of a “universal” domain U. (The reason for the name will be explained presently.)
The best way to define U seems to be to define a domain V with a top element first,and then to
remove the top.

The recursion for V is remarkably simple. We begin with two distinct objects A and V that
give information about the top and bottom of V, respectively. Thus, Ay = A by definition. We
assume that these two special data objects are “atomic” in the sense that they are not equal to
any ordered pair of objects. For the definition of Dy we have these clauses:

(1) A,VED;
(2) (X,A)€ Dy and (A,Y) € Dy whenever X,Y € Dy.

In other words, we begin with two objects and close up under two flavors of copies of these objects.
(A product result is involved here, so that is the reason for structuring the flavors the way we
have.)

For V all subsets of Dy are consistent, so all we have left is to define entailment for this
domain. The clauses are:

(3) ufyA always;

(4) u ry V whenever either V € u or {X | (X,A) Eu} }-v V
and {Y |(A,Y) Eu} kv V;

(5) uly (X"',A) whenever either V € u or {X | (X,A) € u} }-v X’; and
(6) ult v(A,Y¥’) whenever either V € u or {Y |(A,Y) Eu} Fv ¥’.

The proof that V is an information system proceeds as before. Note that, under the above
definition of entailment, the data objects A,(A, A), ((A, A), A), ete. are all equivalent. There is,
however, no other data object equivalent to V. The domain equation satisfied by V is:

V=VvVxV.

Of course, there are an unlimited number of solutions to this equation, so the fact that V satisfies
it tells us very little.

Because V entails everything, we can regard it as a “rogue” object that ought. to be banned
from polite company: the only element of V it gives any information about is the top ele-
ment, which is as unhelpful as any element could be. We should simply throw it out as being
“inconsistent.” What remains is the domain U. Formally we have:

(7) Du = Dy —{¥};
(8) Au = Ay;
(9) Cony = {u C Dy | u finite and u}“y V}; and

(10) uf-uY iff u€ Cony, Y € Dy and u}-vY.

<!-- page 32 (ocr) -->

608

The same style of definition would work in any situation when an information system has a rogue
data object that entails everything: there always is a system that results from eliminating all
those objects that entail everything. Indeed, we could have always included such an object in any
domain and altered the definition to take as elements those deductively closed sets of data objects
that do not have the rogue object as a member. We did not do this for the reason that superfluous
elements cause lots of exceptions in constructs such as product, where there is a temptation to
let them enter into various combinations.

Now in U we do allow V to enter into combinations—and this is part of the secret of the
construction. The consequence is, however, that the domain equation which U satisfies is not too
easy to state since it involves an unfamiliar functor. So it is not through such equations that we
will understand its nature in a direct way. But it is possible to explain how it works by reference
to the steps in the construction.

Imagine the full (infinite) binary tree. The data objects of U are giving information about
possible paths in the tree. We think to the tree starting at the root node at the top of the page
and growing down. The object A gives no information—so no paths are excluded. (If we would
have allowed V, then the information it would have been giving is that all paths are excluded.)
The data object (X, A) tells us about a path that ether it is unrestricted on the right half of
the tree, or on the left, when we start at the node directly below the root, the paths that are
excluded from the subtree are those excluded according to X. This makes sense because the
subtrees of the binary tree look exactly like the whole tree, so information can be relativized or
translated to other positions. With (A, Y) the roles of right and left are interchanged. We could
have introduced data objects of the form (X,Y) which tell us information about both halves of
the tree at the same time, but the consistent set {(X,A),(A,Y)} does the same job. In general
consistent sets should be thought of as conjunctions; while, in this example, the comma in the
ordered pair should be thought of as a disjunction when “reading” information objects.

We can now see that a single data object (if it contains V) looks down the tree along a finite
path to some depth and then excludes the rest of the tree. below that node. A consistent set of
data objects leaves at least one hole, so at least one path is not excluded. The maximal consistent
sets of information objects are those giving true information about one single (infinite) path—the
total elements of the domain U correspond exactly to the infinite paths in the binary tree. The
partial elements are harder to describe geometrically, however. In accumulating information into
a consistent set, holes can be left all over the tree. A partial object is therefore of an indeterminate
character, since the “path” we are describing might sneak through any one of the holes. (There
is, by the way, a precise topological explanation of what is happening. The total elements of U
form a well-known topological space, the so-called Cantor space, and the partially ordered set of
elements of U is isomorphic to the lattice of open sets of the space—save that the whole space is
not allowed.)

This is all very well, but what, we ask, is the good of this domain, and why is it called
“universal”. The proof cannot be given here, but the result is as follows. As a consequence of
standard facts about countable Boolean algebras, it can be proved that every “countably based”
domain is a subdomain of U. More specifically, if A is an information system, and if D4 is
countable, then there exists a pair of approximable mappings

a:A-+U and 6: U-A,

<!-- page 33 (ocr) -->

609

such that
boa=I, and aobC ly.

This makes A a special kind of retract of U. The mappings a and b are far from unique, but at
least there is one way to give a one-one embedding of the elements of A into the elements of U.

The universal property of U can be applied quite widely. For example, since (U — U) is a
system with only countably many data objects (by explicit construction!), this system is a retract
of U. Fixing on one such retraction pair as above, makes U also into a model of the d-calculus.
Whether different retractions give essentially different models I do not know. But the point of the
remark is to show that domains can contain their own function spaces for a variety of interesting
reasons. [ff

A domain of domains. Not many details can be presented here, but we would also like to
remark that even domains can be made into a domain. One way of getting an idea of how this is
possible is to note that since subdomains of U correspond to certain kinds of functions on U, and
since the function space of U is also a subdomain of U, it might be suspected that the subdomains
of U form a single subdomain of U.

That is a fairly sophisticated way of reaching the conclusion (and many details have to be
worked out). A more elementary approach would be just to ask what it means to give a finite
amount of information about a domain. For the sake of uniformity, suppose that the data objects
of the possible domain are drawn from the non-negative integers, and that we conventionally use
0 for A. Then to give a finite amount of information about a domain is—roughly—to specify a
finite part of Con and a finite part of }}. To make the formulation easier, we will reserve for 1 a
role like the one recently played by V. What the specifications will boil down to is pairs (u, v) of
finite sets of integers used as data objects to convey one piece of information about an entailment
relation.

But hold, entailment relations are very closely connected to approximable mappings. Indeed,
we remarked before that the identity function as an approximable mapping on a domain is just
represented as the underlying entailment relation itself. Suppose we take as our domain the
domain of all sets of integers. It is a powerset, so call it P. That is to say, the integers are the
data objects, all finite sets are consistent, and the entailment relation is the minimal possible one.
(As far as elements go, an arbitrary set of integers is equal to the union of all its finite subsets,
which means that the elements of the domain are in a one-one correspondence with the arbitrary
sets of integers.) The question is: which approximable mappings on P into itself correspond to
entailment relations on the integers as data objects?

The answer can be expressed most succinctly using our standard notation. If we think of
r: P-— Pas a relation between finite sets in the usual way, then to say that r is reflexive is to
say:

(1) Ip C rT.
To say that r is transitive is to say:

(2) ror=r.

<!-- page 34 (ocr) -->

610

To say that for r the object 0 plays at being A is to say:
(3) OC r(1),

where in general 7% is short for {n} in the domain P. Then, to say that 1 plays at being a rogue
object is to say:

(4) T =7(i).
Finally, to say that 1 is an inconsistent object that has to be excluded is to say:

(5) 1Zr(0).

That’s it. The collection of approximable mappings satisfying (1)~(5) gives us all the entail-
ment relations we need. Condition (5) is a consistency condition, and for r the consistent finite
sets u are those such that 1 Z r(ui). What we are asserting is that the totality of r satisfying
(1)-(5) forms the elements of a domain—one that has been derived from (P — P) in a way similar
to the way we derived U from V above.

Having made domains into a domain, the next step is to see how constructs on domain
(i.e. functors) can be made into approximable mappings. But the retelling and development of
that story will have to wait for another publication along with the very interesting chapter on
powerdomains. I only hope the ground covered here makes the theory of domains seem more
elementary and more natural. 4
