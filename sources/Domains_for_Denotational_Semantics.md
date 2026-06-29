---
source_pdf: Domains_for_Denotational_Semantics.pdf
title: "Domains for Denotational Semantics"
author: Dana Scott
year: 1982
citation_key: Sco82
alias: "Information systems presentation (ICALP 1982)"
bibliography: "Scott, D. Domains for Denotational Semantics. ICALP 1982, LNCS 140, pp. 577–613."
pages: 34
extraction_method: "pdftotext"
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

- [ ] p.3: 9 Simple definitions of the basic concepts can be given.
- [ ] p.3: 9 Detailed properties are proved as theorems rather than assumed as axioms.
- [ ] p.3: 9 Emphasis can be given to the constructive nature of the definitions.
- [ ] p.3: 9 Domains can be made more visible.
- [ ] p.3: DEFINITION 2.1. An information system is a structure
- [ ] p.5: PROPOSITION 2.3. For all u, v, w, u t, v ~ C Con, we have:
- [ ] p.26: 9    IV,        if t = false.   II

---

## Transcription


<!-- page 1 (pdftotext) -->

                               DOMAINS FOR DENOTATIONAL                                      SEMANTICS

                                                                          by
                                                                  Dana S. Scott
                                               D e p a r t m e n t of C o m p u t e r Science
                                                    Carnegie-Mellon U n i v e r s i t y
                                                P i t t s b u r g h , P e n n s y l v a n i a 15213


          Abstract. The purpose of the theory of domains is to give models for spaces on which to define
          computable functions. The kinds of spaces needed for denotational sematics involve not only spaces
          of higher type (e.g. function spaces) but also spaces defined reeursively (e.g. reflexive domains). Also
          required are many special domain constructs (or functors) in order to create the desired structures.
          There are several choices of a suitable category of domains, but the basic one which has the simplest
          properties is the one sometimes called consistently complete algebraic cpo's. This category of domains
          is studied in this paper from a new, and it is to be hoped, simpler point of view incorporating
          the approaches of many authors into a unified presentation. Briefly, the domains of elements are
          represented set theoretically with the aid of structures called information systems. These systems are
          very familiar from mathematical logic, and their use seems to accord well with intuition. Many things
          that were done previously axiomatically can now be proved in a straightfoward way as theorems.
          The present paper discusses many examples in an informal way that should serve as an introduction
          to the subject.


1. I n t r o d u c t i o n .     I would like to begin w i t h some personal r e m a r k s . W h e n I t h i n k of t h e
n u m b e r of h e a d a c h e s I h a v e caused people in C o m p u t e r Science w h o have tried t o figure out t h e
[?m a t h] e m a t i c a l details of t h e [?T h e o r y] of Domains, I have to cringe. T h e difficulty in t h e p r e s e n t a t i o n
of t h e s u b j e c t is in justifying t h e level of a b s t r a c t i o n used in c o m p a r i s o n w i t h the payoff: t o o often
the effort needed for u n d e r s t [?a n d] i n g t h e a b s t r a c t i o n s does n o t seem w o r t h t h e t r o u b l e - - e s p e c i a l l y
if the notions are u n f a m i l i a r or excessively general.

      For example, C a t e g o r y Theory, w h i c h is m u c h used in discussions of t h e [?T h e o r y] of Domains,
seems far too a b s t r a c t to m a n y people. On t h e o t h e r h [?a n d] , A u t o m a t a [?T h e o r y] - - w h i c h h a s often
benefited from some use of Category [?T h e o r y] - - i s quite a b s t r a c t and, i n m a n y aspects p e r h a p s ,
quite useless, b u t t h e level of a b s t r a c t i o n is fairly low [?a n d] the reasons for the definitions are
usually evident. Thus, t h e subject h a s become by n o w a s t [?a n d] a r d topic even for u n d e r g r a d u a t e
courses, l believe t h a t Michael R a b i n and I h a d m u c h to do w i t h influencing the s u b s e q u e n t
development of the [?t h e o r y] by f o r m u l a t i n g some years ago some basic concepts ( m a n y previously
known) in a way t h a t m a d e sense to anyone w h o h a d been exposed to a little A b s t r a c t Algebra,
Logic [?a n d] Set Theory. T h i s expository p a r t of our p a p e r did n o t require originality, b u t r a t h e r
a certain f r a m e of m i n d [?a n d] a c e r t a i n style of w r i t i n g to p u t t h e ideas [?a n d] p r o b l e m s in s h a r p
relief. (The original p a p e r is R a b i n - S c o t t [1959]; see t h e excellent historical review of t h e subject
in G r e i b a c h [1981].)

     D o m a i n [?T h e o r y] has fared less well. I feel I m a d e a mistake in 1969 in using L a t t i c e [?T h e o r y]
as a m o d e of p r e s e n t a t i o n - - a m i s t a k e as far as C o m p u t e r Science is concerned. Lattices are
very familiar to logicians and those i n t e r e s t e d in Universal Algebra, [?a n d] I liked very m u c h t h e
structures I found. B u t it takes some time to learn the special terminology [?a n d] to become
comfortable w i t h t h e necessary examples. Indeed, w i t h o u t a stock of examples, it is impossible
to have sufficient i n t u i t i o n for m a k i n g the required constructions. True, some people took to
the approach, [?a n d] t h e lattice-theoretic definitions were simple e n o u g h to motivate. B u t a m u c h

<!-- page 2 (pdftotext) -->

                                               578



greater percentage of people I came in contact with found the large number of things to learn
a definite roadblock to understanding. And the Lattice Theory was only partly standard, since
this approach to the theory has to employ complete lattices and topological notions in order to
explain limits and continuity adequately. In fact, Topology of a rather mathematically simple
set-theoretical kind could have been used as the whole foundation much as in Scott [1972], but
that kind of mathematics seems even tess attractive to computer scientists. Again, it is a matter
of background, I think, and it is unreasonable to expect people to know everything. Nevertheless,
the lattice-theoretic approach has great consistency and coherence; it has been carried out in full
detail in Gierz, et al. [1980], which also gives the topological connections. That book contains a
large number of references to the mathematical literature to show the connections of the theory to
many other topics. What we had to miss out there is a clear hook-up with computability theory,
owing simply to a lack of space and time to be able to cover everything.

     In Scott [1981], I tried out another, different presentation (which is also explained in Scott
[1982].) However, I have found that the use of neighborhood systems causes confusion in people
not used to thinking in terms of sets of sets of sets of sets . . . , even though the set theory
required is quite simple. My purpose in the present lecture, then, is to go back once more to the
very beginning to try out another plan for making the story easy and natural. The notion to be
used I call an information system. This is a "static" notion appropriate to bodies of information
about coherent groups of elements. The "dynamic" ideas enter in the ways different systems can
be related and in the semantical definitions about meanings of programming language constructs.
(For discussions of semantical definitions see Stoy [1977], Gordon [1979], and Tennent [1981].)
Neighborhood systems are, in a precise sense, equivalent to information systems, but there seems
to be an interesting trade-off between what properties of structures are axiomatized and what are
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
can be helpful here. A step in the right direction has been made in the LCF system (see Gordom
Milner-Wadsworth [1979]), which, however, does not take advantage of general Category Theory;
but the whole area needs much more development in my opinion.

     The main purpose of the Theory of Domains in Denotational Semantics, as I see it, is to
give a mathematical model of a system of types---including function-space types--and to explain

<!-- page 3 (pdftotext) -->

                                                       579



a notion of computability with respect to these types. There are many possible theories of
types, but the construction of domains is meant to justify reeursive definitions at all types,
[?a n d] - - m o s t essentially--to justify recursive definitions of types. Pursuing these goals has certain
consequences, as we shall see. The model presented here is only one approach, and some
comparisons with other methods wilt be made in Section 8. Again some help from Category
Theory would be welcome in comparing the different kinds of modelling.

     One benefit of Domain Theory is that it is possible to make sense of types containing infinite
elements. The cost required seems to be that the domains therefore have to contain partial
elements as well as total elements. And this is where the lattice-theoretic definitions entered in
the earlier presentations: the partial ordering with relations like x [- y was Used to express the
fact that the element x was "less defined" (i.e. more partial) than y but "contained in" y. The
relation g-, however, must be subjected to many axioms to have a theory suitable to the desired
applications. Instead of such a big group of axioms, I wish to put forward here a construction
where the "skeleton" (or better: "backbone") of a domain is introduced by j u s t a few axioms.
Then the domain itself is defined as a certain construct from the backbone in order to define the
appropriate notion of element. There are several advantages I can see to the new approach:

       9 Simple definitions of the basic concepts can be given.

       9 Detailed properties are proved as theorems rather than assumed as axioms.

       9 Emphasis can be given to the constructive nature of the definitions.

       9 Domains can be made more visible.

       9 The theory of domains is made more available for applications, because it is easier
         to produce the needed complex domains.

It is to be hoped t h a t the reader can judge the validity of these claims from the perhaps too brief
exposition to follow.


2. Information systems.       Intuitively, an information system is a set of "propositions" that can
be made about "possible elements" of the desired domain. We will assume that sufficiently m a n y
propositions have been supplied to distinguish between distinct elements; as a consequence, an
element can be constructed abstractly as the set of all the propositions t h a t are true of it. Partial
elements have "small" sets; while total elements have "large" sets (even: maximal). To make this
somewhat rough idea precise, we have to e x p l a i n - - b y a suitable, but small choice of a x i o m s - - h o w
the collection of all propositions relevant to the domain hangs together, or better, is structured
as a set of abstract propositions. Fortunately, the axioms for this structure are very simple and
familiar, which is a great help in making up examples.

DEFINITION 2.1. An information system is a structure

                        (p, ~,Con, F-),
where P is a set (the set of data objects or propositions), where A is a distinguished member of
D (the least informative member), where Con is a set of finite subsets of P (the consistent sets
of objects), and where [?~--] is a binary relation between members of Con and members of /) (the

<!-- page 4 (pdftotext) -->

                                                     580



entailment relation for objects). Concerning Con, the following axioms must be satisfied for all
finite subsets u, v C_ P:

       (i)     u C Con, whenever u C v E (]on;

       (ii)    {X} E Con, whenever X E P; and

       (iii)   u U { X } E Con, whenever u [?[--] X .

Concerning [?~--], the following axioms must be satisfied for all u, v E Con, and all X E P:

       (iv)    u ~- A;

       (v)     u [?~--] X , whenever X E u; and

       (vi)    if v [?F--] Y for all Y C u and u [?[--] X , then v [?[--] X .

In words we may say of Con that, as a set of sets, (i) it is closed under subsets, (ii) it contains
all singletons, and (iii) adjunetion of an entailed object to a consistent set preserves consistency.
Concerning [?[--], which should be viewed as a "multiary" relation, we may say t h a t (iv) A is
entailed by anything, (v) [?[--] is reflexive, and (vi) [?[--] is transitive. (The last two properties are
both expressed in a way appropriate to a multiary relation on members of P.)          l

     The best advice is to think of the members of P as consisting of finite d a t a objects, some of
which are more informative than others. The word "finite" should be taken here in the sense of
"fully circumscribed"--as regards w h a t is given in A these data objects can be comprehended in
"one step." It is of course possible to introduce information systems where the data objects are
infinite sets, but relative to A they are finite as d a t a objects.

    The member that provides zero information is A. D a t a objects are intended to give infor-
mation about possible elements of the domain to be constructed, so if we were to use A alone,
we would be describing the the least defined elelnent usually written as _l_.

     Not just any combination of d a t a objects will describe a possible element, however; hence,
the need for the notion of consistency. If u E Con is false, then the "propositions" in u cannot all
be applied to the same element at the same time. Finally we haxe to agree that, in general, the
propositions to be allowed are rarely mutually independent. It follows t h a t an entailment relation
must be imposed to record the dependencies t h a t do hold among the propositions. With these
informal understandings, the axioms chosen should all be self-evident.


     A first example. Suppose we let P be the set of non-negative integers, where we think of an
integer n as an abbreviation of the proposition n < x. Here x is a yet-to-be-detcrmincd element,
about which one proposition gives only a little information. We can identify A with 0, and take
Con to be the set of all finite subset:s of P. The entailment relation can be defined formally in
the way suggested by the intuitive reading of the d a t a objects:

        {no,...,nk-1}~-m          iff either m = 0 or m < ni for some i < k.

(Remember to think of the same possible x on both sides of the ~ .) T h a t [?[--] is an entailment
relation in the sense of our axioms is clear. I

<!-- page 5 (pdftotext) -->

                                                      581


     A second example. The first example is possibly misleading because all (finite) sets of d a t a
objects were allowed to be consistent. The example can be modified in a natural way so this is n o t
so; of course, quite a different system wilt be obtained. The idea is to let P be the set of all pairs
(n, m) of integers with n < m, where such a pair stands now for the proposition n < x < m .
Clearly the two data objects (0,2) and (3,7) taken together are inconsistent. (Why?)

      Oh, I see, I have left out A from P; we must therefore include the somewhat artificial pair
(0, oo) with the obvious interpretation. W h e n I say "obvious interpretation" here I mean t h a t
u E Con can be defined by saying t h a t there must be an integer satisfying all the "propositions" in
u. Further, u [?[--] X can be defined by saying t h a t whenever an integer satisfies all the propositions
in u, then it must satisfy X . The notion of "satisfy" really should be obvious from the intuitive
reading given to the d a t a objects, and the reader can verify easily that all the axioms hold for
this example of an information system.        I


      A third example. Let A and B be two fixed sets, and let /) as a set consist of the ordered
pairs (a, b), with a C A and b E B, plus the extra object A. Here the "information" contained in
(a, b) is t h a t a is mapped to b by a yet-to-be-determined function. With this thought in mind, we
will know t h a t a finite set of d a t a objects is consistent just in case it is possible t h a t they can all
belong to the same function. Formally, we can assert:

     {(a0, bo) . . . . . (ak--1, bk--1)} C Con iff for all i , j < k whenever a, = aj, then b, -~- bj.

It is something of a bother having to throw in A in this case, but all we have to say is that if u
is consistent under the above rule, then so also will u tA {A}; and these are the only consistent
sets of data objects for this example. Perhaps it would make more sense to use {(a, b)) in place
of the simpler (a, b), and then we could set A = O more naturally. From this point of view we
can regard each data object as a (very small!) fragment of the graph of a function; the consistent
sets then point to larger fragments of graphs.

     The definition of the entailment relation is the minimal one:

                          u[--XiffeitherX=AorXEu.

These examples show t h a t sometimes the main part of the structure is in Con, sometimes it is in
 [?[--], and sometimes it is in the interplay between the two notions. The object A is not in itself
very important, but it is sometimes useful to have an object there t h a t can always be counted
upon to act in the same way in every system.      I

    Already in formulating the axiom about the transitivity of ~- a relation between sets in Con
was suggested; we now make this official.

DEFINITION 2.2. For u, v E Con we write u [?~--] v to mean t h a t u [--X for all X E v.                 I

PROPOSITION 2.3. For all u, v, w, u t, v ~ C Con, we have:

       (i)     o ~- {~};
       (ii)    u [?[--] v implies u U v E Con;

       (iii)   u [?[--] u;

<!-- page 6 (pdftotext) -->

                                                              582



         (iv)    u [?~--] v [?a n d] v ~ - w i m p l y u ~ - w;

         (v)     u I D_ u, u ~- v, and v D_ v' i m p l y u I [?~--] vt ; [?a n d]

         (vi)    u [?[--] v [?a n d] u ~ - v' imply u ~ v U v'.

Proof.    Obvious.         !


        R e m a r k . It is not w o r t h f o r m u l a t i n g a formal result a t this point, b u t it should be clear t h a t
the properties in 2.3 could have been used as axioms. T h a t is to say, we could have t a k e n [?[--] as
a b i n a r y relation on t h e set Con, used 2.1 (i)-(ii) [?a n d] 2.3 (i)-(vi) as axioms. (Actually, 2.3(ii) is
r e d u n d a n t . ) The old-style e n t a i l m e n t relation would t h e n be definable by:

                           u~--X      iff u ~ - - { X } .

T h e previous axioms in 2.1 are t h e n easily proved from t h e new ones.                      !


      S o m e notation. As it is n o t always clear w h a t s t r u c t u r e is m e a n t if we refer to a d o m a i n
simply b y n a m i n g its u n d e r l y i n g set of d a t a objects, it will be b e t t e r if we use a letter to refer to
an i n f o r m a t i o n system as a whole. We shall therefore write:

                           A = (DA, AA, [?ConA.] , ~-A),

[?a n d] say t h a t A is an information s y s t e m - - w i t h its p a r t s as indicated. For a more informal
discussion, the n o t a t i o n w i t h o u t subscripts can suffice, b u t there can be p r o b l e m s w h e n several
different systems are involved.               |

        So m u c h for the definition of w h a t a s y s t e m is as a [?m a t h] e m a t i c a l structure. T h e n e x t question
is: W h a t is it good for? More precisely, if i n f o r m a t i o n systems are the b a c k b o n e s of d o m a i n s ,
t h e n where are the elements? T h a t is t h e topic of t h e n e x t section.


3. The elements of a system.           L e t A be an i n f o r m a t i o n system, [?a n d] suppose we already h a d a
concept of being an e l e m e n t of A. T h e d a t a objects are m e a n t to be propositions a b o u t elements,
so if X is in DA [?a n d] if x is an element, t h e n we can be expected to know w h a t it m e a n s to say
t h a t X is true of x. Since all we are given is t h e set of d a t a objects DA, we have to assume t h a t
it contains enough objects to distinguish between d i s t i n c t elements. (If t h e r e Were n o t enough of
t h e m , we would have t o change the set DA.) Formally, we can write of two elements x [?a n d] y:

          x = y iff all X E DA which are true of x are also true of y, [?a n d] conversely.

If this principle is accepted, t h e n the elements can b e identified w i t h the sets of propositions t r u e
of t h e m ; formally we can assert:

                           x = { X E PA I X is true of x}.

T h e r e c a n be no confusion injected here in identifying elements t h a t o u g h t to be distinct, since
we are a s s u m i n g t h a t t h e r e are enough d a t a objects in t h e system. If for some r e a s o n we felt we
o u g h t to have more of t h e m to d i s t i n g u i s h betwecn morc elements, t h e n we would have to pass to
a larger [?a n d] different i n f o r m a t i o n system. By agreement, then, the above e q u a t i o n is a tautology.

<!-- page 7 (pdftotext) -->

                                                    583



      So, for the sake of simplicity, elements can be taken to be sets of data objects. But, we
hasten to ask, which sets? The question is really: W h a t are the properties of truth? The answers
are well known, and, in fact, we have already used them in our examples in the last section. In
words, the set of true propositions about a possible element must be (i) consistent in itself, and
(ii) closed under entailment (or deductively closed, for short). Condition (i) is clear because we
are talking about a possible element, n o t an impossible one. Condition (ii) is acceptable, because,
by the very meaning of the word, entailment should be truth preserving. In addition, we are also
saying the converse: any set having properties (i) and (ii) corresponds to a (partial) element. Here
is the formal statement:

DEFINITION 3.1. The elements of the information system A = (DA, AA, ConA, [?k-A]) are those
subsets x of Px where:

       (i)    all finite subsets of x are in ConA; and

       (ii)   whenever u C x and u [?~--] AX, then X E x.

We write x C tAI to mean x is an element of the system. This set of elements is the domain
determined by the given system. An element that is n o t included in any strictly larger element
in the domain is called a total element; the set of total elements is denoted by TotA.  |

     Remarks. Any subset of DA satisfying 3.1 (i) can be called consistent, and every consistent set
generates an element by closing it under entailment. Note, too, t h a t every element contains AA
as a member, because the least informative proposition is true of all elements. Moreover, every
domain has a least element contained in all other elements. We call it A-A and write formally:

                      •    = {X e PAI {AX} [?~--] AX}.
In the above we could j u s t as well have used the empty set O in place of {AA}; and often we can
write simply [?[--] AX.

     The element -LA is often called the bottom element of the domainl There need be no top
or maximal element, TA. Such an element is possible if, and only if, all finite subsets of Pn are
consistent, in which case, as a set, TA ~-~ DA. The possibility is n o t excluded--rather, it is n o t
required. In case TA exists, it is the unique total element of the domain, and conversely.      |

     R e t u r n i n g to our question of the balance between axiomatizaton and construction, what
we have done is first to axiomatize the properties of (PA, AA, ConA, ~--A), then to construct
the domain ]A[ from this structure. The principal claimed advantages are that the axioms for
consistency and entailment are already essentially familiar, and that the definition of elementhood
is direct and natural from our understanding of the properties of truth.

     The ezamples. Let us look again at the three examples of information systems of the last
section. (1) In the first we see t h a t the elements, by the formal definition, are either the finite sets
{n [ n _< m} or the whole set (i.e. T). Intuitively, this corresponds to the fact that the chosen
propositions only give lower bounds on a possible element; thus, no element is "finished" until it
becomes infinite. (2) In the second example there is no top, and the elements are the sets of the
form:

                       {(n,q) ln < m < p < q},

<!-- page 8 (pdftotext) -->

                                                   584


where m _< p are given, and where q ~ ~ is allowed. The total elements here correspond to the
(non-negative) integers, and the partial e]ements to situations where the lower and upper bounds
have not come exactly together. (3) In the third example, the elements are just the graphs (i.e.
sets of ordered pairs) of partial functions from A into B (with the object A adjoined to the graph).
Total elements correspond to total functions (i.e. functions well defined on all of the set A).    II

     The reader should be able to obtain some more examples of information systems from his
own experience and should then consider w h a t the corresponding domain is like. Examples are
really quite easy to make up. Needless to say, Mathematical Logic provides a host of information
systems, but logicians do not often consider the domains determined by the the systems they know
to be worthy of study in themselves. In particular, it does not seem to be widely recognized that
the domains obtained from information systems form a rich category, as we shall show later. The
word "category" is definitely being used here in the precise technical sense of Category Theory,
and the application of the notion is very appropriate since the category of domains has very good
closure properties.


4. Domains as lattices and as topological spaces.    I will a t t e m p t to keep this section as informal
as possible especially as Sections 2 and 3 were quite formal (i.e. mathematical) enough. The
main purpose of the discussion of this section is to relate the new presentation of the Theory of
Domains to previously published ones. (Some alternatives are discussed at the end of the paper.)

     Lattice-theoretic considerations. Let A be an information system. Because the elements of
IA] are introduced as sets, these elements can be given structure from w h a t we know already
about ordinary sets. For instance, the set-theoretic inclusion relation between sets can certainly
be applied to elements. The question is: W h a t does x C y mean intuitively? In fact, we have
already mentioned this relationship before. It means t h a t every proposition (among the ones given
by the information system) true of x is also true of y (though not necessarily conversely). In other
words, x is perhaps only partially determined, while y is more fully determined in a way that
includes everything true of x. Clearly, then, if we grant the interest of partial elements, then this
relation is a natural and basic one. We often read "x ___ y " as "x approximates y".

     Now here is one of the main points of the new exposition: Because x ___ y is defined in
terms of a familiar mathematical notion, then as a relation between elements it inherits all the
well-known properties of the set-theoretical relation. It should not be necessary to write them
out, for everyone who can read this far knows t h a t C__ is in particular reflexive and transitive.
We say t h a t the domain IP/[ is a partially ordered set under inclusion. We note t h a t this (trivial)
result is proved from the definition rather than assumed as an axiom.

        Let us try out another notion. Elements are consistent, deductively closed sets of data
objects. Right? Every subset of a consistent set is consistent, but not every subset is closed under
entailment, in general. Right? But suppose t h a t x and y are two elements. It can easily be seen
t h a t their intersection x N y is again consistent and deductively closed (by a 2 nanosecond proof).
Therefore, the set of elements of a domain is closed under intersection. This means that, as a
partially ordered set, IAI is an inf semilattice.

    Well, the exact terminology is quite unimportant, but the properties of f'l when combined
with the properties of C are pleasantly "algebraic" (and run to several lines when written out).
We all know them: f3 is idempotent, commutative, and associative. The element _L, being the

<!-- page 9 (pdftotext) -->

                                                        585


smallest element of the domain, is a zero element for n.               The operation N is monotonic with
respect to C , and we have the connection:

                        x C _ y iff x N y - - - - x .

W h a t has j u s t been alluded to in words is the standard mathematical axiomatization of the
properties of an infimum (or meet) operation in a partially ordered set. (Remember, however,
to have an operation well defined within a set it is necessary also to have closure under t h a t
operation.)

    W h a t about infs of subsets? No problem. For any non-empty subfamily of IAI, it is just as
easy to prove that the set-theoretical intersection of all the elements in the subfamily is again
an element of the domain. This makes IAI a (conditionally) complete inf semilattice. Even if
you do not have any idea what I am talking about, it does not m a t t e r because the properties of
the domain are built in by the very definition; you do not have to worry at the start about their
formulation, for you can prove t h e m when you need t h e m (if ever).

     W h a t about suprema (or sups or joins)? Here there is a slight problem, because in the way
we set things up they do not always have to exist. Consider w h a t happens with just two elements
z and y. The set-theoretical union of the two elements as subsets of PA need be neither consistent
nor deductively closed; and even if x U y is consistent, it need not be closed under entailment. So
if we want sups within IAI, we cannot get by as cheaply as we can with a domain of arbitrary sets
for which the simple union is the answer.

     Let us write the sup (supposing it exists in [AI) as x [_] y. W h a t do we have when we actually
have it? By the lore of partially ordered sets, x L] y must be the least element in IA] which includes
(in the sense of C ) both x and y. Now we have just spoken about infs of families of elements:
they exist if the family is non empty. This indicates t h a t x LI y exists exactly when there is at
least one element z in IAI such that x __C z and y _ z. This turns out to be a way to say--entirely
inside I A ] - - t h a t x U y is consistent. In other words (and more generally) a sup of a subfamily
exists if, and only if, the union of the family is consistent. (And in t h a t case the sup is just
the deductive closure of the u n i o n - - t h a t is, it is generally larger t h a n the simple set-theoretical
union.) This has an axiomatic version, but it is slightly complicated by the fact t h a t sups do not
always exist. In case T A exists, then we always have all the sup% and IAI is a complete lattice.
(This is discussed in full axiomatic splendor in Gierz, et al. [1980].) But, let it hasten to be added,
not every complete lattice is isomorphic to a domain. The lattices that correspond to domains
are the so-called algebraic lattices. (See the discussion loe. cir. for the additional axiomatics
required.) W h e n the top is missing, the partially ordered structures corresponding to domains are
called conditionally complete, algebraic cpo 's.

     There is, however, an important case in IAI where the union is consistent and is, in fact, the
sup in the domain. Suppose we have a sequence of elements such t h a t

                       z0 C xl C_ z~ _ -.- C z~ _ z,,+i _            ....



As n increases, we can say that the elements x~ are getting "better and better"; thus, they must
be approaching something even more desirable in the limit. L e t
                               oo


                       Y~     U X,,
                             n=O

<!-- page 10 (pdftotext) -->

                                                    586



then there is no question t h a t y is a subset of /)A. But is it an element? Consistency, recall,
means t h a t every finite subset is in [?ConA.] The trick is that a finite subset of y m u s t be a subset
of one of the x~, because the sequence of elements z,~ is increasing. But all the terms of our given
sequence are elements, and so, consistent; therefore, every finite subset of y is consistent.

        The same argument also shows t h a t the set y of d a t a objects is closed under entailment,
because }-- A is defined as a relation between finite (consistent) sets and data objects. It follows
t h a t since each x,~ is a set closed under }---A, then so is y. In other words, y is indeed an element.
Otherwise said, the domain IAI is closed under the formation of unions of increasing chains of
elements, and the union is, of course, the sup in the sense of the partial ordering. Again we have
proved closure rather t h a n assuming it, and the necessary properties of the sup follow from its
definition as a union.

     This last argument can be generalized--as is well known to [?m a t h] e m a t i c i a n s - - t o the case
of directed families of elements. The word "directed," or better "upward-directed," means t h a t
every finite number of elements in the family is included in some further element of the family;
chains always have this property. A good example of the use of directed sets of elements figures
in the discussion of the finite elements of the domain.

    As we have remarked several times, any consistent set of d a t a objects generates an element
by closing it up under the entailment relation; thus, in particular, any set u C Con generates an
element. Let us write



for the closure of u under entailment. (This notation could be used for any consistent subset of P,
but the case of finitely generated elements is especially important.) Such a ~ is always an element
of IAI; the totality of such elements form, by definition, the finite elements of the domain. The
notation ~ should of course be decorated with a subscript A, but, as there is no good place to
write it in, we leave it out.

     We have for all elements x of the domain the basic formula:

                      x =   U{~I~ e C o n A and u g ~}.
This can be read intuitively as saying t h a t every element of the domain is the limit of its finite
approximations. And, having used the word "limit" so often, we ought now to say something
about how to make the meaning of this word correct mathematically. Note t h a t in the limit
representation for z, the union is a directed one. (Why?)


      Topological considerations. Geometrically speaking, a topological space is a collection of
"points" which group themselves in various "neighborhoods" providing thereby a sense of "near-
ness." More specifically, a neighborhood of a point in a metric space consists of all those points
within a certain positive "distance" from the given point; t h a t is, nearness is limited, but it is not
pushed to zero. The m a j o r reason for leaving some "breathing space" around the point comes
out i n defining continuity of functions.

    A function f from one topological space to another is said to be continuous provided that, for
every point x of the first space, and for every neighborhood in the second space around f(x), it is

<!-- page 11 (pdftotext) -->

                                                      587


possible to find--in the first s p a c e - - a neighborhood around x with the following property. If t h e
function is restricted to this neighborhood, then its values lie entirely in the given neighborhood
around f(x). In the metric case we can say that if we do not w a n t the function to wander any
great distance from f(x), then there is a restricted distance around x giving a neighborhood over
which the function values stay as close to f(x) as specified. This keeps the function from j u m p i n g
around wildly, since small variations in x lead to only small variations in f(x).

     The intuition about continuity is no doubt very clear in the more geometric examples, and
gometric intuition can carry us quite far. But the spaces obtained from domain theory are n o t
really geometric spaces, so we need to make some shifts in our metaphors. The geometric notion
of a point usually implies that two points are perfectly distinguishable: if x and y are different,
then they have disjoint neighborhoods. This is certainly true in the metric case, where, if two
points are different, then they are at a positive distance apart. Early on in the study of topological
spaces, however, it was found that not all spaces were metric, and weaker separation properties
of pairs of distinct points were uncovered. One of the very weak versions of such a condition is
called the "To-axiom." The best way to put it is t h a t if two points have the same neighborhoods,
then they are the same. The contrapositive s t a t e m e n t sounds odd: if two points are distinct, t h e n
there is a neighborhood t h a t contains one but not the other. The oddity of this s t a t e m e n t lies in
the feeling t h a t you cannot make up your mind over which is the better point.

     In our domains there is already a notion of "betterness" which proves to be very closely
related to the implicit neighborhood structure. The reason why our domains, as spaces of points,
are not ,'geometric" in the familiar sense is t h a t they contain partial elements. A geometric point
on the other hand is "perfect" or totally determined; it cannot be made better than it already
is. The metric in c o m m o n spaces is measuring something other than betterness, for there are
competing notions of approximation afoot here. Thus, we must keep our special goals in defining
domains clearly in mind to avoid confusion.

     Consider an information system A. For each u C ConA, we define a corresponding neighbor-
hood of tAI by the equation:
                       [u]~ = {x ~ ] A i l u C_ =}.

The neighborhoods of an element x are all those sets [u]A where u C x. Note t h a t this is the same
as saying ~ C x or ~ approximates x. Indeed, the neighborhoods are in a one-one correspondence
with the finite elements of IAI. A neighborhood collects together all those elements sharing the
same finite amount of information.

     If both u _ x and v ___ z, then it is easy to see t h a t the intersection of the two neighborhoods
is again a neighborhood of x by virtue of the formula:



In case u and v are inconsistent with each other, then the intersection will be the e m p t y set (3.
Because every element of our domain IAI is the union of the finite elements it contains, it is trivial
to prove t h a t two elements with exactly the same neighborhoods are the same. For these reasons,
then, it follows t h a t IAI is a T0-topological space. The immediate reaction to this intelligence is:
So what?

     The answer to this scepticism will appear in the best ligbt when we discuss in the n e x t section
the notion of funclion or mapping appropriate to our domains. The argument will bc based on the

<!-- page 12 (pdftotext) -->

                                                           588


extremely elementary form of the definition t h a t characterizes the general continuous function
together with the fact that the geometric intuition is suggestive of theorems to prove. In Section
6 we will find t h a t the space of all continuous functions between two given domains is also a
domain, a most useful result t h a t is interesting topologically. But further interest for Domain
Theory comes from the circumstance t h a t there is a connection between geometry and domains.
We cannot go into the full details here, b u t I can make some brief remarks.

     Before continuing t h a t discussion, though, it should be remarked t h a t once the topology of
the domain has been uncovered, then the unions of chains of elements (or directed sets of elements)
are topological limits according to accepted general definitions. Thus, what we felt intuitively
was a limiting process (the getting better and better up to the union) is in fact a limit formation
in a precise mathematical sense. This helps convince us t h a t we are on the right track.

      Total e l e m e n t s as a space. In any domain it can be proved that any element x can be extended
to a total element t, which is characterized by the property t h a t it is a m a x i m a l element of the
partial ordering. (Perhaps there are m a n y such t, b u t there is always at least one with x C t.)
Recall t h a t the set of all total elements of IAI is denoted by Totn. Because the set Torn C IAI,
it is a topological space itself. Suppose s and t are two distinct total elements, then they must
be inconsistent with each o t h e r - - b u t we shall prove more. If every finite consistent u C_ s also
satisfied u C t, then s _C t would follow. But this is impossible, because s is maximal. Let, then,
u E Con with u _C s be chosen so t h a t u _C t fails. Now u must be inconsistent with t, since
otherwise there would be an element containing t h e m both. It follows t h a t u must be inconsistent
with some v E ConA with v ___ t. In this way we show t h a t the neighborhoods [u]A and [v]A are
disjoint.

     This argument proves t h a t TotA is a H a u s d o r f f s p a c e (or T2-space). We cannot go further into
the details here, but it is also a totally disconnected, compact Hausdorff space. (These s p a c e s - -
well known from studies of Logic and the Theory of Boolean A l g e b r a s - - a r e also zero-dimensional.)
Assuming the countability of ConA, which is not such a bold assumption, all such spaces can be
conveniently embedded into the real line so as to preserve the topological structure. Perhaps this
does not seem so surprising, but it shows t h a t the topological nature of TotA, the uppermost
level of the To space [A[, is indeed quite geometric. And it can also be shown t h a t any arbitrary
continuous function on TotA into a n y topological space can be extended to a continuous function
on [A[, so the whole domain proves to be quite a "roomy" space with many good connections to
more usual topological spaces.

     A n o t e on n e i g h b o r h o o d s t r u c t u r e s . Topological spaces can be defined in several ways, and in
general they do not carry a preferred neighborhood structure. (For example,there is no topological
significance to the the usual rational intervals we use to define neighborhoods for the real line: any
similarly dense set of points would do in place of the rational numbers.) Domains, the way we have
defined them, however, do have preferred neighborhoods. The set of finite elements of IAI can
be defined topologically, and as we have seen they determine a convenient set of neighborhoods.
(The reason for all this is the so-called zero-dimensonal character of the domains. There is a
higher-dimensional theory, but this leads to continuous lattices and can only be explained using
the kind of presentation in Gierz, et al.[1980]. It is too long-winded a story for the present paper.
The higher-dimensonal domains do not have a preferred set of neighborhoods, however.)

    Having realized this, it is a short step to giving an algebraic axiomatization of the neigh-
borhood structure. Smyth [1975] contains a presentation in terms of the equivalent notion of

<!-- page 13 (pdftotext) -->

                                                                     589


 finite element. Scott [1981] t u r n s t h e story around [?a n d] defines a set-theoretical r e p r e s e n t a t i o n
 of a n e i g h b o r h o o d as j u s t a family of sets c o n t a i n i n g a largest "neighborhood" and closed u n d e r
 forlning the intersection of any two sets in t h e family t h a t contain a third~ T h e set-theoretical
 form of this definition is very simple, and Scott [1981] spells out t h e details of how the [?t h e o r y] of
 domains can be based on this s t a r t i n g point. S u b s e q u e n t investigation, however, has convinced
 t h e a u t h o r t h a t the p r e s e n t a p p r o a c h t h r o u g h i n f o r m a t i o n systems is even simpler and b e t t e r for
 a n u m b e r of t h e e s s e n t i a l constructions. T h e [?t h e o r y] introduced b y Ersov [1970] of F-spaces is
 a n o t h e r a x i o m a t i z a t i o n s o m e w h a t i n t e r m e d i a t e b e t w e e n the topological [?a n d] the lattice theoretic.
 D o m a i n s in t h e p r e s e n t sense t h e n become complete F-spaces. T h e r e are m a n y i n t e r e s t i n g aspects
 to this m e t h o d , b u t t h e a u t h o r feels t h a t i n f o r m a t i o n systems are a b o u t as e l e m e n t a r y [?a n d] familiar
 as we can get, and t h e y are therefore more suggestive of new c o n s t r u c t i o n s .


 5. A p p r o x i m a b l e m a p p i n g s between domains.               Once a general notion of set or d o m a i n h a s
 been defined [?m a t h] e m a t i c a l l y , t h e n e x t m a j o r issue is: How are the different domains to be related
 one to a n o t h e r ? T h e answer to this i m p o r t a n t question c a n m a n y times be given b y defining
 an a p p r o p r i a t e concept of mapping between domains. The answer need n o t be unique; the same
 collection of domains m a y s u p p o r t more t h a n one idea of function d e p e n d i n g on t h e special aspects
 of t h e d o m a i n s t h a t need to be b r o u g h t out. In the case of the k i n d s of domains being studied
 here, there are two principal answers, one of which is to be explained in this section.

         in order to u n d e r s t [?a n d] an a p p r o p r i a t e n o t i o n of a m a p p i n g or a function between d o m a i n s
 c o n s t r u c t e d from i n f o r m a t i o n systems, we have to refer b a c k to t h e way in which elements are
 introduced. As we have seen in Section 3, an e l e m e n t is a consistent, closed set of d a t a objects.
 To generate an element, one h a s to g e n e r a t e more [?a n d] more of the finite consistent subsets of t h e
 element. Note t h a t t h e separate d a t a objects have to be grouped into these finite consistent sets,
 because t h e e n t a i l m e n t relation m a y require a finite set of a r b i t r a r y size on the left in m a k i n g t h e
 necessary e n t a i l m e n t s for closure. It is this k i n d of passage from a finite set to its closure t h a t is
 to be generalized in defining m a p p i n g s .

          Consider two domains. To m a p from one to a n o t h e r , some i n f o r m a t i o n a b o u t a possible
  element of t h e first is presented as input to t h e f u n c t i o n f . T h e n as output the f u n c t i o n f s t a r t s
  generating an element. If the i n p u t were u, a consistent set of t h e first domain, t h e n part of
  t h e o u t p u t in the second d o m a i n m i g h t be a c o n s i s t e n t set v. We could say t h a t t h e r e is a n
  i n p u t / o u t p u t relationship set up by f , and indicate b y u f v t h a t this relation holds going from u
  in the first d o m a i n to v in the second. Of course to get the full effect of f , it is necessary to t a k e
  all the v's related to a given u, because even a small finite a m o u n t of i n p u t m a y cause an infinite
  a m o u n t of o u t p u t . B u t every e l e m e n t of a d o m a i n is j u s t t h e sum t o t a l of its finite subsets (finite
  a p p r o x i m a t i o n s ) , so it is sufficient to m a k e t h e m a p p i n g relationship go between finite sets. Here
i s t h e formal definition w i t h t h e exact conditions t h a t the relation f m u s t satisfy.

 DEFINITION 5.1. L e t A and B be two given i n f o r m a t i o n systems. An approximable m a p p i n g
 f : A --~ B is a b i n a r y relation between the two sets C o n A [?a n d] ConB such t h a t :

           (i)      0 f O;
           (ii)     u f v and u f        v' always imply u f (v U v'); and

           (iii)    ul [--h u, u f v, [?a n d] v [--n v / always imply u r f v I.

<!-- page 14 (pdftotext) -->

                                                       590



We say t h a t A is the source of f and B is the target.           !

       Intuitively the relationship u f v is an i n p u t / o u t p u t passage which can be read informally as:
 "if you are willing to give at least u arnount of information about the argument, then the mapping f
is willing to give at least v amount of information about the value (and possibly even more--if you
are patient)." Condition (i) means t h a t no (non-trivial) information about the i n p u t merits no
information about the output. Condition (ii) implies that all the contributions to the o u t p u t from
a fixed input are consistent, and in fact the union of two of the o u t p u t sets is again an o u t p u t set.
O u t p u t corresponding to a fixed input is cumulative. Condition (iii) assures us t h a t the mapping
relation f works in harmony with the two entailment r e l a t i o n s : i f a certain relationship holds,
and if the lef~-hand side is strengthened while the right-hand side is weakened, t h e n the mapping
relation must continue to hold. W h a t we must discuss next is what this means for elements.

     Before defining the notion of function value, however, it is useful to remark t h a t in the
definition of approximable mapping the form of the statement could be simplified by reducing
sets on the right to their elements. Specifically, we note the equivalence:

                        ufviffuf{Y}for           allYGv.

In other words an approximable mapping is completely determined by the relation set up between
consistent sets on the lef~ and single d a t a objects on the right.

DEFINITION 5.2. If f : A -+ B is an approximable mapping between information systems, and
if x E [A[ is an element of the first, then we define the image (or function value) of x under f by
the formula:

                        f ( x ) ---- {Y E.Pn I u f {Y} for some u _C x}.

Alternatively, we could use the equivalent formula:

                        f ( x ) --- U{v c ConB [ u f v for some u = x}.         |


      Note that, under Definition 5.2, it has to be proved that the image of an element in [A I lies in
]B I in order to justify the use of the ordinary function-value notation. But both the consistency
and the closure under entailment of f ( x ) are direct consequences of the properties in the definition
of approximable mapping.

PROPOSITION 5.3. Let f , g : A ---* B be two approximable mappings between two information
systems. Then

        (i)     f always maps elements to elements under Definition 5.2;

        (ii)    f = g    iff f ( x ) = g(z) for all x E IAI; and

        (iii)   f C g    iff f ( x ) C__g(x) for all x e ]Al.

Moreover, the approzimable mappings are monotone in the sense that

        (iv)    x _C Y in IAI always implies f ( x ) C f ( v ) in 131.

All these results follow from the observation that

<!-- page 15 (pdftotext) -->

                                                   591


        (v)    uf~       i# ~ c f ( ~ ) ,
for all u C ConA and all v E ConB.          |

      The proof is straightforward, and it completely justifies the use of the function-value notation.
Consequently, the question arises as to whether the characterization of approximable mappings
could not have been given in terms of elements in the first place. The answer is yes. Indeed,
approximable mappings correspond exactly to functions on elements preserving unions of chains
(this, in the case of countable information systems; directed unions must be used in general).
This characterization has also been called "continuity," because it is equivalent to saying that
the mappings between elements are continuous mappings in the topological sense, when IAI and
IB] are regarded as topological spaces, as explained in the last section. The reason for the word
"approximable" is explained in Section 7.

     Having justified the idea of an approximable mapping as a transformation on elements,
the next step is to combine mappings. It is hardly surprising to learn that compositions of
approximable mappings are approximable, which in mathematical terms means that the domains
together with the approximable mappings form a category. The interesting part starts when
we want to combine domains. But, to fix ideas, it is useful to spell out how compositions take
place on the level of the data objects and consistent sets. For instance, it was noted that in
any information system [?~--] is transitive on Con, and in Definition 5.1 a transitivity condition
comes in. There is a perfectly good reason for the parallelism, for, a s we see next, the first idea
(entailment) is a special case of the second (approximable mapping).

PROPOSITION 5.4. L e t A be an information system.            Then the following formula defines an
approximable mapping IA : A --+ A:

        (i)    u IA v     iff u k" x v ,

for all u, v E [?COnA.] [?A n d] we have:

        (ii)   IA(x) -----x,

for all x E [AI.     |

     In other words, the given entailment relation itself defines the identity function on the domain
in question; and of course, the identity function is an approximable mapping.

PROPOSITION 5.5. Let f : A ~ B and g : B ---* C be two approximable mappings.                Then the
following formula defines an approximable mapping g o f : A --+ C:

        (i)    u (g ~ f ) w    iff u f v and v g w for somc v E ConB,

for all u C ConA and w E Cone. [?A n d] we have:

        (ii)   (g o f)(~) = g(f(~)),

for all z E IAI.     I

      In other words, composition of input/output relations is effected by putting the input into the
first, getting, some output, and then putting that in as input to the second. The correctness of this

<!-- page 16 (pdftotext) -->

                                                        592



recipe on elements (i.e. formula 5.5(ii)) follows from the basic formula 5.3(v). Because the cla:ss of
all sets and arbitrary mappings forms a c a t e g o r y - - i n the formal meaning of the w o r d - - t h e above
three propositions show that the totality of information systems and approxi.mable mappings also
forms a category: a sub-category of the category of sets. We have given a special representation to
the category by our use of d a t a objects and consistent sets, and we have thereby put the elements
into a secondary position for a good reason. But the elements are there to use. The axioms
for a category could also be verified directly using the basic definitions like 5.4(i) and 5.5(i); the
details are bland. The more interesting topic is: w h a t are the closure conditions on our domains;
how do we construct new domains given old ones?

    Before we go on to the first basic constructs of sums and products of domains, we remark on
some other easy examples of approximable mappings: constant maps.

PROPOSITION 5.6. Given information systems A, B, C, and D, and given a fixed element b E [B[,
then there is a unique approximable mapping coast b : A --~ B such that:

        (i)     (const b)(x) --~ b,

for all x E [A[. Moreover, we have:

        (it)    f o.(const b) -----const f(b),

for all approzimable mappings f : B --+ C; and

        (iii)   (const b) o g -----coast b,

for all approzimable mappings g : D --+ A.          |

      The proof is immediate, since we need only interpret the i n p u t / o u t p u t relation u (const b) v
a s meaning v ___ b. We note that our notation is somewhat ambiguous since, for example, in
5.6(iii) we are using coast b in two senses: once as a mapping from A, and once as a mapping
from D. In fact, we should hang two subscripts on the thing to fix both the source and the target
of the mapping. This is too painful, however, and we generally rely on context to make the
meaning clear. (Formal rules of type checking can be given, so on a computer-based system all
the necessary subscripts could be put back in. Thus, the kind of ambiguity we are dealing with
here is not very serious.)


6. Products and sums of domains.          In the category of sets, the product (the cartesian product)
of two sets is by definition just the set of ordered pairs of elements. We could use the same
definition in the category of d o m a i n s - - p r o v i d e d we worked in terms of the elements of the
domains. The disadvantage is t h a t the determination of the product domain from d a t a objects is
lost, or at least pushed into the background. We shall therefore give a construction of products
directly in terms of the given d a t a objects, and then show how to prove t h a t the product is just
the one expected when w e l o o k at the elements.

     The idea for the definition is a simple one. Think of two domains A and B. A d a t a object
X C PA can be giving information about a possible element x E [A[, and a d a t a object Y E / ~
can be giving information about a possible element y C IB[. How do we wish to give information
about the pair (x, y)? The first piece of advice is not to say all t h a t is known all at once. For

<!-- page 17 (pdftotext) -->

                                                          593


example, if pressed, we can say we know X about the first coordinate of the pair; oply later,
if really pressed, we can say we also know Y about the second coordinate. The point is t h a t
data objects provide only partial information, and it does not matter if it takes several of them
to give fairly complete information about the whole element. This attitude motivates, then, the
particular form of our official definition.

DEFINITION 6.1. Let A and B be two information systems. By A X B, the product system, we
understand the system where:

        (i)     D A x B = { ( X , Aa) I X E D A } U { ( A A , Y) I Y 9

        (ii)    AAXB = (AA, AB);

        (iii)   u 9 ConA• B iff fstu 9 ConAandsndu 9 Cons;

        (iv') u ~--x•      ( X ' , A B ) iff fstu I--A X ' ; and

       (iv't) u I---A•     (AA, Y') iff s n d u [--s yt;

where, in (iii), u is any finite subset of PAXB, in (iv') and (iv"), u 9 C o n x x n , and we let:

                          fst u ---~{ X E PAI (X, A s ) E u}, and
                         s n d u = { Y E / ) B I(AA, Y ) 9     I


      Note that in 6.1(i) the two sets in the union are just two copies of PA and PB, respectively.
There is a shared member, however, the object (AA, AB) , which is indeed the least informative
data object--whether it is looked at from the point of view of A or of B. We could have used
all the pairs (X, Y), but if we did, the consistent set {(X, Y)} would be deductively equivalent to
the set {(X, AB),(AA, Y)} according to the definition of [--A•      and so there is not much point
in having this redundancy. Strictly speaking, we should not make these remarks until we have
actually verified that 6.1 is indeed a proper definition.

PROPOSITION 6.2. IrA and B are information systems, then so is A X B, and we have mappings

                         fst:A•               and s n d : A ) < B - , , B ,

such that, for approzimable mappings

                         f: C-~A      and 9 : C - - * B ,

there is one and only one approximable mappin9 (f , g) : C -* A X B such that

                         fsto(f,g)-~-f     and sndo{f,g)[?~--]-g.



Proof. Checking that 6.1 does indeed define an information system is straightforward, but there
are six things that must be proved according to Definition 2.1. We have to leave the details to the
reader. Next using the notation of 6.1, where fst and snd were applied as operations on consistent
sets u E Conn• s, we redefine matters to have approximable mappings, where, for v E ConA and
w E Cons,

<!-- page 18 (pdftotext) -->

                                                        594



        (1)    ufstv    iff f s t u t - - x v ;

        (2)    usndw      iff s n d u F - B w ; [?a n d]

        (3)    , (S, g) ~ ~ ,       f (fst.) and ~ 9 (snd~).

Because we defined A >( B so that consistency and entailment worked independently on the two
halves of the set of data objects, it is easy to check that (1)-(3) define approximable mappings
having the desired properties.

    The uniqueness of (f, g) comes out of the observation that, if z and z I are two elements of
A X B for which

                        fst(z) = fst(z') and s n d ( z ) = snd(z'),

then z = z ~. The reason is that fst and snd just divide elements into the two kinds of data
objects, and then strip off the parentheses. (Look back at Definition 6.1.) No information is lost,
so if z and z ~ are transformed into the same elements both times, then they have to be the same.

    T h a t lemma treats one pair of elements at a time, b u t (f, g) is a function. But if (f, g)' were
another function satisfying the conditions of the above proposition, then the two functions would
be pointwise equal. We could then quote 5.3 to assure ourselves t h a t they are the same function.



     Ordered pairs. By using the definition
                        (~, v) = (const(~), eonstCv))(•

which invokes 6.2 on any convenient fixed domain C, it is easy to prove that ]A >( B I is in a
one-one correspondence with the set-theoretical product of IAI and IBI. Indeed, it can be shown
that for x E IXl and y E IBI,

        (1)    ( x , y ) = { ( X , AB) I X E x } U { ( A A , Y) IYEY}EI.A. XB[;
        (2)    fst(~,v) = =;

        (3)    sndC~,v) = V;

and, for all z E IA X B],

        (4)    . = fist z, sad z).

Also, using the notation of 6.2, we can say t h a t

        (5)    (f, g)Ct) = (fit), g(t)),
for all t E ]CI.

     There are also remarks t h a t could be made about the pointwise nature of the partial ordering
of IA X B[, b u t we will not formulate them here. We do remark, however, t h a t there is also a
trivial product of no terms, 1, called the unii type or domain. It is such t h a t 1)1 = {AI}, and

<!-- page 19 (pdftotext) -->

                                                     595



that equation determines it up to isomorphism. The domain 1 has but one element, namely 11.
Note also that all approximable mappings f : 1 --~ A are constant, which shows how Definition
5.1 is a generalization of Definition 3.1. Note finally t h a t there is but one approximable mapping
f : A --* 1, namely f = 0 = c o n s t ( l l ) . !

    We turn now to the definition and properties of sums of domains.

DEFINITION 6.3. Let A and B be two information systems. By A q- B, the separated sum system,
we understand the system where, after choosing some convenient object A belonging neither to
PA nor to /)In, we have:

       (i)     D . + . = {(x, a) I x ~ p.} u {(a, Y) I Y c PB} U {(A, A)};

       (ii)    AA+B [?~--]-CA, A);

       (iii)   u E Cona+B iff either lft u E COnA and rht u -~ 0
                                or lft u ~- 0 and r h t u E ConB;

       (ivt) u }--A+B (X t, A) iff lf%u ~ 0 and lft u }--A X~;

       OC t) u ~-A+B (A, y ' ) iff rht u ?d 0 and rht u }--B Y~; and

       (iv'") u }---),+n (A, A) always holds.

where, in (iii), u is any finite subset of DA-ffB, in (iv')-(ivm), u E COnA+B, and we let:

                      tn ~ = { x e D. I ( x , a ) ~ u}, and
                      r h t u = { r C / ~ I (A,Y) E u}.          |


     The plan of the sum definition is very similar to that for product, except that (1) for reasons
to be made clear in examples, the parts do not share the least informative element (i.e. the data
objects (AA, A), (A, AB) , and (A, A) are inequivalent in this system), and (2) instead of defining
consistency and entailment in a conjunctive way, these notions are defined disjunctively. The
effect of these changes over Definition 6.1 is to produce a system A-~-B whose elements divide
into disjoint copies of those of A and B (plus an extra element I A + B ) . These remarks can be
made more precise in the following way:

PROPOSITION 6.4. I r A and B are information systems, then so is A --~ B, and we have approzim-
able mappings

                      inl: A - - + A + B   and i n r : B - - - ~ A + B ,

such that, for approximable mappings

                      f : A---~C and g : B---*C,

there is one and only one approximable mapping [f, g] : A -]- B ~ C, such that

                      [f, g] o inl = f ,   [f,g] o inr = g , and           [f,g](..t_A+B) = -I-c.

<!-- page 20 (pdftotext) -->

                                                        596


Proof. The proof that 6.3 defines a system satisfying the basic axioms of 2.1 has to be left to the
reader. Next using the notation of 6.1, where lft and rht were applied as operations on consistent
sets u E ConA+B, we redefine matters to have approximable raappings, where, for v E ConA and
W E ConB,

       (1)   v inl u iff {(X, A) [ X E v} [--x+a u;

       (2)   w inr u iff { ( A , y ) ] Y E w} I--x+a u; and
                                                                                /
       (3)   u[f,g]s    iff either ~-c s, o r l f t u # O [?a n d] l f t u f s ,
                                or rht u ~A O and rht u g s.

Because we defined A + B so that consistency and entailment worked on the two halves of the
set of data objects just as they worked on h and B, respectively, it is easy to check that (1)-(3)
define approximable mappings, and that the desired properties hold.

     The uniqueness of If, g] comes from the fact that the elements of A + B, apart from the
bottom element of the domain, are just the elements in the ranges of inl and inr. Since the
function [f, g] takes bottom to bottom (in the indicated domains), it will be uniquely determined
by what it does on the two halves of the sum. The last equations of the theorem just say that
the function is completely determined on these elements.    |

    It can also be shown that Propositions 6.2 and 6.4 uniquely characterize the domains A >( B
and A q- B up to isomorphism, and they give u s the existence of additional mappings that are
needed to show that product and sum are functors on the category of domains. We can also show
from these results that the domain

                     BOOL ~ 1 + 1

has two elements true and false, such that any mapping on BOOL is uniquely determined by its
action on true, false and /nOOL, and the values on the first two elements may be arbitrarily
chosen.


7. T h e f u n c t i o n space as a domain. Functions or mappings between domains are of basic
importance for our theory, since it is through them that we most easily transform data and relate
the structures into which the elements defined by the data objects enter. There are many possible
functions, and large groups of them can be treated in a uniform manner. For instance, ff the source
and target domains match properly, any pair of functions can be composed--composition is an
operation on functions of general significance. Now, if in the theory we could combine functions
into domains themselves, then an operation like composition might become a mapping of the
theory. Indeed, this is exactly what happens: suitably construed, composition is an approximable
mapping of two arguments. Of course, for each configuration of linked source and target domains,
there is a separate composition operation.

      In order to make approximable mappings elements of a suitable domain, we have to discover
first what their appropriate data objects are. In Section 5 this was hinted at already. To
determine an approximable mapping f : A --~ B, we have to say which pairs (u, v) with u E PA
and v E PB stand in the mapping relation u f v. One such pair gives a certain (finite) amount
of information about the possible functions that contain it, and an approximable mapping is

<!-- page 21 (pdftotext) -->

                                                            597

completely determined by such pairs. Therefore, if there are appropriate notions of consistency
and entailment for these pairs, we will be able to form a domain having functions as elements.
Let us try out a formal definition first, and then look to an explanation of how it works.

DEFINITION 7.1. Let A and B be two information systems. By A -~ B, the function space, we
understand the system where:

       (i)     PA-~B =   {(u, v) I u e ConA and . E ConB};

       (ii)    AA--,B ~ (O, O); and where,

for all n and all w = ((uo, vo),..., (u,~--l, v~--l)}, we have:

       (iii)   wEConA~u        iff w h e n e v e r l C { O , . . . , n - - 1 } [?a n d] U { u i l i E I } E C o n A ,
                                     then U{v~ [ i E I} @ Conn; and

       (iv)    ~o I--A-~B (~', v') iff U{~'~ l u' I--A ~,~} ~ B r

for all u ~ E ConA and v t E ConB.          |

      We have already explained the choice of data objects in (i) above, and the least informative
pair in (ii) is clearly right. Remember that as a d a t a object (u, v) should be read as meaning
that if the information in u is supplied as input, then at least v will be obtained as output. It
is pretty obvious that one such data object by itself is consistent (they make constant functions,
don't they?), b u t a set of several of these pairs may n o t be consistent. Hence, the need for part
(iii) of the definition. It can be read informally as follows: Look for a selection I of the indices
used in setting u p w where the ui for i E I are jointly consistent. Since the pairs in w are meant
as correct information about a single function, then the combined input from all these selected
ui must be allowable. The function will then be required to give as o u t p u t at least all the vi for
i E I, owing to the fact that we are given that w is true of the function we have in mind. As
a consequence, the set U{vi f i E I} has got to be consistent, because it comes as o u t p u t from
consistent i n p u t for a single approximable function. W h a t we are arguing for is the necessity of
(iii)--the word "consistency" should mean t h a t the d a t a objects in the set are all true of at least
one function.

     Finally we have to argue that (iv) must give the right notion of entailment for these data
objects. This can be seen by noting t h a t for a fixed consistent w the set of pairs (C, v I) satisfying
the right-hand side of (iv) defines an approximable function. In checking this we have to remark
that, for each u' E COnA, the set U(vi [ u' F-A ui} is consistent, so the definition makes sense.
The transitivity properties needed for proving t h a t we have an approximable mapping are easy
to establish. This shows in particular t h a t w is true of at least one approximable function, since
the separate pairs (ui,vi) all satisfy the definition. But it is also simple to argue t h a t for any
approximable function, if w is true of it, then so is any pair (u', v') satisfying the definition of (iv).
Consequently, what we find in (iv) is the definition of the least approximable function generated by
w. The a r g u m e n t we have just outlined thus shows t h a t the relationship w [--A-.B (C, C) means
exactly t h a t whenever w is true of an approximable m a p p i n g then so is (u ~, C). It follows at once
that [--n-~n is an entailment relation, and t h a t the elements of A -* B are just the approximable
mappings, as we indicate in the next theorem.

<!-- page 22 (pdftotext) -->

                                                      598


THEOREM 7.2. IrA, B, [?a n d] ( are information systems, then so is A --+ B, and the approximable
mappings f : A --+ B are exactly the elements f G [A ~ B[. Moreover we have an approximable
mapping apply : (B ~ C) X B ---r C such that whenever g : B --+ C and y C [B[, then

                       applYCg, Y) = gCY)-

Furthermore, for all approximable mappings h : A >( B ~ C, there is one and only one approzim.
able mapping curry h : A -+ (B --+ C) such that

                       h = apply o ((curry h) o fst, snd).




Proof. We have already remarked on the essentials of the proof above. Definition 7.1 was devised
to characterize exactly in ConA-~B the finite subsets of approximable functions, which, as binary
relations, are being regarded as sets of ordered pairs. If f : A --+ B and if w ___ f , then from the
properties of approximable functions, it can be checked directly t h a t w satisfies the right-hand
side of 7.1(iii). Conversely, if w E ConA-.B, then, as we have said, the relation which is defined
by 7.1(iv) and may be notated by:

                          = {(u', v')lw ~-A-.~ Cu',r
is an approximable mapping, as can be proved using the right-hand side of 7.1(iv) and the usual
properties of [--A and [--B. Since w __C ~ , we see t h a t w }--A-.B w r if, and only if, for all
approximable f : A --~ B, w ___ f implies w ~ _ f . (This is also the same as w I C ~ , of
course.) From these considerations it follows t h a t not only is A -+ B an information system, but
all approximable mappings are elements. Finally, if f E [A --+ B[, t h e n - - a s a binary relation - - i t
must be an approximable mapping, because the properties of Definition 5.1 axe built into 7.1.

     The construction of the special mapping apply as an approximable mapping also uses the
idea of 7.1(iv). The consistent sets of the compound space (B --* C) X B are essentially pairs of
consistent sets, say w C C o n B ~ c and u ~ E B. Now the relation we want from such pairs to
consistent sets v ~ C COnB is just nothing more or less than w [--B-~C (u ~, v~)- Our discussion in
the previous paragraph hints at why apply does in fact reproduce functional application when we
evaluate apply(g, y).

     The definition of curry h uses the same trick of regarding a binary relation with one term in
a relationship being a pair as corresponding to another relation with one coordinate of the pair
shifted to the other side. Specifically, we can think of an approximable mapping h : A X B --~ t2
as a relation from pairs (u, v) of consistent sets for A and B, respectively, over to consistent sets w
for C. W h a t we want for curry h is the relationship t h a t goes from u to the pair (v, w). Of course
(v, w) is j u s t one data object for B --+ C, but the i n p u t / o u t p u t passage from the consistent sets
of A to these objects is sufficient to determine c u r r y h as an approximable mapping. The exact
connection between the two mappings is given in terms of function values as follows:

                       hCx, y) ---- (cnr~ h)C~)Cy),
for all x E IAI and y ~ IBI. From this equation it follows t h a t curry h is uniquely determined.
But, from w h a t we know about apply, this is actually the same equation as t h a t stated at the
end of the theorem.     |

<!-- page 23 (pdftotext) -->

                                                 599


    Approximations to functions. Why have approximable functions been given this name? In
general, elements of domains are the limits of their finite approximations. We have just indicated
why the approximable mappings from one domain into another do form the elements of a domain
themselves. We have explicitly shown how to construct the finite approximable mappings O.
A closer examination of the definitions would emphasize the very constructive nature of this
analysis. It follows that the approximable mappings can therefore be approximated by simple
functions. It does not follow that all approximable mappings are simple or constructive, since
what takes place in the limiting process can be very complex. But the result does show how we
can start to make distinctions once a precise sense of approximation is uncovered.     |


      Higher-type functions and the combinators. In the above discussion we have already combined
the function-space construction with other domains by means of products. But there is nothing
now stopping us from iterating the arrow domain constructor with itself as much as we like.
This is how the so-called higher types are formed. In certain categories, such as the category of
sets, this is a non-constructive move leading to the higher cardinal numbers. In the category of
domains, however, the construct is constructive, because we have shown how to define all the
parts of A -* B in terms of very finite data objects (assuming, it need hardly be added, that A
and B are constructively given).

     Once the higher types have been formed as spaces, it must be asked what we are to do with
them. The answer is that there are many, many mappings between these spaces that can be
defined in terms of the simple notions we have been working with. These mappings are useful for
the following reason: the higher types provide remarkabe scope for modelling notions (as those
needed in denotatonal semantics for example), but the various aspects of the models have to be
related--and this is where these mappings come into play. We have already seen a preliminary
example in the last theorem, which can be interpreted as saying why the two domains shown are
isomorphic:

                    AXB-*C          ~ A - + (B--~ C).


     We have neither the time nor the space to present a full theory of higher-type operators
here, so some further examples will have to suffice. First, we have already made use of constant
mappings. Since the construction of them is very uniform, there ought to be an associated
operator. In fact, we have already been using it notationally. We have the approximable mapping
const : B --* (A -* B) that takes every element of B to the corresponding constant function. (It
has to be checked that this is an approximable mapping.) Note that there is a different mapping
for each pair of domains A and B, because the resulting types of const are different.

     As another example, take the pairing of functions explained in Proposition 6.2. We can think
of the operator in this case being

                    pair : (C -* A) X (C i-* B) -* (C --* (A X B)),

where for functions of the proper type we have:

                    pair(f, g) -----(f, g).

There will be a similar operator for the construct of Proposition 6A.

<!-- page 24 (pdftotext) -->

                                                      600


    Of course the most basic operator of function composition is also approximable of the
appropriate type. We can write:

                             comp: (B --, C) X (A --* B) ~ (A ~ C),

where for functions of the right types we have:

                             comp(q, f) = g o f,

The approximability has to be checked, of course. But once a number of the more primitive
operators have been established as being approximable, then others can be proved to be so by
writing them as combinations of previously obtained operators. II


     Categories again. All of what we have been saying about operators ties in with category
theory very nicely--as the category theorists have known for a long time. The technical term
for what we have been doing in part is cartesian closed category--that is a property of the
category of domains. Without going into details, that is essentially what 6.2 and 7.2 show of
our category. But domains have many other properties beyond being a cartesian closed category.
For example the possibility of forming sums is an extra (and useful) bonus, and there are many
others. Nevertheless, the categorical viewpoint is a good way of organizing the properties, and
it suggests other things to look for from our experiences with other categories. The next result
gives a particularly important notion that can be expressed as an operator.    |

THEOREM 7.3. Let A be an information system.                Then there is a unique operator, the least
fixed-point operator, such that

       (i)     fix: (A ~ A) ~ A; and,

for all approximable mappings f : A ~ A, we have:

       (ii)    f(fix(f)) C fix(f); and

       (iii)   for all x E IAI, if f(~) C_C_~, then fix(f) _ ~.

Moreover, for this operator, condition (ii) is an equality.

Proof.    This is a well-known result--especially the fact that the conditions above uniquely
determine the operator. The only question is the existence of the operator. The inclusion of
condition (ii) gives the hint, for fix(f) is the least solution of f ( x ) C_ x. Suppose x is any such
element, then if u _C. x and u f v hold, it follows that v __Cx. Now, since O C x always holds, ff
we wish to form the least x, we start with O and just follow it under the action of f .

       Specifically, we define fix(f) to be the union of all v E ConA for which there exist a sequence
u0, . . . , u , E ConA where:

       (1)     u0 ~ 0;

       (2)     ui f u i + l for all i < n; and

       (3)     u . ---- v.

<!-- page 25 (pdftotext) -->

                                                              601



Because f is approximable, it is clear t h a t fix f is closed under entailment. To prove that it is
consistent, suppose b o t h v and v t belong to the sets thrown into the union. We have to show t h a t
v 12 v ~ is consistent and also is thrown in. Consider the two sequences u 0 ~ . . . , u n E ConA and
uo~,..., u , / E ConA t h a t are responsible for putting v and v r in. It is without loss of generality
t h a t we assume they are of the same length, since we can always add lots of O's onto the front of
the shorter one and still satisfy (1)-(3). Now one j u s t argues by induction on i t h a t the sequence
of unions u~ LJ u / s a t i s f i e s (1)-(3) with respect to v U v'.

     But why is fix approximable? The method of proof is to replace f by ~ in (2) above, and
to use the condition t h a t there exists a sequence satisfying (1)-(3) as defining a relation between
sets w E COnA-,A and sets v E Conh. It is not difficult to prove that this is an approximable
mapping in the sense of the official definition. Clearly this relation determines fix as an operator.
|

     The result above not only proves that every approximable mapping of the form f : A --* A
has a fixed point as an element of A, but t h a t the association of the least fixed point is itself
an approximable operator. The formulation makes essential use of the partial ordering of the
domains, b u t Gordon Plotkin noticed as an exercise t h a t the characterization of the operator can
be given entirely by equations.

PROPOSITION 7.4.           The least fixed-point operator is uniquely determined by the following three
conditions:

       (i)     fix~: (A --.. A) ---. A, for all systems A;

       (ii)    fixA(f) ~- f ( f i x h ( f ) ) , . f o r all f : A ---* A.; and

       (iii)   h(fixA(f)) = fixB(g), whenever f : A --~ A, g : B -* B, h : A -+ B,
                               provided that h o f -~ g o/h and h(_kA)~-~In. |

     Remarks on the space of strict mappings. In 7.4 and many other places we have had occasion
to make use of mappings that take the bottom element of one domain over to the bottom element
of the other domain. Such mappings are called strict mappings because they take a strict view
of having empty input. As notation we might write

                         f : A --*s B
to mean t h a t f is a strict approximable mapping (i.e. f(-LX) = A_B). The totality of domains
and strict mappings forms an interesting category in itself, but it is best used in connection with
the full category of all approximable mappings.

     The collection of strict mappings forms a domain, too. The way to see this is to refer back to
Definition 7.1 and add an additional clause ruling out non-strict mappings as inconsistent. W h a t
has to be added to 7.1(iii) is the conjunct on the right-hand side to the effect t h a t if the condition
O [--A U { u i [ i E I} holds, then 0 ~-B U{vi [ i E I} holds too. By the same arguments we used
before, it follows t h a t this is the appropriate system for the domain of strict mappings. We can
denote it by (A -+s B)

     There is also a useful operator

                         s t r i c t : (A -~ B) -~ (A - * . B)

<!-- page 26 (pdftotext) -->

                                                        602


defined by the condition t h a t for f : A -~ B we have:

                     ustrict(f) v        iff     eitherO~-Bvor       O~#Auandufv,

for all u E ConA and v C ConB. This operator converts every approximable mapping into the
largest strict mapping contained within it.

     Since every strict mapping is an approximable mapping, there is also an obvious operator
going the other way. The pair of operators shows t h a t A -% B as a domain is w h a t is called a
retract of A--+ B. There is an interesting theory of this kind of relationship between domains,
but we cannot enter into it here.

   As a very small application of the use of strict mappings, we remark t h a t the following two
domains are isomorphic:

                     A X A -~- (BOOL --~ A).

The mapping from right to left is called the conditional operator, cond, and we have for all
elements x, y C IAt and t E IBOOL]

                                          /=,        if~=true,
                     eond(x, y)(t)
                                     9    IV,        if t = false.   II




8. Some domain equations.          Having outlined the theory of several domain constructs, the
final topic for this paper will be the discussion of the iteration of these constructs in giving
recursive, rather than direct definitions of domains. These recursively defined systems have often
been called "reflexive," because the domains generally contain copies of themselves as a Part of
their very structure. The way that this self-containment takes place is best expressed by the
so-called domain equations, which are really isomorphisms t h a t relate the domain as a whole
to a combination of domains--usually with the main domain as a component. This description
is rough, since recursion equations for domains can be as complex as recursion equations for
functions. We will not enter into a full theory of domain equations now but will just review
some preliminary examples to illustrate how the new presentation makes the constructions more
explicit.


     A domain of trees or S-expressions. This is everyone's favorite example. [?A n d] a very nice
example it is, but we should not think t h a t it contains all the m e a t of the theory of domain
equations. Even if we generalize the kinds of equations to contain all iterations of the domain
constructs + and X, the full power of the method has not been exploited. We will try to make
this clear in the further examples.

     Let a domain (information system) A be given. W h a t we want to construct is a domain T
of "trees" built up from elements of A as "atoms". For simplicity we consider unlabelled binary
trees here, but more complex trees are easy to accommodate. The domain equation we want to
"solve" is this one:

                    T --~ A + ( T •            T).

<!-- page 27 (pdftotext) -->

                                                603


If such a domain exists, then we can say that (up to isomorphism) the elements of the domain
T are either bottom, or elements of the given domain A, or pairs of elements from the domain T
itself. And these are the only kinds of elements that T has.

     To prove that such a domain exists it is only necessary to ask what information has to be
given about a prospective element. The answer may involve us in a regress, but the running
backwards need not be infinite--at least for the finite elements. As we shall see, the infinite
elements of T can be self-replicating; but, to define a domain fully, all we have to do is to build
up the finite elements out of the data objects in a systematic way. Fortunately, in order to satisfy
the above equation, the required closure conditions on data objects are simple to achieve.

    In the first place, we need copies of all the data objects of A to put into the sum. The easy
way to do this is to take an object A not in DA and to let, by definition,

                      AT = (A, A).
That gives us one member of PT, the one we always have to have in any case. The copy of an
X C PA is just going to be (X, A). The other members of PT will be of the form (A, U), where
U gives us information about the other kind of elements of T. The point is that T has to be a
sum, and we are using just the scheme of Definition 6.3 to set this up.

      Next we have to think what kind of information the U above should contain. Because we
want a product, we refer back to Definition 6.1 and imagine we have already defined PT. What
6.1(i) suggests is that we throw in a bunch of other data objects into PT. The only point that
needs care is that the data objects for the product must be copied into the overall sum. With this
in mind, the following clauses give us the inductive definition of PT:

       (1)    AT E PT;

       (2)    (X, A) E PT whenever X E PA; and
       (3)    (A, (y, a T ) ) E ~T, and (A, CAT, Z)) E DT whenever Y, Z E PT.

Of course,when we say "inductive definition," we mean that PT is the least class satisfying (1)-(3).
By standard arguments it can be shown that PT satisfies this set-theoretical equation:

             P~ = {AT} U {(Z, A) I Z E PA} O {CA, (Y, AT)) I Y ~ PT} O {(a, CAT, Z)) I Z E PT}.

In fact, with some very mild assumptions about ordered pairs in set theory, PT is the only solution
to the above equation.

     Defining the data objects is but part of the story: the same data objects can enter into
quite different information systems. Data objects are just "tokens" and are only given "meaning"
when Conw and ~-W are defined. Let us consider the problem of consistency first. We already
understand the notion as it applies to sum and product systems, so we must merely copy over
the parts of the previous definitions in the right position for the definition of ConT. There are
two forms we could give this definition; perhaps the best is the inductive one. We have:

       (4)    0 E ConT;

       (5)    U U {AT} C ConT whenever u E COnT;

<!-- page 28 (pdftotext) -->

                                                 604



       (6)    {(x, A) Ix c ~} ~ ConT whenever w C ConA;
       (7)    {(A, (Y, AT)) I Y E u} U {(A, (AT, Z)) I Z ~ ,} ~ Coat
                              whenever u, v G ConT.

Conditions (4)-(7) certainly make the inductive character of ConT clear--again, let us emphasize,
the set being specified is the least such. Also clear from the definition is the fact that a consistent
set of T--aside from containing A T - - i s either a copy of a consistent set of A or a copy of a
consistent set of T X T. We could thus state a set-theoretical equation for CoaT similar to the
one for PT-

     It remains to define entailment for T. Here are the inductive clauses which are pretty much
forced on us by our objective of solving the domain equation:

       (8)    u ~-T AT    always;

       (9)    U U {AT} ~--T Y whenever u ~--T Y;

       (10)   {(X, A) I X 6 w} ~-T (W, A) whenever w ~-A W;

       (11) {(A, (Y, AT)) I Y c ~} u {(A, (AT, Z))} ~--T CA,(X, AT))
                              whenever u t--T X and v G COnT; and

       (12) {(A, (r, AT)) I r ~ ~} U {(A, (AT, Z))} t--T (A, (AT,X))
                              whenever u k-T X and u 6 ConT.

Inductive definitions engender inductive proofs. It now has to be checked that consistency and
entailment for T satisfy the axioms of 2.1. The steps needed for this check are mechanical. (The
proof may be aided by noting that the cases in (4)-(7) and in (8)-(12) are disjoint---except for a
trivial overlap between (8) and (9). The cases get invoked typically by asking, when confronted
with an entailment to prove, for the nature of the data object on the right of the [?turnstile].)

     Having defined and verified that T is an information system, the validity of the domain
equation for T is secured by forming the right-hand side and noting that T is identical to A +
(T X T). The reason is that we carefully chose the notation to match the official definitions of
sums and products. (In general, in solving domain equations some transformation might have to
take place to "re-format" data objects if things are not set up to be literally the same.)

     It should be remarked that the sense can be made precise in which T is the least solution of
the given domain equation. (It is an initial algebra in a suitable category of algebras and algebra
homomorphisms.) It is pretty obvious that it is minimal in some sense, because we put into it
only what was strictly required by the problem and nothing more.

     It is also fairly obvious that there are m a n y solutions to this domain equation. A non-
constructive way to obtain non-minimal solutions is to interpret the whole construction of T in
a non-standard model of set theory. Though, in the definition of PT, it looks like we are only
working with very finite objects, everything we did could be made abstract and could be carried
out in some funny universe. The result would be a system of "finite" data objects having all
the right formal properties but containing things not in the standard minimal system. We would
then take the notions of consistency and entailment that also exist in the funny universe and

<!-- page 29 (pdftotext) -->

                                                           605


restrict t h e m to sets of data objects t h a t are actually finite in the standard sense. It can be seen
from the formal properties of the construction t h a t the resulting notions satisfy our axioms for
an information system and t h a t the domain equation h o l d s - - B U T the system w o u l d h a v e m a n y
different elements beyond what we put into the original T. To make this construction work,
by the way, we would have to force A to be absolute in the modeh if it is actually finite (say,
A = B O O L ) , then there is no problem. (Constructive methods for introducing "nonstandard"
d a t a objects can also be given.)

     Finally, we must remark on why we called T a domain of S-expressions. The answer becomes
clear when we structure T as an algebra. First, there is an approximable mapping

                          atom : A --* T,

which injects A into T making the elements of A "atoms" of T. Then there is a truth-valued
predicate on T which decides whether an element is an atom:

                          isatom : T -* B O O L .

Finally, since T X T is a part of T, we can redefine the paring functions so that:

                          pair: TX T-+T,           fst: T-+T,      and s n d : T - - * T .

In LISP terminology, these operations are the same as the familiar cons, car, and cdr. This makes
T into an algebra where, starting from atoms, e l e m e n t s - - e x p r e s s i o n s - - c a n be built up by iterated
pairing.

       But why is our system different from the usual way of regarding S-expressions? The answer
is t h a t by including partial expressions (those involving J-T) and by completing the domain
with limits, infinite expressions are introduced. For instance, if a C ITI, then we can solve the
fixed-point equation:

                          x = pair(atom(a), x),

which is an infinite list of a's. This is but one example; the possibilities have been discussed in
many papers too numerous to mention here.

     As is common to remark, S-expressions can also be thought of as trees: the parse tree t h a t
gives the grammatical form of the expression. W h a t we have added to the idea of a tree is
possibility of having infinite trees, and having all these trees as elements of a domain. |

     A domain for k-claculus. A lengthy discussion with m a n y references on X-calculus models
can be found in Longo [1982]. All we wish to remark on here is how the method of construction
by solving a domain equation can be fit into the new presentation. W h a t I have added to the
previous ideas (that in any case came out of an analysis of finite elements of models) is the general
view of information systems. In particular the models obtained this way are not lattices--hence,
the need for the calculations with Con. I hope t h a t the presentation here makes it clearer how
"pure" k-calculus models can be related to other domains having other types of s t r u c t u r e s - - f o r
instance, those needed in denotational semantics.

     The domain equation we wish to solve is:

                         D ~ A + ( D - - * V).

<!-- page 30 (pdftotext) -->

                                                    606


We proceed in much the same way we did for T, except we must now put in data objects
appropriate to the function space. Here is construction, where again A is chosen outside DA
and AD ~ (A, A):

       (2)    ZXDEPD;

       (2)    ( Z , A) E PD whenever X E PA;

       (3)    (A, (u, v)) e PD whenever u, v E COUD;

       (4)    0 E toaD;

       (5)    U U {AD} ~ ConD whenever u E ConD;

       (6)    {(x, n) I x E ~} E Coup whenever w C ConA; and

       (7)    {( A, (u0, v0)),..., (A, (u,~--l, v ~ - l ) ) } E COnD provided ui, v~ e ConD
              for all i < n and whenever I _ { 0 , . . . , n - - 2} and U{u, 1 i E I} E COnD,
              then U{vi [ i C I} E C0nD.

W h a t is different here from the definition of T is the fact that the concepts DD and ConD are
mutually recursive because the data objects are themselves buill; from consistent sets. The scheme
is based on a combination of the sum construct and the function-space construct, b u t the mutual
recursion allows "feedback" to occur.

    To complete the definition we have to give the clauses for the inductive definition of entail-
meat. They are:

       (8)    U ['--DAD    always;

       (9)    u U {AD} }---DY whenever u }---DY;

       (10)   {(X, A) IX E w} }---D(W, A) whenever w [ - A W;

       (12) {Ca, (~0, v0)) .... , Ca, ( ~ - 1 , v~-l))} ~ . (~, (~', v))
              whenever U{vd ] u' }--Dud} }---DV' and the set on the left is in COnD.

Obviously these definitions are much shorter if we have a domain in which all sets are consistent,
but there are many reasons for retaining the consistency concept throughout. The check that D
is an information system and satisfies the domain equation is mechanical. We cannot detail here
how this construction provides a X-calculus model.

     It is clear that these definitions are constructive, and that, with a suitable Ghdel numbering
of the data objects, the predicates for consistency and entailment are recursively enumerable,
However, the recursioa used builds up the predicates by going from less complicated data objects
to more complicated ones; therefore, the predicates must be recursive, because, for a certain size
data object, the derivation that puts it into the predicate is of a bounded length. This observation
helps in the discussion of the computability of the operators defined on these domains--another
topic we cannot discuss here.       I

<!-- page 31 (pdftotext) -->

                                                     607


    A universal domain. As a final example of building up domains recursively, we give a
construction of a "universal" domain U. (The reason for the name will be explained presently.)
The best way to define U seems to be to define a domain V with a top element first,and then to
remove the top.

     The recursion for V is remarkably simple. We begin with two distinct objects A and ~7 that
give information about the top and bottom of V, respectively. Thus, Av ~ A by definition. We
assume that these two special data objects are "atomic" in the sense that they axe not equal to
any ordered pair of Objects. For-the definition of Pv we have these clauses:

       (1)    A, V E /)v;

       (2)    ( x , a) E Pv and (/~,Y) e Pv whenever x , Y e pv.

In other words, we begin with two objects and close up under two flavors of copies of these objects.
(A product result is involved here, so that is the reason for structuring the flavors the way we
have.)

   For V all subsets of Pv are consistent, so all we have left is to define entailment for this
domain. The clauses are:

       (3)    u [--v A   always;

       (4)    u F-v ~7 whenever either V E u or {X I (X, A) E u} I--v ~7
                            and {Y I (A, y ) E u} [--v V;

       (5)    u }--v (X', A) whenever either V E u or {X [ (X, A) E u} }--v X'; and

       (6)    u t--v ( A , y ' ) whenever either V E u or {Y ](A, Y) E u} [--v Y'.

     The proof that V is an information system proceeds as before. Note that, under the above
definition of entailment, the data objects A, (A, A), ((A, A), A), etc. are all equivalent. There is,
however, no other data object equivalent to ~7. The domain equation satisfied by V is:

                       V~V•

Of course, there are an unlimited number of solutions to this equation, so the fact that V satisfies
it tells us very little.

    Because V entails everything, we can regard it as a "rogue" object that ought to be banned
from polite company: the only element of V it gives any information about is the top ele-
ment, which is as unhelpful as any element could be. We should simply throw it out as being
"inconsistent." What remains is the domain U. Formally we have:

       (v)    P~ = P v - (v};

       (8)    A . = av;

       (9)    Con. = {~ C P~ I ~ finite and u ~ v V}; and

       (10)   ut-'uY     iff u E C o n u , Y C P u   and u [ - - v Y .

<!-- page 32 (pdftotext) -->

                                                    608


The same style of definition would work in any situation when an information system has a rogue
data object that entails everything: there always is a system that results from eliminating all
those objects that entail .everything. Indeed, we could have always included such an object in any
domain and altered the definition to take as elements those deductively closed sets of data objects
that do not have the rogue object as a member. We did n o t do this for the reason that superfluous
elements cause lots of exceptions in constructs such as product, where there is a temptation to
let them enter into various combinations.

     Now in U we do allow V to enter into combinations--and this is part of the secret of the
construction. The consequence is, however, that the domain equation which U satisfies is not too
easy to state since it involves an unfamiliar functor. So it is not through such equations that we
will understand its nature in a direct way. But it is possible to explain how it works by reference
to the steps in the construction.

     Imagine the full (infinite) binary tree. The data objects of U are giving information about
possible paths in the tree. We think to the tree starting at the root node at the top of the page
and growing down. The object A gives no information--so no paths are excluded. (ff we would
have allowed V, then the information it would have been giving is that all paths are excluded.)
The data object ( X , A ) tells us about a path that either it is unrestricted on the right half of
the tree, or on the left, when we start at the node directly below the root, the paths that are
excluded from the subtree axe those excluded according to X . This makes sense because the
subtrees of the binary tree look exactly like the whole tree, so information can be relativized or
translated to other positions. With ( A , y ) the rSles of right and left are interchanged. We could
have introduced data objects of the form (X, Y) which tell us information about both halves of
the tree at the same time, but the consistent set {(X, A), ( A , y ) } does the same job. In general
consistent sets should be thought of as conjunctions; while, in this example, the comma in the
ordered pair should be thought of as a disjunction ~hen "reading" information objects.

     We can now see that a single data object (if it contains •) looks down the tree along a finite
path to some depth and then excludes the rest of the tree below that node. A consistent set of
data objects leaves at least one hole, so at least one path is not excluded. The maximal consistent
sets of information objects are those giving true information about one single (infinite) p a t h - - t h e
total elements of the domain U correspond exactly to the infinite paths in the binary tree. The
partial elements are harder to describe geometrically, however. In accumulating information into
a consistent set, holes can be left all over the tree. A partial object is therefore of an indeterminate
character, since the "path" we are describing might sneak through any one of the holes. (There
is, by the way, a precise topological explanation of what is happening. The total elements of U
form a well-known topological space, the so-called Cantor space, and the partially ordered set of
elements of U is isomorphic to the lattice of open sets of the space--save that the whole space is
not allowed.)

     This is all very well, but what, we ask, is the good of this domain, and why is it called
"universal". The proof cannot be given here, but the result is as follows. As a consequence of
standard facts about countable Boolean algebras, it can be proved that every "countably based"
domain is a subdomain of U. More specifically, if A is an information system, and if PA is
countable, then there exists a pair of approximable mappings

                      a: A-~U      and b: U - - ~ A ,

<!-- page 33 (pdftotext) -->

                                                     609


such t h a t

                         boa~---IA and a o b C     Iu.

This makes A a special kind of retract of U: T h e mappings a and b are far from'unique, but at
least there is one way to give a one-one embedding of the elements of A into the elements of U.

       The universal property of U can be applied quite widely. For example, since (U --* U) is a
system with only countably many data objects (by explicit construction!), this system is a retract
of U. Fixing on one such retraction pair as above, makes U also into a model of the X-calculus.
W h e t h e r different retractions give essentially different models I do n o t know. But the point of the
remark is to show t h a t domains can contain their own function spaces for a variety of interesting
reasons.        |


     A domain of domains. Not many details can be presented here, but we would also like to
remark t h a t even domains can be made into a domain. One way of getting an idea of how this is
possible is to note t h a t since subdomains of U correspond to certain kinds of functions on U, and
since the function space of U is also a subdomain of U, it might be suspected t h a t the subdomains
of U form a single subdomain of U.

      T h a t is a fairly sophisticated way of reaching the conclusion (and m a n y details have to be
worked out). A more elementary approach would be just to s               w h a t it means to give a finite
amount of information about a domain. For the sake of uniformity, suppose that the d a t a objects
of the possible domain are drawn from the non-negative integers, and t h a t we conventionally use
0 for •. T h e n to give a finite amount of information about a domain i s - - r o u g h l y - - t o specify a
finite part of Con and a finite part of F - . To make the formulation easier, we wilt reserve for 1 a
r61e like the one recently played by V. W h a t the specifications will boil down to is pairs (u, v) of
finite sets of integers used as d a t a objects to convey one piece of information about an entailment
relation.

        But hold, entailment relations are very closely connected to approximable mappings. Indeed,
we remarked before t h a t the identity function as an approximable mapping on a domain is j u s t
represented as the underlying entailment relation itself. Suppose we take as our domain the
domain of all sets of integers. It is a powerset, so call it P. T h a t is to say, the integers are the
d a t a objects, all finite sets are consistent, and the entailment relation is the minimal possible one.
(As far as elements go, an arbitrary set of integers is equal to the union of all its finite subsets,
which means t h a t the elements of the domain are in a one-one correspondence with the arbitrary
sets of integers.) The question is: which approximable mappings on P into itself correspond to
entailment relations on the integers as d a t a objects?

     The answer can be expressed most succinctly using our standard notation. If we think of
r : P --* P as a relation between finite sets in the usual way, then to say t h a t r is reflexive is to
say:

         (1)   Ip C r.

To say t h a t r is transitive is to say:

         (2)   r o r = r.

<!-- page 34 (pdftotext) -->

                                                610


To say that for r the object 0 plays at being A is to say:

       (3)   ~c_r(•
where in general ~ is short for {n} in the domain P. Then, to say that 1 plays at being a rogue
object is to say:

       (4)   T=r(i).

Finally, to say that 1 is an inconsistent object that has to be excluded is to say:

       (5)   i ~ r(~).
     That's it. The collection of approximable mappings satisfying (1)-(5) gives us all the entail-
ment relations we need. Condition (5) is a consistency condition, and for r the consistent finite
sets u are those such that i ~ r(~). What we are asserting is that the totality of r satisfying
(1)-(5) forms the elements of a domain--one that has been derived from (P -* P) in a way similar
to the way we derived U from V above.

    Having made domains into a domain, the next step is to see how constructs on domain
(i.e. functors) can be made into approximable mappings. But the retelling and development of
that story will have to wait for another publication along with the very interesting chapter on
powerdomains. I only hope the ground covered here makes the theory of domains seem more
elementary and more natural.     |
