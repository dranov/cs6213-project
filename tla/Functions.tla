------------------------------ MODULE Functions -----------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Notions about functions including injection, surjection, and bijection.*)
(*  Originally contributed by Tom Rodeheffer, MSR.                         *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)


(***************************************************************************)
(* Restriction of a function to a set (should be a subset of the domain).  *)
(***************************************************************************)
\* @type: (a -> b, Set(a)) => (a -> b);
Restrict(f,S) == [ x \in S |-> f[x] ]

(***************************************************************************)
(* Range of a function.                                                    *)
(* Note: The image of a set under function f can be defined as             *)
(*       Range(Restrict(f,S)).                                             *)
(***************************************************************************)
\* @type: (a -> b) => Set(a);
Range(f) == { f[x] : x \in DOMAIN f }


(***************************************************************************)
(* The inverse of a function.                                              *)
(***************************************************************************)
\* @type: (a -> b, Set(a), Set(b)) => (b -> a);
Inverse(f,S,T) == [t \in T |-> CHOOSE s \in S : t \in Range(f) => f[s] = t]


(***************************************************************************)
(* A function is injective iff it maps each element in its domain to a     *)
(* distinct element.                                                       *)
(*                                                                         *)
(* This definition is overridden by TLC in the Java class SequencesExt.    *)
(* The operator is overridden by the Java method with the same name.       *)
(***************************************************************************)
\* @type: (a -> b) => Bool;
IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

(***************************************************************************)
(* Set of injections between two sets.                                     *)
(***************************************************************************)
\* @type: (Set(a), Set(b)) => (Set(a -> b));
Injection(S,T) == { M \in [S -> T] : IsInjective(M) }


(***************************************************************************)
(* A map is a surjection iff for each element in the range there is some   *)
(* element in the domain that maps to it.                                  *)
(***************************************************************************)
\* @type: (Set(a), Set(b)) => (Set(a -> b));
Surjection(S,T) == { M \in [S -> T] : \A t \in T : \E s \in S : M[s] = t }


(***************************************************************************)
(* A map is a bijection iff it is both an injection and a surjection.      *)
(***************************************************************************)
\* @type: (Set(a), Set(b)) => (Set(a -> b));
Bijection(S,T) == Injection(S,T) \cap Surjection(S,T)


(***************************************************************************)
(* An injection, surjection, or bijection exists if the corresponding set  *)
(* is nonempty.                                                            *)
(***************************************************************************)
ExistsInjection(S,T)  == Injection(S,T) # {}
ExistsSurjection(S,T) == Surjection(S,T) # {}
ExistsBijection(S,T)  == Bijection(S,T) # {}


=============================================================================
\* Modification History
\* Last modified Sun Dec 27 09:38:06 CET 2020 by merz
\* Last modified Wed Jun 05 12:14:19 CEST 2013 by bhargav
\* Last modified Fri May 03 12:55:35 PDT 2013 by tomr
\* Created Thu Apr 11 10:30:48 PDT 2013 by tomr
