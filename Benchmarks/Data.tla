-------------------------------- MODULE Data --------------------------------
(***************************************************************************)
(* This module contains basic operators shared by the specifications of    *)
(* the deconstructed and the distributed Bakery algorithms.                *)
(***************************************************************************)
EXTENDS Integers, TLAPS

(***************************************************************************)
(* Lexicographic ordering on pairs of integers.                            *)
(***************************************************************************)
q \ll r == \/ q[1] < r[1]
           \/ /\ q[1] = r[1]
              /\ q[2] < r[2]

Max(i,j) == IF i >= j THEN i ELSE j

\* pseudo-value represented as an inverted question mark in the paper
qm  == CHOOSE v : v \notin Nat

CONSTANT N
ASSUME NAssump == N \in Nat \ {0}

(***************************************************************************)
(* Processes and their identities.                                         *)
(***************************************************************************)
Procs == 1..N
OtherProcs(i) == Procs \ {i}
ProcIds == {<<i>> : i \in Procs}
SubProcs == {p \in Procs \X Procs : p[1] # p[2]}
SubProcsOf(i) == {p \in SubProcs : p[1] = i} 
WrProcs == {w \in Procs \X Procs \X {"wr"} : w[1] # w[2]}
MsgProcs == {w \in Procs \X Procs \X {"msg"} : w[1] # w[2]}

(***************************************************************************)
(* Utility lemmas used in the TLAPS proofs.                                *)
(***************************************************************************)
LEMMA qmNotNat == qm \notin Nat
BY NoSetContainsEverything DEF qm

LEMMA TotalOrder ==
  ASSUME NEW i \in Procs, NEW wi \in Nat, 
         NEW j \in Procs \ {i}, NEW wj \in Nat
  PROVE  <<wi, i>> \ll <<wj, j>> \/ <<wj, j>> \ll <<wi, i>>
BY DEF \ll, Procs

LEMMA AsymmetricOrder ==
  ASSUME NEW i \in Procs, NEW wi \in Nat,
         NEW j \in Procs, NEW wj \in Nat
  PROVE  ~ (<<wi, i>> \ll <<wj, j>> /\ <<wj, j>> \ll <<wi, i>>)
BY DEF \ll, Procs

(***************************************************************************)
(* The provers have a hard time with the process identifiers, and we help  *)
(* them by proving utility lemmas.                                         *)
(***************************************************************************)
LEMMA DisjointIds ==
  /\ ProcIds \cap SubProcs = {}
  /\ ProcIds \cap WrProcs = {}
  /\ ProcIds \cap MsgProcs = {}
  /\ SubProcs \cap WrProcs = {}
  /\ SubProcs \cap MsgProcs = {}
  /\ WrProcs \cap MsgProcs = {}
BY DEF ProcIds, SubProcs, WrProcs, MsgProcs

LEMMA ProcId ==
  ASSUME NEW i \in Procs
  PROVE  /\ <<i>> \in ProcIds
         /\ <<i>> \notin SubProcs
         /\ <<i>> \notin WrProcs
         /\ <<i>> \notin MsgProcs
BY DEF ProcIds, SubProcs, WrProcs, MsgProcs

LEMMA SubProcId ==
  ASSUME NEW i \in Procs, NEW j \in OtherProcs(i)
  PROVE  /\ <<i,j>> \in SubProcs
         /\ <<i,j>> \notin ProcIds
         /\ <<i,j>> \notin WrProcs
         /\ <<i,j>> \notin MsgProcs
         /\ <<i,j,"wr">> \in WrProcs
         /\ <<i,j,"wr">> \notin ProcIds
         /\ <<i,j,"wr">> \notin SubProcs
         /\ <<i,j,"wr">> \notin MsgProcs
         /\ <<i,j,"msg">> \in MsgProcs
         /\ <<i,j,"msg">> \notin ProcIds
         /\ <<i,j,"msg">> \notin SubProcs
         /\ <<i,j,"msg">> \notin WrProcs
BY DEF ProcIds, SubProcs, WrProcs, MsgProcs, OtherProcs

LEMMA SubProcsOfEquality ==
  ASSUME NEW p \in Procs
  PROVE  SubProcsOf(p) = { <<p,q>> : q \in OtherProcs(p) }
BY DEF SubProcsOf, SubProcs, OtherProcs

(***************************************************************************)
(* Several variables represent functions of the (informal) type            *)
(*                                                                         *)
(*   [ i \in Procs -> [ OtherProcs(i) -> S ] ]                             *)
(*                                                                         *)
(* We write this as POP(S) and provide some utility lemmas below.          *)
(***************************************************************************)
PFunc(X,Y) ==
  \* partial functions from X to Y
  UNION {[XX -> Y] : XX \in SUBSET X}

POP(S) ==
  \* set of functions [i \in Procs -> [OtherProcs(i) -> S]]
  {f \in [Procs -> PFunc(Procs,S)] :
     \A i \in Procs : DOMAIN f[i] = OtherProcs(i)}

LEMMA POP_construct ==
  ASSUME NEW S, NEW s(_,_), 
         \A p \in Procs : \A q \in OtherProcs(p) : s(p,q) \in S
  PROVE  [p \in Procs |-> [q \in OtherProcs(p) |-> s(p,q)]] \in POP(S)
<1>. DEFINE f(p) == [q \in OtherProcs(p) |-> s(p,q)]
<1>1. ASSUME NEW p \in Procs
      PROVE  /\ f(p) \in PFunc(Procs, S)
             /\ DOMAIN f(p) = OtherProcs(p)
  <2>. OtherProcs(p) \in SUBSET Procs
    BY DEF OtherProcs
  <2>. QED  BY DEF PFunc
<1>. QED  BY <1>1, Zenon DEF POP

LEMMA POP_access ==
  ASSUME NEW S, NEW f \in POP(S),
         NEW p \in Procs, NEW q \in OtherProcs(p)
  PROVE  f[p][q] \in S
BY DEF POP, PFunc

LEMMA POP_except ==
  ASSUME NEW S, NEW f \in POP(S),
         NEW p \in Procs, NEW q \in OtherProcs(p), NEW s \in S 
  PROVE  /\ [f EXCEPT ![p][q] = s] \in POP(S)
         /\ [f EXCEPT ![p][q] = s][p][q] = s
         /\ \A pp \in Procs : \A qq \in OtherProcs(pp) :
               pp # p \/ qq # q => [f EXCEPT ![p][q] = s][pp][qq] = f[pp][qq]
BY DEF POP, PFunc, OtherProcs

\* NB: Combining the two following lemmas breaks proofs.
LEMMA POP_except_fun_type ==
  ASSUME NEW S, NEW f \in POP(S), NEW p \in Procs, 
         NEW g(_,_), \A q \in OtherProcs(p) : g(p,q) \in S
  PROVE  [f EXCEPT ![p] = [q \in OtherProcs(p) |-> g(p,q)]] \in POP(S)
BY DEF POP, PFunc, OtherProcs

LEMMA POP_except_fun_value ==
  ASSUME NEW S, NEW f \in POP(S), NEW p \in Procs, 
         NEW g(_,_), \A q \in OtherProcs(p) : g(p,q) \in S
  PROVE  LET ff == [f EXCEPT ![p] = [q \in OtherProcs(p) |-> g(p,q)]]
         IN  /\ \A q \in OtherProcs(p) : ff[p][q] = g(p,q) 
             /\ \A pp \in Procs \ {p} : \A qq \in OtherProcs(pp) : ff[pp][qq] = f[pp][qq]
BY DEF POP, PFunc, OtherProcs

LEMMA POP_except_equal ==
  ASSUME NEW i \in Procs, NEW j \in OtherProcs(i), 
         NEW S, NEW f \in POP(S), NEW g \in POP(S), NEW x \in S,
         \A k \in Procs : \A l \in OtherProcs(k) :
            g[k][l] = IF k=i /\ l=j THEN x ELSE f[k][l]
  PROVE  g = [f EXCEPT ![i][j] = x]
BY DEF POP, PFunc


=============================================================================
\* Modification History
\* Last modified Tue Nov 16 19:50:05 CET 2021 by merz
\* Created Mon Sep 06 18:41:47 CEST 2021 by merz
