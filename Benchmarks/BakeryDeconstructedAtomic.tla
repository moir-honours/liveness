--------------------- MODULE BakeryDeconstructedAtomic ----------------------
(***************************************************************************)
(* This is the PlusCal specification of the deconstructed bakery algorithm *)
(* in the paper                                                            *)
(*                                                                         *)
(*    Deconstructing the Bakery to Build a Distributed State Machine       *)
(*                                                                         *)
(* There is one simplification that has been made in the PlusCal version:  *)
(* the registers localCh[i][j] have been made atomic, a read or write      *)
(* being a single atomic action.  This doesn't affect the derivation of    *)
(* the distributed bakery algorithm from the deconstructed algorithm,      *)
(* which also makes the simplifying assumption those registers are atomic  *)
(* because they disappear from the final algorithm.                        *)
(*                                                                         *)
(* Here are some of the changes made to the paper's notation to conform to *)
(* PlusCal/TLA+.  Tuples are enclosed in << >>, so we write <<i, j>>       *)
(* instead of (i,j).  There's no upside down "?" symbol in TLA+, so that's *)
(* replaced by the identifier qm.                                          *)
(*                                                                         *)
(* The pseudo-code for main process i has two places in which subprocesses *)
(* (i, j) are forked and process i resumes execution when they complete.   *)
(* PlusCal doesn't have subprocesses.  This is represented in PlusCal by   *)
(* having a single process <<i, j>> executing concurrently with process i, *)
(* synchronizing appropriately using the variable pc.                      *)
(*                                                                         *)
(* Here is the basic idea:                                                 *)
(*                                                                         *)
(*   This pseudo-code for process i:                       `.              *)
(*        main code ;                                                      *)
(*        process j # i \in S                                              *)
(*          s1: subprocess code                                            *)
(*        end process                                                      *)
(*        p2: more main code                               .'              *)
(*                                                                         *)
(*   is expressed in PlusCal as follows:                                   *)
(*                                                                         *)
(*      In process i                                      `.               *)
(*            main code ;                                                  *)
(*        p2: await \A j # i : pc[<<i,j>>] = "s2"                          *)
(*            more main code                                 .'            *)
(*                                                                         *)
(*      In process <<i,j>>                                   `.            *)
(*        s1: await pc[i] = "p2"                                           *)
(*            subprocess code ;                                            *)
(*        s2: ...                                            .'            *)
(*                                                                         *)
(* Also, processes have identifiers and, for reasons that are not          *)
(* important here, we can't use i as the identifier for process i, so we   *)
(* use <<i>>.  So, pc[i] in the example above should be pc[<<i>>].  In the *)
(* pseudo-code, process i also launches asynchronous processes (i, j) to   *)
(* set localNum[j][i] to 0.  In the code, these are another set of         *)
(* processes with ids <<i, j, "wr">>.                                      *)
(*                                                                         *)
(* We could simplify this algorithm by not waiting for localNum[j][i] to   *)
(* equal 0 in subprocess <<i,j>> and having the asynchronous write of 0    *)
(* not do anything if process i has begun the write to localCh[i][j] that  *)
(* sets its value to number[i].  However, I think I like the algorithm in  *)
(* the paper the way it is because it makes the pseudo-code more           *)
(* self-contained.                                                         *)
(*                                                                         *)
(* Like the pseudo-code shown in the paper, this version of the algorithm  *)
(* represents the M action as an atomic step.                              *)
(***************************************************************************)

EXTENDS Data

(**************************************************************************
--algorithm Decon {
  variables number = [p \in Procs |-> 0], 
            localNum = [p \in Procs |-> [q \in OtherProcs(p) |-> 0]] ,
            localCh  = [p \in Procs |-> [q \in OtherProcs(p) |-> 0]] ; 
  
  fair process (main \in ProcIds) 
  {
   ncs:- while (TRUE) {
            skip ; (* noncritical section *)
         M: await \A p \in SubProcsOf(self[1]) : pc[p] = "test" ;
            with (v \in {n \in Nat \ {0} : \A j \in OtherProcs(self[1]) :
                           localNum[self[1]][j] # qm => n > localNum[self[1]][j]}) {
               number[self[1]] := v;
               localNum := [j \in Procs |-> 
                             [i \in OtherProcs(j) |-> 
                                IF i = self[1] THEN qm 
                                               ELSE localNum[j][i]]];
            } ;
         L: await \A p \in SubProcsOf(self[1]) : pc[p] = "ch" ;
        cs: skip ; (* critical section *)
         P: number[self[1]] := 0 ;
            localNum := [j \in Procs |->
                          [i \in OtherProcs(j) |->
                             IF i = self[1] THEN qm
                                            ELSE localNum[j][i]]];
          }
  }

  fair process (sub \in SubProcs) {
    ch: while (TRUE) {
           await pc[<<self[1]>>] = "M" ;
           localCh[self[2]][self[1]] := 1 ;
    test:  await pc[<<self[1]>>] = "L" ;
           localNum[self[2]][self[1]] := number[self[1]] ;
      Lb:  localCh[self[2]][self[1]] := 0 ;
      L2:  await localCh[self[1]][self[2]] = 0 ;
      L3:- (* See below for an explanation of why there is no fairness here. *)
           await (localNum[self[1]][self[2]] \notin {0, qm}) => 
                  (<<number[self[1]], self[1]>> \ll 
                      <<localNum[self[1]][self[2]], self[2]>>) 
                  (* The await condition is written in the form
                     A => B rather than A \/ B because when TLC is finding   
                     new states, when evaluating A \/ B it evaluates B
                     even when A is true, and in this case that would 
                     produce an error if localNum[self[1]][self[2]] equals qm.  *)
        }
  }
  
  (* We allow process <<i,j,"wr">> to set localNum[j][i] to 0 only if it has
     not already been set to qm by process <<i>> in action M0.  We could
     also allow it to write 0 after that write of qm but before 
     process <<i,j>> executes statement test.  Such a write just
     decreases the possible executions, so eliminating this possibility
     doesn't forbid any possible executions.                            *)
  fair process (wrp \in WrProcs) {
    wr: while (TRUE) {
          await /\ localNum[self[2]][self[1]] = qm
                /\ pc[<<self[1]>>] \in {"ncs", "M"} ;
          localNum[self[2]][self[1]] := 0 ;
        }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "7827c38d" /\ chksum(tla) = "83cb6c12")
VARIABLES number, localNum, localCh, pc

vars == << number, localNum, localCh, pc >>

ProcSet == (ProcIds) \cup (SubProcs) \cup (WrProcs)

Init == (* Global variables *)
        /\ number = [p \in Procs |-> 0]
        /\ localNum = [p \in Procs |-> [q \in OtherProcs(p) |-> 0]]
        /\ localCh = [p \in Procs |-> [q \in OtherProcs(p) |-> 0]]
        /\ pc = [self \in ProcSet |-> CASE self \in ProcIds -> "ncs"
                                        [] self \in SubProcs -> "ch"
                                        [] self \in WrProcs -> "wr"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "M"]
             /\ UNCHANGED << number, localNum, localCh >>

M(self) == /\ pc[self] = "M"
           /\ \A p \in SubProcsOf(self[1]) : pc[p] = "test"
           /\ \E v \in {n \in Nat \ {0} : \A j \in OtherProcs(self[1]) :
                          localNum[self[1]][j] # qm => n > localNum[self[1]][j]}:
                /\ number' = [number EXCEPT ![self[1]] = v]
                /\ localNum' = [j \in Procs |->
                                 [i \in OtherProcs(j) |->
                                    IF i = self[1] THEN qm
                                                   ELSE localNum[j][i]]]
           /\ pc' = [pc EXCEPT ![self] = "L"]
           /\ UNCHANGED localCh

L(self) == /\ pc[self] = "L"
           /\ \A p \in SubProcsOf(self[1]) : pc[p] = "ch"
           /\ pc' = [pc EXCEPT ![self] = "cs"]
           /\ UNCHANGED << number, localNum, localCh >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P"]
            /\ UNCHANGED << number, localNum, localCh >>

P(self) == /\ pc[self] = "P"
           /\ number' = [number EXCEPT ![self[1]] = 0]
           /\ localNum' = [j \in Procs |->
                            [i \in OtherProcs(j) |->
                               IF i = self[1] THEN qm
                                              ELSE localNum[j][i]]]
           /\ pc' = [pc EXCEPT ![self] = "ncs"]
           /\ UNCHANGED localCh

main(self) == ncs(self) \/ M(self) \/ L(self) \/ cs(self) \/ P(self)

ch(self) == /\ pc[self] = "ch"
            /\ pc[<<self[1]>>] = "M"
            /\ localCh' = [localCh EXCEPT ![self[2]][self[1]] = 1]
            /\ pc' = [pc EXCEPT ![self] = "test"]
            /\ UNCHANGED << number, localNum >>

test(self) == /\ pc[self] = "test"
              /\ pc[<<self[1]>>] = "L"
              /\ localNum' = [localNum EXCEPT ![self[2]][self[1]] = number[self[1]]]
              /\ pc' = [pc EXCEPT ![self] = "Lb"]
              /\ UNCHANGED << number, localCh >>

Lb(self) == /\ pc[self] = "Lb"
            /\ localCh' = [localCh EXCEPT ![self[2]][self[1]] = 0]
            /\ pc' = [pc EXCEPT ![self] = "L2"]
            /\ UNCHANGED << number, localNum >>

L2(self) == /\ pc[self] = "L2"
            /\ localCh[self[1]][self[2]] = 0
            /\ pc' = [pc EXCEPT ![self] = "L3"]
            /\ UNCHANGED << number, localNum, localCh >>

L3(self) == /\ pc[self] = "L3"
            /\ (localNum[self[1]][self[2]] \notin {0, qm}) =>
                (<<number[self[1]], self[1]>> \ll
                    <<localNum[self[1]][self[2]], self[2]>>)
            /\ pc' = [pc EXCEPT ![self] = "ch"]
            /\ UNCHANGED << number, localNum, localCh >>

sub(self) == ch(self) \/ test(self) \/ Lb(self) \/ L2(self) \/ L3(self)

wr(self) == /\ pc[self] = "wr"
            /\ /\ localNum[self[2]][self[1]] = qm
               /\ pc[<<self[1]>>] \in {"ncs", "M"          }
            /\ localNum' = [localNum EXCEPT ![self[2]][self[1]] = 0]
            /\ pc' = [pc EXCEPT ![self] = "wr"]
            /\ UNCHANGED << number, localCh >>

wrp(self) == wr(self)

Next == (\E self \in ProcIds: main(self))
           \/ (\E self \in SubProcs: sub(self))
           \/ (\E self \in WrProcs: wrp(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ProcIds : WF_vars((pc[self] # "ncs") /\ main(self))
        /\ \A self \in SubProcs : WF_vars((pc[self] # "L3") /\ sub(self))
        /\ \A self \in WrProcs : WF_vars(wrp(self))

\* END TRANSLATION 

-----------------------------------------------------------------------------
(***************************************************************************)
(* In statement L3, the await condition is satisfied if process <<i,j>>    *)
(* reads localNum[self[1]][self[2]] equal to qm.  This is because that's a *)
(* possible execution, since the process could "interpret" the qm as 0.    *)
(* For checking safety (namely, mutual exclusion), we want to allow that   *)
(* because it's a possibility that must be taken into account.  However,   *)
(* for checking liveness, we don't want to require that the statement must *)
(* be executed when localNum[self[1]][self[2]] equals qm, since that value *)
(* could also be interpreted as localNum[self[1]][self[2]] equal to 1,     *)
(* which could prevent the wait condition from being true.  So we omit     *)
(* that fairness condition from the formula Spec produced by translating   *)
(* the algorithm, and we add weak fairness of the action when              *)
(* localNum[self[1]][self[2]] does not equal qm.  This produces the TLA+   *)
(* specification FSpec defined here.                                       *)
(***************************************************************************)
FSpec == /\ Spec
         /\ \A q \in SubProcs : WF_vars(L3(q) /\ (localNum[q[1]][q[2]] # qm))
         
TypeOK == /\ number \in [Procs -> Nat]
          /\ /\ DOMAIN localNum = Procs
             /\ \A i \in Procs : localNum[i] \in [OtherProcs(i) -> Nat \cup {qm}]
          /\ /\ DOMAIN localCh = Procs
             /\ \A i \in Procs : localCh[i] \in [OtherProcs(i) -> {0,1}]

MutualExclusion == \A p, q \in ProcIds : (p # q) => ({pc[p],pc[q]} # {"cs"})

StarvationFree == \A p \in ProcIds : (pc[p] = "M") ~> (pc[p] = "cs")
-----------------------------------------------------------------------------
(***************************************************************************)
(* Checking the invariant in the appendix of the paper.                    *)
(***************************************************************************)

inBakery(i,j) == \/ pc[<<i,j>>] \in {"Lb", "L2", "L3"}
                 \/ /\ pc[<<i,j>>] = "ch" 
                    /\ pc[<<i>>] \in {"L", "cs"}

inCS(i) == pc[<<i>>] = "cs"

(***************************************************************************)
(* In TLA+, we can't write both inDoorway(i, j, w) and inDoorway(i, j), so *)
(* we change the first to inDoorwayVal.  Its definition differs from the   *)
(* definition of inDoorway(i, j, w) in the paper to avoid having to add a  *)
(* history variable to remember the value of localNum[self[1]][j] read in  *)
(* statement M0.  It's a nicer definition, but it would have required more *)
(* explanation than the definition in the paper.                           *)
(*                                                                         *)
(* The definition of inDoorway(i, j) is equivalent to the one in the       *)
(* paper.  It is obviously implied by \E w \in Nat : inDoorwayVal(i,j,w),  *)
(* and type correctness implies the opposite implication.                  *)
(***************************************************************************)
inDoorwayVal(i, j, w) == /\ pc[<<i>>] = "L"
                         /\ pc[<<i,j>>] = "test"
                         /\ number[i] > w

inDoorway(i, j) == /\ pc[<<i>>] = "L"
                   /\ pc[<<i,j>>] = "test"

Outside(i, j) == ~(inDoorway(i,j) \/ inBakery(i,j))

passed(i, j, LL) == IF LL = "L2" THEN \/ pc[<<i,j>>] = "L3"
                                      \/ /\ pc[<<i,j>>] = "ch" 
                                         /\ pc[<<i>>] \in {"L", "cs"}
                                 ELSE /\ pc[<<i,j>>] = "ch" 
                                      /\ pc[<<i>>] \in {"L", "cs"}
                                      
Before(i, j) == /\ inBakery(i, j)
                /\ \/ Outside(j, i)
                   \/ inDoorwayVal(j, i, number[i])
                   \/ /\ inBakery(j, i)
                      /\ <<number[i], i>> \ll <<number[j], j>>
                      /\ ~passed(j,i,"L3")
                      
Inv(i, j) == /\ inBakery(i, j) => Before(i, j) \/ Before(j, i) 
                                    \/ inDoorway(j, i)   
             /\ passed(i, j, "L2") => Before(i, j) \/ Before(j, i) 
             /\ passed(i, j, "L3") => Before(i, j)                
                      
I == \A i \in Procs : \A j \in OtherProcs(i) : Inv(i, j)
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following is for testing.  Since the spec allows the values of      *)
(* number[n] to get arbitrarily large, there are infinitely many states.   *)
(* The obvious solution to that is to use models with a state constraint   *)
(* that number[n] is at most some value TestMaxNum.  However, TLC would    *)
(* still not be able to execute the spec because the with statement in     *)
(* action M allows an infinite number of possible values for number[n].    *)
(* To solve that problem, we have the model redefine Nat to a finite set   *)
(* of numbers.  The obvious set is 0..TestMaxNum.  However, trying that    *)
(* reveals a subtle problem.  Running the model produces a bogus           *)
(* counterexample to the StarvationFree property.                          *)
(*                                                                         *)
(* This is surprising, since constraints on the state space generally fail *)
(* to find real counterexamples to a liveness property because the         *)
(* counterexamples require large (possibly infinite) traces that are ruled *)
(* out by the state constraint.  The remaining traces may not satisfy the  *)
(* liveness property, but they are ruled out because they fail to satisfy  *)
(* the algorithm's fairness requirements.  In this case, a behavior that   *)
(* didn't satisfy the liveness property StarvationFree but shouldn't have  *)
(* satisfied the fairness requirements of the algorithm did satisfy the    *)
(* fairness requirement because of the substitution of a finite set of     *)
(* numbers for Nat.                                                        *)
(*                                                                         *)
(* Here's what happened: In the behavior, two nodes kept alternately       *)
(* entering the critical section in a way that kept increasing their       *)
(* values of num until one of those values reached TestMaxNum.  That one   *)
(* entered its critical section while the other was in its noncritical     *)
(* section, re-entered its noncritical section, and then the two processes *)
(* kept repeating this dance forever.  Meanwhile, a third process's        *)
(* subprocess was trying to execute action M.  Every time it tried to      *)
(* execute that action, it saw that another process's number equaled       *)
(* TestMaxNum.  In a normal execution, it would just set its value of num  *)
(* larger than TestMaxNum and eventually enter its critical section.       *)
(* However, it couldn't do that because the substitution of 0..TestMaxNum  *)
(* for Nat meant that it couldn't set num to such a value, so the enter    *)
(* step was disabled.  The fairness requirement on the enter action is     *)
(* weak fairness, which requires an action eventually to be taken only if  *)
(* it's continually enabled.  Requiring strong fairness of the action      *)
(* would have solved this problem, because the enabled action kept being   *)
(* enabled and strong fairness would rule out a behavior in which that     *)
(* process's enter step never occurred.  However, it's important that the  *)
(* algorithm satisfy starvation freedom without assuming strong fairness   *)
(* of any of its steps.                                                    *)
(*                                                                         *)
(* The solution to this problem is to substitute 0..(TestMax+1) for Nat.   *)
(* The state constraint will allow the enter step to be taken, but will    *)
(* allow no further steps from that state.  The process still never enters *)
(* its critical section, but now the behavior that keeps it from doing so  *)
(* will violate the weak fairness requirements on that process's steps.    *)
(***************************************************************************)
TestMaxNum == 4
TestNat == 0..(TestMaxNum + 1)
=============================================================================
\* Modification History
\* Last modified Tue Nov 16 18:37:41 CET 2021 by merz
\* Last modified Thu Jul 01 12:24:37 CEST 2021 by merz
\* Last modified Wed Apr 28 18:06:24 PDT 2021 by lamport
\* Created Sat Apr 24 09:45:26 PDT 2021 by lamport6
