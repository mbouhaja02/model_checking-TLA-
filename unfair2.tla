---- MODULE unfair2 ----
EXTENDS Naturals, TLC

CONSTANTS N  (* Number of processes *)

(* PlusCal options (-sf) *)

(*
--algorithm Semaphore {
variables s = 1;            (* Shared semaphore counter *)

process (P \in 1..N)
variables go = FALSE;       (* Clearing flag *)
{
loop:  while (TRUE) {
lock:    if (s > 0) {       (* Atomic test-and-set *)
           s := s-1;
           go := TRUE
         };
testing: if (go = FALSE) {
           goto lock
         };
cs:      skip;              (* In the critical section *)
unlock:  s := s+1;
         go := FALSE
       }
}

}
*)

\* BEGIN TRANSLATION
VARIABLES pc, s, go

vars == << pc, s, go >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ s = 1
        (* Process P *)
        /\ go = [self \in 1..N |-> FALSE]
        /\ pc = [self \in ProcSet |-> "loop"]

loop(self) == /\ pc[self] = "loop"
              /\ pc' = [pc EXCEPT ![self] = "lock"]
              /\ UNCHANGED << s, go >>

lock(self) == /\ pc[self] = "lock"
              /\ IF s > 0
                    THEN /\ s' = s-1
                         /\ go' = [go EXCEPT ![self] = TRUE]
                    ELSE /\ TRUE
                         /\ UNCHANGED << s, go >>
              /\ pc' = [pc EXCEPT ![self] = "testing"]

testing(self) == /\ pc[self] = "testing"
                 /\ IF go[self] = FALSE
                       THEN /\ pc' = [pc EXCEPT ![self] = "lock"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                 /\ UNCHANGED << s, go >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "unlock"]
            /\ UNCHANGED << s, go >>

unlock(self) == /\ pc[self] = "unlock"
                /\ s' = s+1
                /\ go' = [go EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "loop"]

P(self) == loop(self) \/ lock(self) \/ testing(self) \/ cs(self)
              \/ unlock(self)

Next == (\E self \in 1..N: P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : SF_vars(P(self))

\* END TRANSLATION

(* Atomic propositions *)
CS(p) == (pc[p] = "cs")
REQ(p) == (pc[p] = "lock")

(* In every state, there is at most one process in the critical section *)
Mutex == [](\A p \in 1..N: \A q \in (1..N \{p}): ~(CS(p) /\ CS(q)))

(* Every process that tries to enter the critical section is eventually granted the access to the critical section *)
NoStarvation == \A p \in 1..N: [](REQ(p) => <>CS(p))

====
