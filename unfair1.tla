---- MODULE unfair1 ----
EXTENDS Naturals, TLC

CONSTANTS N  (* Number of processes *)


(*
--algorithm Semaphore {
  variables s = 1;      (* Shared semaphore counter *)

  macro P(sem) { await sem > 0; sem := sem - 1 }
  macro V(sem) { sem := sem + 1 }

  process (P \in 1..N)
  {
  loop:  while (TRUE) {
  lock:    P(s);
  cs:      skip;              (* In the critical section *)
  unlock:  V(s)
         }
  }
}
*)

\* BEGIN TRANSLATION
VARIABLES pc, s

vars == << pc, s >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ s = 1
        /\ pc = [self \in ProcSet |-> "loop"]

loop(self) == /\ pc[self] = "loop"
              /\ pc' = [pc EXCEPT ![self] = "lock"]
              /\ s' = s

lock(self) == /\ pc[self] = "lock"
              /\ s > 0
              /\ s' = s - 1
              /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "unlock"]
            /\ s' = s

unlock(self) == /\ pc[self] = "unlock"
                /\ s' = s + 1
                /\ pc' = [pc EXCEPT ![self] = "loop"]

P(self) == loop(self) \/ lock(self) \/ cs(self) \/ unlock(self)

Next == (\E self \in 1..N: P(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(* Atomic propositions *)
CS(p) == (pc[p] = "cs")
REQ(p) == (pc[p] = "lock")

(* In every state, there is at most one process in the critical section *)
Mutex == [](\A p \in 1..N: \A q \in (1..N \{p}): ~(CS(p) /\ CS(q)))

(* Every process that tries to enter the critical section is eventually granted the access to the critical section *)
NoStarvation == \A p \in 1..N: [](REQ(p) => <>CS(p))

====
