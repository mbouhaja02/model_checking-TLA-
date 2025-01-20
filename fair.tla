---- MODULE fair ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N  (* Number of processes *)

(* PlusCal options (-sf) *)

(*
--algorithm Semaphore {
  variables s = <<>>;      (* Shared semaphore counter *)

  macro P(sem) { sem := Append(sem, self);
      while Head(sem) # self do skip; }
  macro V(sem) { sem := Tail(sem); }

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
        /\ s = <<>>
        /\ pc = [self \in ProcSet |-> "loop"]

loop(self) == /\ pc[self] = "loop"
              /\ pc' = [pc EXCEPT ![self] = "lock"]
              /\ s' = s

lock(self) == /\ pc[self] = "lock"
              /\ IF Len(s) > 0 THEN s' = Append(s, self) /\ Head(s) = self
                 ELSE s' = <<self>>
              /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "unlock"]
            /\ s' = s

unlock(self) == /\ pc[self] = "unlock"
                /\ s' = Tail(s)
                /\ pc' = [pc EXCEPT ![self] = "loop"]

P(self) == loop(self) \/ lock(self) \/ cs(self) \/ unlock(self)


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

Fairness == [] (\A p \in 1..N: (REQ(p) \/ CS(p)) => <> CS(p))
====
