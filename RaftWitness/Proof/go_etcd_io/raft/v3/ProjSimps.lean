/-
The main tree's `proj_simps` command (`Proof/go_etcd_io/raft/v3/ProjSimps.lean`), re-exported. Until
2026-11-17 a copy of it: a generic command, not raft's, which the witness tree now also reaches
through the main tree (`Proof.runtime.Start` → the backend's `InvBbolt` → bbolt's `Data`, stage S1
of `notes/bbolt-integration-plan.md`), where two copies declare the same names.
-/
module

public import Proof.go_etcd_io.raft.v3.ProjSimps
