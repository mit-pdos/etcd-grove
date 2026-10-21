/-
Port of `election_proof/protocol.v` (at feb5c73d4): the protocol model and its ghost
state, one module per part of the Rocq file.

This module is what the shared definitions (`Defs`, `Inv*`) are written on: the
model and the ghost state. The protocol's theorems (`StepGhost`,
`LeaderCompleteness`, `Refinement`, `Facts`) are imported by the proofs that use
them, so that they check in parallel with `Defs` and the invariants instead of
before them.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Model
public import Proof.go_etcd_io.raft.v3.Protocol.Ghost
public import Proof.go_etcd_io.raft.v3.Protocol.GhostState

@[expose] public section
