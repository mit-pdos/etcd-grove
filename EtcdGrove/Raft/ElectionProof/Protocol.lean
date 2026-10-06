/-
Port of `election_proof/protocol.v` (at feb5c73d4): the protocol model and its ghost
state, one module per part of the Rocq file.
-/
import EtcdGrove.Raft.ElectionProof.Protocol.Model
import EtcdGrove.Raft.ElectionProof.Protocol.Ghost
import EtcdGrove.Raft.ElectionProof.Protocol.GhostState
import EtcdGrove.Raft.ElectionProof.Protocol.StepGhost
import EtcdGrove.Raft.ElectionProof.Protocol.LeaderCompleteness
import EtcdGrove.Raft.ElectionProof.Protocol.Refinement
import EtcdGrove.Raft.ElectionProof.Protocol.Facts
