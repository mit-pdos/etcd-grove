/-
Port of `election_proof/protocol.v` (at feb5c73d4): the protocol model and its ghost
state, one module per part of the Rocq file.
-/
import EtcdGrove.Raft.Protocol.Model
import EtcdGrove.Raft.Protocol.Ghost
import EtcdGrove.Raft.Protocol.GhostState
import EtcdGrove.Raft.Protocol.StepGhost
import EtcdGrove.Raft.Protocol.LeaderCompleteness
import EtcdGrove.Raft.Protocol.Refinement
import EtcdGrove.Raft.Protocol.Facts
