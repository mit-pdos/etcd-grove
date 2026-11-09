/-
Lean-first (no Rocq counterpart).

# The Go checker's package initialization (Draft, 2026-11-08)

`examples/raft/tracecheck/etcdraft` has package-level variables (`EmptyBag`, `Invariants`, the
tables `RaftMsgType`, `RaftMsgSubtype`, `ReceiveMessageTraceNames`). Draft: its package fact holds
what the proofs read of those variables, which callers get from the package's initialization
(`etc/gen-init.py`, Draft S6 of `notes/trace-validation-plan.md`), not from the specs: the three
tables (layer C's `trace.go`, 2026-11-09), each at a map Go never writes after initialization,
holding its literal (`raftMsgTypeMap`, `raftMsgSubtypeMap`, `receiveNamesMap`). `Invariants`'
functions are still to add (`Violated`).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft
public import Perennial.Proof.fmt
public import Perennial.Proof.strconv
public import Perennial.Proof.strings

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft

/-- `RaftMsgType`'s literal (`trace.go`; `MsgType`'s values are `iota`'s, `types.go`). -/
def raftMsgTypeMap : GMap GoString w8 :=
  GMap.insert go!"MsgApp" (W8 2) <| GMap.insert go!"MsgAppResp" (W8 3) <|
  GMap.insert go!"MsgVote" (W8 0) <| GMap.insert go!"MsgVoteResp" (W8 1) <|
  GMap.insert go!"MsgHeartbeat" (W8 2) <| GMap.insert go!"MsgHeartbeatResp" (W8 3) <|
  GMap.insert go!"MsgSnap" (W8 2) <|
  GMap.insert go!"MsgPreVote" (W8 4) <| GMap.insert go!"MsgPreVoteResp" (W8 5) <| GMap.empty

/-- `RaftMsgSubtype`'s literal. -/
def raftMsgSubtypeMap : GMap GoString GoString :=
  GMap.insert go!"MsgHeartbeat" go!"heartbeat" <| GMap.insert go!"MsgHeartbeatResp" go!"heartbeat" <|
  GMap.insert go!"MsgApp" go!"app" <| GMap.insert go!"MsgAppResp" go!"app" <|
  GMap.insert go!"MsgSnap" go!"snapshot" <| GMap.empty

/-- `ReceiveMessageTraceNames`' literal. -/
def receiveNamesMap : GMap GoString Bool :=
  GMap.insert go!"ReceiveAppendEntriesRequest" true <| GMap.insert go!"ReceiveAppendEntriesResponse" true <|
  GMap.insert go!"ReceiveRequestVoteRequest" true <| GMap.insert go!"ReceiveRequestVoteResponse" true <|
  GMap.insert go!"ReceiveSnapshot" true <| GMap.empty

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- The package's facts: the three tables, each a map holding its literal for good. -/
abbrev etcdraftInit : IProp GF :=
  iprop((∃ m : Loc, globalAddr RaftMsgType ↦□ m ∗ m ↦$□ raftMsgTypeMap) ∗
    (∃ m : Loc, globalAddr RaftMsgSubtype ↦□ m ∗ m ↦$□ raftMsgSubtypeMap) ∗
    (∃ m : Loc, globalAddr ReceiveMessageTraceNames ↦□ m ∗ m ↦$□ receiveNamesMap))

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft :=
  define_is_pkg_init etcdraftInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft

end Perennial
