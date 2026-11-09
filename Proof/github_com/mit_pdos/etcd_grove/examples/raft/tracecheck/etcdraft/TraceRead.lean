/-
Lean-first (no Rocq counterpart).

# Reading a trace: the trace specification's states and tables (layer C's `trace.go`, 2026-11-09)

What the proofs of `trace.go`'s functions share: a state of the trace specification (`tstateRO`,
Go's `TState` by value: a read-only `*State` and its positions), the package's three tables read
through the package fact (`Base.lean`'s `etcdraftInit`) as the transcription's functions
(`raftMsgType`, `raftMsgSubtype`, `isReceiveName`), and a trace's lines read at a position.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.StateRead

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section types
variable [GooseExts]
abbrev G.TState := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TState
abbrev G.TraceError := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TraceError
end types

/-! ## The tables, purely -/

/-- A Go string constant against a `strRel`-related string: `==` is the Lean `=`. -/
theorem strRel_lit_eq {gs gc : GoString} {s c : String} (h : strRel gs s) (hc : strRel gc c) :
    (gc = gs) = (c = s) :=
  propext (strRel_eq_iff hc h)

/-- `strRel` of a string constant (decided). -/
macro "strRel_lit" : tactic => `(tactic| (unfold strRel; decide))

open github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft in
/-- `RaftMsgType[gs]` is `raftMsgType`'s, as the Go's `MsgType`. -/
theorem raftMsgTypeMap_lookup {gs : GoString} {s : String} (h : strRel gs s) :
    raftMsgTypeMap !! gs = (raftMsgType s).map msgTypeW := by
  have e1 := strRel_lit_eq h (show strRel go!"MsgApp" "MsgApp" by strRel_lit)
  have e2 := strRel_lit_eq h (show strRel go!"MsgAppResp" "MsgAppResp" by strRel_lit)
  have e3 := strRel_lit_eq h (show strRel go!"MsgVote" "MsgVote" by strRel_lit)
  have e4 := strRel_lit_eq h (show strRel go!"MsgVoteResp" "MsgVoteResp" by strRel_lit)
  have e5 := strRel_lit_eq h (show strRel go!"MsgHeartbeat" "MsgHeartbeat" by strRel_lit)
  have e6 := strRel_lit_eq h (show strRel go!"MsgHeartbeatResp" "MsgHeartbeatResp" by strRel_lit)
  have e7 := strRel_lit_eq h (show strRel go!"MsgSnap" "MsgSnap" by strRel_lit)
  have e8 := strRel_lit_eq h (show strRel go!"MsgPreVote" "MsgPreVote" by strRel_lit)
  have e9 := strRel_lit_eq h (show strRel go!"MsgPreVoteResp" "MsgPreVoteResp" by strRel_lit)
  simp only [raftMsgTypeMap, GMap.insert, GMap.empty, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  by_cases h1 : "MsgApp" = s; · subst h1; rfl
  by_cases h2 : "MsgAppResp" = s; · subst h2; rfl
  by_cases h3 : "MsgVote" = s; · subst h3; rfl
  by_cases h4 : "MsgVoteResp" = s; · subst h4; rfl
  by_cases h5 : "MsgHeartbeat" = s; · subst h5; rfl
  by_cases h6 : "MsgHeartbeatResp" = s; · subst h6; rfl
  by_cases h7 : "MsgSnap" = s; · subst h7; rfl
  by_cases h8 : "MsgPreVote" = s; · subst h8; rfl
  by_cases h9 : "MsgPreVoteResp" = s; · subst h9; rfl
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, ite_false]
  unfold raftMsgType
  split <;> simp_all

open github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft in
/-- `RaftMsgSubtype[gs]` is `raftMsgSubtype`'s: defined at the same strings, each holding the Lean's. -/
theorem raftMsgSubtypeMap_lookup {gs : GoString} {s : String} (h : strRel gs s) :
    (raftMsgSubtypeMap !! gs).isSome = (raftMsgSubtype s).isSome ∧
    ∀ g t, raftMsgSubtypeMap !! gs = some g → raftMsgSubtype s = some t → strRel g t := by
  have e1 := strRel_lit_eq h (show strRel go!"MsgHeartbeat" "MsgHeartbeat" by strRel_lit)
  have e2 := strRel_lit_eq h (show strRel go!"MsgHeartbeatResp" "MsgHeartbeatResp" by strRel_lit)
  have e3 := strRel_lit_eq h (show strRel go!"MsgApp" "MsgApp" by strRel_lit)
  have e4 := strRel_lit_eq h (show strRel go!"MsgAppResp" "MsgAppResp" by strRel_lit)
  have e5 := strRel_lit_eq h (show strRel go!"MsgSnap" "MsgSnap" by strRel_lit)
  simp only [raftMsgSubtypeMap, GMap.insert, GMap.empty, e1, e2, e3, e4, e5]
  by_cases h1 : "MsgHeartbeat" = s
  · subst h1; refine ⟨rfl, ?_⟩; intro g t hg ht; cases hg; cases ht; strRel_lit
  by_cases h2 : "MsgHeartbeatResp" = s
  · subst h2; refine ⟨rfl, ?_⟩; intro g t hg ht; cases hg; cases ht; strRel_lit
  by_cases h3 : "MsgApp" = s
  · subst h3; refine ⟨rfl, ?_⟩; intro g t hg ht; cases hg; cases ht; strRel_lit
  by_cases h4 : "MsgAppResp" = s
  · subst h4; refine ⟨rfl, ?_⟩; intro g t hg ht; cases hg; cases ht; strRel_lit
  by_cases h5 : "MsgSnap" = s
  · subst h5; refine ⟨rfl, ?_⟩; intro g t hg ht; cases hg; cases ht; strRel_lit
  simp only [h1, h2, h3, h4, h5, ite_false]
  have : raftMsgSubtype s = none := by unfold raftMsgSubtype; split <;> simp_all
  rw [this]
  exact ⟨rfl, fun _ _ h => by cases h⟩

open github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft in
/-- `ReceiveMessageTraceNames[gs]` is `isReceiveName`. -/
theorem receiveNamesMap_lookup {gs : GoString} {s : String} (h : strRel gs s) :
    (receiveNamesMap !! gs).getD false = isReceiveName s := by
  have e1 := strRel_lit_eq h (show strRel go!"ReceiveAppendEntriesRequest" "ReceiveAppendEntriesRequest" by strRel_lit)
  have e2 := strRel_lit_eq h (show strRel go!"ReceiveAppendEntriesResponse" "ReceiveAppendEntriesResponse" by strRel_lit)
  have e3 := strRel_lit_eq h (show strRel go!"ReceiveRequestVoteRequest" "ReceiveRequestVoteRequest" by strRel_lit)
  have e4 := strRel_lit_eq h (show strRel go!"ReceiveRequestVoteResponse" "ReceiveRequestVoteResponse" by strRel_lit)
  have e5 := strRel_lit_eq h (show strRel go!"ReceiveSnapshot" "ReceiveSnapshot" by strRel_lit)
  simp only [receiveNamesMap, GMap.insert, GMap.empty, e1, e2, e3, e4, e5]
  unfold isReceiveName
  by_cases h1 : "ReceiveAppendEntriesRequest" = s; · subst h1; rfl
  by_cases h2 : "ReceiveAppendEntriesResponse" = s; · subst h2; rfl
  by_cases h3 : "ReceiveRequestVoteRequest" = s; · subst h3; rfl
  by_cases h4 : "ReceiveRequestVoteResponse" = s; · subst h4; rfl
  by_cases h5 : "ReceiveSnapshot" = s; · subst h5; rfl
  simp only [h1, h2, h3, h4, h5, ite_false]
  simp only [Option.getD_none]
  have n1 : (s == "ReceiveAppendEntriesRequest") = false := beq_eq_false_iff_ne.2 (fun e => h1 e.symm)
  have n2 : (s == "ReceiveAppendEntriesResponse") = false := beq_eq_false_iff_ne.2 (fun e => h2 e.symm)
  have n3 : (s == "ReceiveRequestVoteRequest") = false := beq_eq_false_iff_ne.2 (fun e => h3 e.symm)
  have n4 : (s == "ReceiveRequestVoteResponse") = false := beq_eq_false_iff_ne.2 (fun e => h4 e.symm)
  have n5 : (s == "ReceiveSnapshot") = false := beq_eq_false_iff_ne.2 (fun e => h5 e.symm)
  rw [n1, n2, n3, n4, n5]; rfl

/-! ## A trace's lines, purely -/

/-- The line at a position in range is the list's. -/
theorem Trace.line_eq (tr : Trace) (l : Nat) (h1 : 1 ≤ l) (h2 : l ≤ tr.len) :
    tr.lines[l - 1]? = some (tr.line l) := by
  unfold Trace.line Trace.len at *
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- A Go `TState` (by value) holding `ts`: its state read-only, its positions. -/
def tstateRO (g : G.TState) (ts : TState) : IProp GF :=
  iprop(stateRO g.S' ts.s ∗ ⌜sint.Z g.L' = ts.l ∧ sint.Z g.PL' = ts.pl⌝)

instance tstateRO_persistent (g : G.TState) (ts : TState) : Persistent (tstateRO (GF := GF) g ts) := by
  unfold tstateRO; infer_instance

open github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft in
/-- The package's facts: its three tables. -/
theorem etcdraftInit_get :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ⊢
      etcdraftInit :=
  isPkgInit_access _

end defs

end Etcdraft
end EtcdGrove
end Perennial
