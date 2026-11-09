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
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Own

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

/-- `string` is not an interface type: so a method of a named string type (`Role`'s `String`) resolves
on a value receiver (a local instance, as `go.NotInterface go.uint64`'s in
`notes/perennial-changes.md`: Perennial states `NotInterface` of the type constructors only). -/
instance notInterface_string_trace [GooseExts] : go.NotInterface go.string := ⟨by unfold go.string; trivial⟩

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

/-! ## Go comparisons, as the Lean's (instances pinned, for `rw`) -/

theorem sint_decide {a b : w64} {x y : Int} (ha : sint.Z a = x) (hb : sint.Z b = y) :
    decide (a = b) = decide (x = y) :=
  decide_eq_decide.2 (sint_eq_iff a b x y ha hb)

theorem sint_decide_nat {a b : w64} {x y : Nat} (ha : sint.Z a = (x : Int)) (hb : sint.Z b = (y : Int)) :
    decide (a = b) = decide (x = y) := by
  rw [sint_decide ha hb]; exact decide_eq_decide.2 Int.ofNat_inj

theorem uint_decide {a b : w64} {x y : Nat} (ha : uint.nat a = x) (hb : uint.nat b = y) :
    decide (a = b) = decide (x = y) :=
  decide_eq_decide.2 (uint_eq_iff a b x y ha hb)

/-- `z == y + x` on `int`s with `y` and `z` far from overflow: the sum wraps only out of their range,
so the Go's comparison is the Lean's on integers whatever `x` (`appendEntriesIfLogged`'s
`e != b+ev.Entries`). -/
theorem add_eq_iff_small (x y z : w64) (hy : -2 ^ 62 < sint.Z y ∧ sint.Z y < 2 ^ 62)
    (hz : -2 ^ 62 < sint.Z z ∧ sint.Z z < 2 ^ 62) :
    z = y + x ↔ sint.Z z = sint.Z y + sint.Z x := by
  constructor
  · intro h; subst h; word
  · intro h; word

/-! ## A trace's lines, purely -/

/-- The line at a position in range is the list's. -/
theorem Trace.line_eq (tr : Trace) (l : Nat) (h1 : 1 ≤ l) (h2 : l ≤ tr.len) :
    tr.lines[l - 1]? = some (tr.line l) := by
  unfold Trace.line Trace.len at *
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl

theorem Trace.isEvent_le {tr : Trace} {ts : TState} {e : String} (h : tr.isEvent ts e = true) :
    ts.l ≤ tr.len := by
  unfold Trace.isEvent at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

theorem Trace.isNodeEvent_le {tr : Trace} {ts : TState} {e : String} {i : ID}
    (h : tr.isNodeEvent ts e i = true) : ts.l ≤ tr.len := by
  unfold Trace.isNodeEvent at h; simp only [Bool.and_eq_true] at h; exact Trace.isEvent_le h.1

theorem Trace.isMessageEvent_le {tr : Trace} {ts : TState} {e : String} {i j : ID}
    (h : tr.isMessageEvent ts e i j = true) : ts.l ≤ tr.len := by
  unfold Trace.isMessageEvent at h; simp only [Bool.and_eq_true] at h; exact Trace.isEvent_le h.1.1.1

theorem Trace.isMessageEvent_msg {tr : Trace} {ts : TState} {e : String} {i j : ID}
    (h : tr.isMessageEvent ts e i j = true) : (tr.line ts.l).ev.msg.isSome = true := by
  unfold Trace.isMessageEvent at h; simp only [Bool.and_eq_true] at h; exact h.1.1.2

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- A Go `TState` (by value) holding `ts`: its state read-only, its positions. -/
def tstateRO (g : G.TState) (ts : TState) : IProp GF :=
  iprop(stateRO g.S' ts.s ∗ ⌜sint.Z g.L' = ts.l ∧ sint.Z g.PL' = ts.pl⌝)

/-- A Go `*line` holding `x` (`logline`'s result, the receiver of `line`'s methods). -/
def linePtrRO (q : Loc) (x : Line) : IProp GF := iprop(∃ ln : G.line, q ↦□ ln ∗ lineRO ln x)

instance linePtrRO_persistent (q : Loc) (x : Line) : Persistent (linePtrRO (GF := GF) q x) := by
  unfold linePtrRO; infer_instance

/-- A fresh `[]*State` holding `sts`, each a read-only state (an action's successors, as
`State.Receive`'s spec returns them). -/
def statesOut (out : GoSlice) (sts : List State) : IProp GF :=
  iprop(∃ qs : List Loc, out ↦* qs ∗ ownSliceCap Loc out (DFrac.own 1) ∗ [∗list] r;s ∈ qs;sts, stateRO r s)

/-- No successor: `nil`. -/
theorem statesOut_nil : ⊢ statesOut (GF := GF) slice.nil [] := by
  unfold statesOut
  iexists []
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  iapply BigSepL2.bigSepL2_nil.2
  ipureintro; trivial

/-- One successor: a one-element slice literal. -/
theorem statesOut_single (out : GoSlice) (q : Loc) (s : State) :
    out ↦* [q] ∗ ownSliceCap Loc out (DFrac.own 1) ∗ stateRO q s ⊢ statesOut (GF := GF) out [s] := by
  unfold statesOut
  iintro ⟨Ho, Hc, Hs⟩
  iexists [q]
  iframe
  iapply BigSepL2.bigSepL2_nil.2
  ipureintro; trivial

/-- A fresh `[]TState` holding `tss` (`receive`'s and `Next`'s successors). -/
def tstatesOut (out : GoSlice) (tss : List TState) : IProp GF :=
  iprop(∃ gs : List G.TState, out ↦* gs ∗ ownSliceCap G.TState out (DFrac.own 1) ∗
    [∗list] g;x ∈ gs;tss, tstateRO g x)

instance tstateRO_persistent (g : G.TState) (ts : TState) : Persistent (tstateRO (GF := GF) g ts) := by
  unfold tstateRO; infer_instance

open github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft in
/-- The package's facts: its three tables. -/
theorem etcdraftInit_get :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ⊢
      etcdraftInit :=
  isPkgInit_access _

end defs

/-! ## Proof tactics (hygiene off: they name the proof's hypotheses) -/

set_option hygiene false in
/-- Open `Ht : traceRO t tr`: the trace's fields (`gt`, its points-to's by field name), its lines
(`lns`, `Hlns`, `Hl`) and their number (`hlenZ`). -/
macro "open_trace" : tactic => `(tactic| (
  ihave #Ht0 := Ht
  iunfold traceRO at Ht0
  icases Ht0 with ⟨%Hv, %gt, #Hp, ⟨%lns, #Hlns, #Hl⟩, #Hsrv, #Hinit, #Hboot, #Hinit0⟩
  ihave %Hlen := ownSlice_len $$ Hlns
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hl
  have hlenZ : (tr.len : Int) = sint.Z gt.lines'.len := by unfold Trace.len; rw [← Hll, Hlen.1]; word
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf))

set_option hygiene false in
/-- Open `Hts : tstateRO g ts`: `Hst : stateRO g.S' ts.s` and `Hg` (its positions). -/
macro "open_ts" : tactic => `(tactic| (
  ihave #Hts0 := Hts
  iunfold tstateRO at Hts0
  icases Hts0 with ⟨#Hst, %Hg⟩))

set_option hygiene false in
/-- Open a line `Hq : q ↦□ ln`, `Hln : lineRO ln x` (`open_lineP`: from `Hlp : linePtrRO q x`): its fields and its event's (`ge`), their
relations (`Hlf`, `Hef`), its message (`Hemsg`, a `match` on `x.ev.msg`) and properties. -/
macro "open_line" : tactic => `(tactic| (
  iunfold lineRO at Hln
  icases Hln with ⟨⟨%ge, #Hev, #Hevr⟩, %Hlf, %ca, %cb, %Hcab, #Hc0, #Hc1⟩
  iunfold eventRO at Hevr
  icases Hevr with ⟨%Hef, -, #Hemsg, #Heprop⟩
  icases typedPointsto_split _ _ _ $$ Hq with Hqf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hqf
  icases typedPointsto_split _ _ _ $$ Hev with Hevf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hevf))

set_option hygiene false in
macro "open_lineP" : tactic => `(tactic| (
  ihave #Hlp0 := Hlp
  iunfold linePtrRO at Hlp0
  icases Hlp0 with ⟨%ln, #Hq, #Hln⟩
  open_line))

set_option hygiene false in
/-- An action's `HΦ'` (`∀ out sts, ⌜sts = <the Lean's>⌝ -∗ statesOut out sts -∗ Φ #out`) applied to
`nil`, the Lean's `[]` shown by `simp` with the given facts. -/
macro "ret_nil" "[" xs:ident,* "]" : tactic => `(tactic| (
  try simp only [Bool.not_false, Bool.not_true]
  try wp_auto
  ihave Hn : statesOut (GF := GF) slice.nil [] $$ []
  · iapply statesOut_nil
  iapply HΦ' $$ [] Hn
  ipureintro; simp [$[$xs:ident],*]))

set_option hygiene false in
/-- `HΦ'` applied to a one-element slice literal of `q`, which holds `s` by `Hs`. -/
macro "ret_single" q:term "," s:term "," Hs:ident "[" xs:ident,* "]" : tactic => `(tactic| (
  try simp only [Bool.not_false, Bool.not_true]
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, Hcap0⟩
  try wp_auto
  ihave Hout := statesOut_single _ $q $s $$ [Hsl0 Hcap0]
  · isplitl [Hsl0]
    · iexact Hsl0
    isplitl [Hcap0]
    · iexact Hcap0
    iexact $Hs:ident
  iapply HΦ' $$ [] Hout
  ipureintro; simp [$[$xs:ident],*]))

set_option hygiene false in
/-- `ret_nil`, for an action the Lean evaluates (`Hev : <the Lean's> = .ok sts`, `HΦ'` over `sts`). -/
macro "ret_nil" "[" xs:ident,* "]" "at" Hev:ident : tactic => `(tactic| (
  try simp only [Bool.not_false, Bool.not_true]
  try wp_auto
  ihave Hn : statesOut (GF := GF) slice.nil [] $$ []
  · iapply statesOut_nil
  iapply HΦ' $$ [] Hn
  ipureintro
  simp [Pure.pure, Except.pure, Bind.bind, Except.bind, $[$xs:ident],*] at $Hev:ident
  first | exact $Hev:ident | exact ($Hev:ident).symm))

set_option hygiene false in
/-- `ret_single`, for an action the Lean evaluates. -/
macro "ret_single" q:term "," s:term "," Hs:ident "[" xs:ident,* "]" "at" Hev:ident : tactic => `(tactic| (
  try simp only [Bool.not_false, Bool.not_true]
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, Hcap0⟩
  try wp_auto
  ihave Hout := statesOut_single _ $q $s $$ [Hsl0 Hcap0]
  · isplitl [Hsl0]
    · iexact Hsl0
    isplitl [Hcap0]
    · iexact Hcap0
    iexact $Hs:ident
  iapply HΦ' $$ [] Hout
  ipureintro
  simp [Pure.pure, Except.pure, Bind.bind, Except.bind, $[$xs:ident],*] at $Hev:ident
  first | exact $Hev:ident | exact ($Hev:ident).symm))

end Etcdraft
end EtcdGrove
end Perennial
