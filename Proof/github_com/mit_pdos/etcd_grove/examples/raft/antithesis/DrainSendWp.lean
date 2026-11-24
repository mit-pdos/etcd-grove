/-
Lean-first (no Rocq counterpart). #33 S4: `DrainPhases.lean`'s `drainSend.stmt` proved: `Cluster.drain`'s
send loop (`Cluster.drain.sendE`), over the `Ready`'s messages: for each, the cause reported
(`reportCause`), the `send` report recorded (`report_au` at `sendStep`, raft's facts grown by the
message's: `sendExt`), the message cloned (`proto.Clone`: `cloneMsg.law`, the registered
`raftpb.Message` instance's `ClonePb` specialised) and handed to `Cluster.send` (a forwarded proposal,
or an in-flight message: `netFacts_of_ready`, its certificate, its term within the ceiling, sent).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainPhases
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainReports
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainExt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainMsgs
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainBounds
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRunLaws
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__reportCause
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder__record
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__send
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.msgOf
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- Go's `msgType` of a described type is the binding's. -/
theorem mtypeOf_msgTypeStr {t : w32} {ty : MsgType} (H : mtypeOf t = some ty) :
    msgTypeStr t = AntSim.msgTypeStr ty := by
  have key : ∀ k : Int, uint.Z t = k → t = W32 k := fun k hk => by rw [← hk]; simp
  unfold mtypeOf at H
  split at H <;> cases H <;> rename_i hk <;> rw [key _ hk] <;> decide

theorem mtypeOf_ne_snap {t : w32} {ty : MsgType} (H : mtypeOf t = some ty) (hns : ty ≠ .snap) :
    t ≠ MsgSnap := by
  intro h; subst h; rw [show mtypeOf MsgSnap = some .snap from rfl] at H
  exact hns (Option.some.inj H).symm

/-- **A `Ready` message's `msgOf` report is the protocol message's**: its reading (not a
snapshot), its numbers within `2 ^ 61`. -/
theorem msgOfSt_abs {st : MsgSt} {q : Msg} (habs : absMsgOf st = some q) (hns : q.ty ≠ .snap)
    (hnums : AntSim.MsgNums (2 ^ 61) q) (hterm : uint.Z st.msg.Term' < 2 ^ 61) (to : w64) :
    msgOfSt st to = AntSim.msgOf q to := by
  obtain ⟨hI, hL, hC, hE⟩ := msgNums_st habs hns hnums
  obtain ⟨ty, hty, rfl⟩ := absMsgOf_cases habs hns
  have hns' : st.msg.Type' ≠ MsgSnap := mtypeOf_ne_snap hty hns
  unfold msgOfSt AntSim.msgOf
  simp only [hns', decide_false, Bool.false_eq_true, ↓reduceIte, absMsg, absMsgFrom, Msg.mkV,
    mtypeOf_msgTypeStr hty]
  have e1 : sint.Z st.msg.Term' = uint.Z st.msg.Term' := by word
  have e2 : sint.Z st.msg.Index' = uint.Z st.msg.Index' := by word
  have e3 : sint.Z st.msg.LogTerm' = uint.Z st.msg.LogTerm' := by word
  have e4 : sint.Z st.msg.Commit' = uint.Z st.msg.Commit' := by word
  rw [e1, e2, e3, e4, entOfE_logOf' (fun e he => (hE e he).1)]
where
  entOfE_logOf' {es : List EntryM} (h : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61) :
      es.map entOfE = AntSim.logOf es := by
    unfold AntSim.logOf
    apply List.map_congr_left
    intro e he
    have := h e he
    have e6 : sint.Z e.Term' = uint.Z e.Term' := by word
    unfold entOfE AntSim.entOf
    rw [e6]

/-- The `send` report's numbers. -/
theorem evSend_numsOk {st : MsgSt} {q : Msg} (habs : absMsgOf st = some q) (hns : q.ty ≠ .snap)
    (hnums : AntSim.MsgNums (2 ^ 61) q) (hterm : uint.Z st.msg.Term' < 2 ^ 61) (id : w64)
    (b : AntCheck.Str) : (AntSim.evSend id b q).NumsOk := by
  obtain ⟨hI, hL, hC, hE⟩ := msgNums_st habs hns hnums
  obtain ⟨ty, -, rfl⟩ := absMsgOf_cases habs hns
  simp only [AntSim.evSend, AntCheck.Event.NumsOk, AntCheck.optNumOk, AntSim.msgOf,
    AntCheck.Msg.NumsOk, AntCheck.numOk, AntCheck.numBound, absMsg, absMsgFrom, Msg.mkV,
    AntCheck.entriesOk, AntSim.logOf]
  and_intros
  all_goals try exact True.intro
  all_goals try (intro _ h; cases h; done)
  intro mm hmm
  simp only [Option.some.injEq] at hmm
  subst hmm
  refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, ⟨by word, by word⟩, ⟨by word, by word⟩, ?_⟩
  intro es hes
  simp only [Option.some.injEq] at hes
  subst hes
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  have := (hE x hx).1
  unfold AntSim.entOf
  split <;> exact ⟨by word, by word⟩

theorem evSend_weight {st : MsgSt} {q : Msg} (habs : absMsgOf st = some q) (hns : q.ty ≠ .snap)
    (id : w64) (b : AntCheck.Str) : (AntSim.evSend id b q).weight = st.ents.length + 2 := by
  obtain ⟨ty, -, rfl⟩ := absMsgOf_cases habs hns
  simp [AntSim.evSend, AntCheck.Event.weight, AntCheck.Event.size, AntCheck.Msg.size, AntSim.msgOf,
    AntSim.logOf, absMsg, absMsgFrom, Msg.mkV]

end pure

/-! The range loop over the messages is proved by `wp_slice_for_range_ro`, at the `slice.forRange`
it is about, not unfolded by `wp_auto`. -/
attribute [-instance] pure_wp_slice_for_range

section loop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A range loop over a slice the loop only reads** (a copy of
`Proof/go_etcd_io/raft/v3/DescribeConfChange.lean`'s private `wp_slice_for_range_ro`). -/
theorem wp_slice_for_range_drain {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (dq : DFrac) (body : GoFunc)
    (P : Nat → IProp GF) (Φ : val → IProp GF) :
    sl ↦*{dq} vs -∗ P 0 -∗
    □ (∀ (i : Nat) (x : V), ⌜vs[i]? = some x⌝ -∗ P i -∗ sl ↦*{dq} vs -∗
        WP (App (App (Val #body) (Val #(W64 i))) (Val #x))
          {{ bv, ⌜bv = executeVal⌝ ∗ P (i + 1) ∗ sl ↦*{dq} vs }}) -∗
    (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) -∗
    WP (App (App (Val (slice.forRange t)) (Val #sl)) (Val #body)) {{ Φ }} := by
  iintro Hs HP #Hiter HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  unfold slice.forRange
  wp_auto
  ihave Hinv : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 j ∗ "HP" ∷ P j ∗ "Hs" ∷ sl ↦*{dq} vs ∗
      "HΦ" ∷ (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) ∗ "%Hj" ∷ ⌜j ≤ vs.length⌝ :
      IProp GF) $$ [i HP Hs HΦ]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for Hinv
  by_cases hj : j < vs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, _root_.and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, vs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index (t := t) sl (sint.Z (W64 (j : Int))) vs dq x h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    iapply wp_wand $$ (Hiter $$ %j %x %hx HP Hs)
    iintro %bv ⟨%hbv, HP, Hs⟩
    subst hbv
    iapply wp_for_post_do
    wp_auto
    iframe
    iexists (j + 1)
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    have hj1 : j + 1 ≤ vs.length := hj
    iframe
    ipureintro; exact hj1
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = vs.length := by omega
    subst hjl
    iapply HΦ $$ HP Hs

end loop

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`proto.Clone` of a `raftpb.Message`** (the registered instance's `proto.ClonePb.spec`: with
`pbMessageC_reg`, a frozen message with no responses, `msgPtsCC_msgRoC`, is cloned exactly, as it
marshals): a fresh message owned at the same content, with its capacity. -/
abbrev cloneMsg.law : Prop :=
  ∀ (l : Loc) (c : MsgC), c.resps = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      msgPtsCC l DFrac.discard DFrac.discard false c }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l)))
  {{ (l' : Loc), RET #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l');
      msgPtsCC l' (DFrac.own 1) (DFrac.own 1) true c }}

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

theorem sentW_of_lb (γ : AntNames) (net : List Msg) (m : Msg) (h : m ∈ net) :
    sentLb (GF := GF) γ net ⊢ sentW γ m := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  unfold sentLb sentW monoListIdxOwn
  iintro #H
  iexists i, net
  iframe H
  ipureintro; rw [List.getElem?_eq_getElem hi, he]

/-- **The ceiling below `2 ^ 61`** (the budget's receipt bound, `antRunFits`), its lower bound
persistent. -/
theorem loopRest_tc (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG))
    (h_rb : rnTermLB_rb.law (GF := GF) (hG := hG)) (hfit : antRunFits GF)
    (γ : AntNames) (j : Fin 3) (n : Loc) (v : AntSim.NodeView) (net : List Msg) (rs : RNState) :
    loopRest (GF := GF) γ j n v net rs ⊢ |={⊤}=>
      ⌜uint.Z rs.tc < 2 ^ 61⌝ ∗ □ rnTermLB γ.raft rs.tc ∗ loopRest γ j n v net rs := by
  iintro Hrest
  iunfold loopRest at Hrest
  icases Hrest with ⟨%ms, %si, %cl, %applied, #Hms, Hbs, %Hsto, Hnr, Hrole, Hterm, Hvote, Hcommit,
    Happ, Hcause, Hv, Hl, #Hlb, Hco, %Hby, %HN⟩
  icases nodeRaft_open h_bp γ j rs $$ Hnr with ⟨Htc, #Hb, %Hst, Hnrc⟩
  haveI := h_tlp γ.raft rs.tc
  ihave #Htc := Htc
  imod h_rb γ.raft rs.tc ⊤ (by solve_ndisj) $$ Hb Htc with %Hrb
  ihave Hnr := Hnrc $$ %rs %rfl Htc
  imodintro
  isplitr
  · ipureintro; unfold antRunFits at hfit; have := uint.nat_eq_uint_Z rs.tc; omega
  iframe Htc
  iunfold loopRest
  iexists ms, si, cl, applied
  iframe Hms Hbs Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl Hlb Hco
  ipureintro; exact ⟨Hsto, Hby, HN⟩

end proof

end AntHarness
end EtcdGrove
end Perennial
