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

theorem mtypeOf_propose {t : w32} (H : mtypeOf t = some .propose) : t = MsgProp := by
  have key : ∀ k : Int, uint.Z t = k → t = W32 k := fun k hk => by rw [← hk]; simp
  unfold mtypeOf at H
  split at H <;> cases H
  rename_i hk; rw [key _ hk]; rfl

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

theorem forall₂_getElem {α β : Type _} {R : α → β → Prop} {l : List α} {k : List β}
    (h : List.Forall₂ R l k) (i : Nat) (h1 : i < l.length) (h2 : i < k.length) : R l[i] k[i] := by
  induction h generalizing i with
  | nil => simp at h1
  | cons hab _ ih =>
    cases i with
    | zero => exact hab
    | succ i => exact ih i (by simpa using h1) (by simpa using h2)

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
  · ipureintro; unfold antRunFits at hfit
    have h1 : uint.Z rs.tc = (uint.nat rs.tc : Int) := by word
    omega
  iframe Htc
  iunfold loopRest
  iexists ms, si, cl, applied
  iframe Hms Hbs Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl Hlb Hco
  ipureintro; exact ⟨Hsto, Hby, HN⟩

end proof

section send
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- **`drainSend.stmt`**: the range loop (`wp_slice_for_range_drain`) at the invariant "the first
`i` messages sent": `drainMid` at a view whose pending messages are the `Ready`'s from the `i`th
on, those messages still owned. An iteration: the cause reported, the message frozen
(`msgPtsCC_persist`) and read (`GetTo`, `msgOf`: `msgOfSt_abs`), the `send` report (`sendStep`,
`sendExt`), the clone handed to `Cluster.send` (a forwarded proposal, or in flight:
`netFacts_of_ready`, its term below the ceiling, sent). -/
theorem drainSend
    (wp_record : Recorder.record.spec (GF := GF) (hG := hG))
    (wp_reportCause : Cluster.reportCause.spec (GF := GF) (hG := hG))
    (wp_msgOf : msgOf.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_send : Cluster.send.spec (GF := GF) (hG := hG))
    (wp_Clone : cloneMsg.law (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG))
    (h_rb : rnTermLB_rb.law (GF := GF) (hG := hG))
    (h_le : rnTermLB_le.law (GF := GF) (hG := hG)) :
    drainSend.stmt (GF := GF) (hG := hG) := by
  intro hTB cp np bp rdp c n γ j I v₁ net₀ qp K Φ
  iintro ⟨#Hpkg, #Hc, #Hn, Hmid, Hmsgs, Hadd, Htt, HΦ⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, #Hr, #Hrec, #Hro, %Hlen, #Hn0, #Hn1, #Hn2,
    #Hstop, #Hbc, #Hnj, #Hinv, %Hfits⟩
  iunfold drainMid at Hmid
  icases Hmid with ⟨Hcp, Hnp, Hbp, Hrdp, #Hrn, Hraw, Hrest, #Hdur, #Hce, %Hv⟩
  imod loopRest_tc h_bp h_tlp h_rb Hfits γ j n v₁ net₀ I.rs₂ $$ Hrest with ⟨%Htc, #Htlb, Hrest⟩
  unfold drainMsgs
  icases Hmsgs with ⟨Hsl, Hcap, Hown, #Hrm, %Hok⟩
  unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.drain.sendE
  icases typedPointsto_not_null_dup _ _ _ $$ Hrdp with ⟨Hrdp, %Hrnn⟩
  iStructNamed Hrdp
  wp_pure
  wp_auto
  ihave Hrdp : (rdp ↦ I.rd : IProp GF) $$ [SoftState HardState ReadStates Entries Snapshot
      CommittedEntries Messages MustSync]
  · iapply typedPointsto_combine _ _ _ Hrnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  have hlen : v₁.pend.length = I.ms.length := (List.Forall₂.length_eq Hok).symm
  wp_apply (wp_slice_for_range_drain (V := Loc) _ I.rd.Messages' (I.ms.map QMsg.loc) (DFrac.own 1) _
    (fun i => iprop(∃ (vv : AntSim.NodeView) (net : List Msg) (x : Loc),
      drainMid cp np bp rdp c n γ j I vv net ∗ ⌜vv.pend = v₁.pend.drop i⌝ ∗ m_ptr ↦ x ∗
      ([∗list] qm ∈ I.ms.drop i, msgOwnZ false qm.loc (readyDq qm.st) qm.st) ∗
      netAdder c γ qp ∗ threadTok))) $$ Hsl [Hcp Hnp Hbp Hrdp Hraw Hrest m Hown Hadd Htt]
  · iexists v₁, net₀, _
    simp only [List.drop_zero]
    iframe m Hown Hadd Htt
    unfold drainMid
    iframe
    iframe Hrn Hdur Hce
    ipureintro; exact Hv
  · imodintro
    iintro %i %x %hx HP Hs
    icases HP with ⟨%vv, %net, %x0, Hmid, %Hpend, Hm, Hown, Hadd, Htt⟩
    have hi : i < I.ms.length := by
      have := (List.getElem?_eq_some_iff.1 hx).1; simpa using this
    have hxe : x = I.ms[i].loc := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi] at hx
      exact (Option.some.inj hx).symm
    subst hxe
    have hip : i < v₁.pend.length := by omega
    have hOk_i : DrainMsgOk (AntSim.nodeId j) I.rs.tc I.ms[i] v₁.pend[i] :=
      forall₂_getElem Hok i hi hip
    rw [List.drop_eq_getElem_cons hip] at Hpend
    rw [List.drop_eq_getElem_cons hi]
    icases Hown with ⟨Hq, Hown⟩
    ihave #Hrq := BigSepL.bigSepL_lookup (Φ := fun _ q => isRaftMsg (GF := GF) γ.raft.raftNames
      (AntSim.nodeId j) q.st) (List.getElem?_eq_getElem hi) $$ Hrm
    iunfold drainMid at Hmid
    icases Hmid with ⟨Hcp, Hnp, Hbp, Hrdp, -, Hraw, Hrest, -, -, %Hv⟩
    iunfold loopRest at Hrest
    icases Hrest with ⟨%ms, %si, %cl, %applied, #Hms, Hbs, %Hsto, Hnr, Hrole, Hterm, Hvote, Hcommit,
      Happ, Hcause, Hvf, Hl, #Hlb, Hco, %Hby, %HN⟩
    obtain ⟨habs, hto, hsh, hnums, hdst, htle⟩ := hOk_i
    have hterm : uint.Z I.ms[i].st.msg.Term' < 2 ^ 61 := by
      have : uint.Z I.rs₂.tc = uint.Z I.rs.tc := rfl
      omega
    have hns : v₁.pend[i].ty ≠ .snap := by
      intro h; rcases hsh.2.1 with h' | h'
      · rcases h' with h' | h' | h' | h' | h' | h' <;> rw [h] at h' <;> cases h'
      · rw [h] at h'; cases h'
    obtain ⟨ty, hty, hmeq⟩ := absMsgOf_cases habs hns
    have hns' : I.ms[i].st.msg.Type' ≠ MsgSnap := mtypeOf_ne_snap hty (by rw [hmeq] at hns; exact hns)
    have hnorm : AllNormal I.ms[i].st.ents := by
      have := hsh.2.2.2; rw [hmeq] at this; exact this
    iunfold msgOwnZ at Hq
    icases Hq with ⟨%cm, Hcc, %Hcm⟩
    imod msgPtsCC_persist _ _ _ $$ Hcc with #Hcc
    have hcs : cm.csUfNil := Hcm.2.1.1
    ihave HpC : msgPtsC (GF := GF) I.ms[i].loc DFrac.discard DFrac.discard false I.ms[i].st $$ []
    · rw [← Hcm.1]; iapply msgPtsCC_msgPtsC _ _ _ _ cm hcs; iexact Hcc
    ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
    · iPkgInit
    ihave #Hn' := Hn
    iunfold nodeRO at Hn'
    icases Hn' with ⟨%ch, #Hid, #Hname, #Hin, #Hbag⟩
    wp_auto
    wp_apply +noauto wp_reportCause c γ n j vv cl $$ [$Hpkg $Hc $Hn $Hcause $Hco $Hvf $Hl]
      as ⟨Hcause, Hco, Hvf, Hl⟩
    wp_take_receipt as Hr1
    wp_apply +noauto wp_GetTo.1 I.ms[i].loc DFrac.discard DFrac.discard false I.ms[i].st
      $$ [$Hpb $HpC] as HpC
    wp_take_receipt as Hr2
    wp_apply +noauto wp_msgOf I.ms[i].loc DFrac.discard DFrac.discard false I.ms[i].st
      I.ms[i].st.msg.To' hns' hnorm $$ [$Hpkg $HpC] as %g ⟨-, #Hg, Hr3⟩
    (try wp_auto)
    obtain ⟨b, hb, hbt⟩ : ∃ b, reportedView vv = { vv with told := b } ∧
        (vv.byE = go!"recv" → b = true) := by
      unfold reportedView
      split
      · exact ⟨true, rfl, fun _ => rfl⟩
      · rename_i h
        refine ⟨vv.told, rfl, fun hb => ?_⟩
        simp only [not_and, Bool.not_eq_false] at h; exact h hb
    rw [hb]
    have hby : vv.byE = I.v.byE := Hv.2.2.2.2.1
    have hmo : msgOfSt I.ms[i].st I.ms[i].st.msg.To' = AntSim.msgOf v₁.pend[i] v₁.pend[i].dst := by
      rw [absMsgOf_dst habs]; exact msgOfSt_abs habs hns hnums hterm _
    ipersist «$a0»
    ihave #Hev : AntCheck.eventRO «$a0_ptr» (AntSim.evSend (AntSim.nodeId j) I.v.byE v₁.pend[i]) $$ []
    · iunfold AntCheck.eventRO
      iexists _
      iframe «$a0»
      simp only [AntSim.evSend, AntCheck.fieldRO]
      isplitr
      · ipureintro
        simp only [AntCheck.fieldRel, AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy,
          AntCheck.fRole, AntCheck.fTerm, AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst,
          AntCheck.fLastIndex, AntCheck.fLastTerm, AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW,
          AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx]
        and_intros <;> first | rfl | decide
      simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing,
        AntCheck.fMsg, AntCheck.fCause]
      rw [← hmo]
      iframe Hg
      ipureintro
      and_intros <;> decide
    have hpend' : ({ vv with told := b } : AntSim.NodeView).pend =
        v₁.pend[i] :: v₁.pend.drop (i + 1) := Hpend
    have hstep := sendStep GF j { vv with told := b } v₁.pend[i] (v₁.pend.drop (i + 1)) net hpend'
      (fun h => hbt h) (by show (AntSim.evSend _ vv.byE _).NumsOk; rw [hby]
                           exact evSend_numsOk habs hns hnums hterm _ _) Hfits
    ihave #Hev' : AntCheck.eventRO «$a0_ptr» (AntSim.evSend (AntSim.nodeId j)
        ({ vv with told := b } : AntSim.NodeView).byE v₁.pend[i]) $$ []
    · have e : ({ vv with told := b } : AntSim.NodeView).byE = I.v.byE := hby
      rw [e]; iexact Hev
    ihave #Hmsg := isRaftMsg_isMessage' γ.raft.raftNames (AntSim.nodeId j) I.ms[i].st v₁.pend[i]
      habs hns $$ Hrq
    ihave #Hext := sendExt γ v₁.pend[i] (by have := hnums.1; omega) $$ Hmsg
    ihave HAU := report_au γ j { vv with told := b }
      { ({ vv with told := b } : AntSim.NodeView) with pend := v₁.pend.drop (i + 1) }
      (AntSim.evSend (AntSim.nodeId j) ({ vv with told := b } : AntSim.NodeView).byE v₁.pend[i])
      net [v₁.pend[i]]
      (fun G => AntSim.MsgFacts G v₁.pend[i]) hstep $$ [Hvf Hl]
    · iframe Hinv Hlb Hext Hvf Hl
    ihave Hrc : ⧗ (AntSim.evSend (AntSim.nodeId j) ({ vv with told := b } : AntSim.NodeView).byE
        v₁.pend[i]).weight $$ [Hr1 Hr2 Hr3]
    · rw [evSend_weight habs hns]
      iapply (receipt_add (GF := GF) (I.ms[i].st.ents.length + 1) 1).2
      iframe Hr2
      iapply (receipt_add (GF := GF) I.ms[i].st.ents.length 1).2
      iframe Hr3 Hr1
    wp_apply +noauto wp_record γ.strm r «$a0_ptr» (AntSim.evSend (AntSim.nodeId j)
      ({ vv with told := b } : AntSim.NodeView).byE v₁.pend[i]) _
      $$ [$Hpkg $Hrec $Hev' $Hrc $HAU] as ⟨Hvf, Hl, %net', #Hlb', %Hpre'⟩
    (try wp_auto)
    ihave %hsent := isRaftMsg_shape γ.raft.raftNames (AntSim.nodeId j) I.ms[i].st $$ Hrq
    have hres : cm.resps = [] := by
      have h := hsent.2.2.2.2.2.2.2
      rw [← Hcm.1] at h
      simpa [MsgC.model] using h
    ihave #Hppk : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
    · iPkgInit
    wp_apply wp_Clone I.ms[i].loc cm hres $$ [$Hppk $Hcc] as %l' Hcl
    ihave Hcl := msgPtsCC_cap_any _ _ _ (needsCap I.ms[i].st.msg) cm $$ Hcl
    imod msgPtsCC_persist_els _ _ _ _ cm $$ Hcl with Hcl
    ihave Hsm : sendMsg (GF := GF) γ l' I.ms[i].st $$ [Hcl]
    · iunfold sendMsg
      by_cases hprop : v₁.pend[i].ty = .propose
      · ileft
        isplitr
        · ipureintro
          apply mtypeOf_propose
          rw [hty, ← hprop, hmeq]; rfl
        iexists cm
        iframe Hcl
        ipureintro; exact ⟨Hcm.1, hcs⟩
      · iright
        iexists v₁.pend[i]
        iunfold netMsg
        isplitl [Hcl]
        · iexists cm
          iframe Hcl
          ipureintro; exact ⟨Hcm.1, hcs⟩
        isplitr
        · ipureintro
          exact netFacts_of_ready habs hto hsh hprop hdst ⟨j, rfl⟩ hsent hnums hterm
        iframe Hmsg
        isplitr
        · iapply h_le γ.raft I.rs₂.tc I.ms[i].st.msg.Term' (by
            have : uint.Z I.rs₂.tc = uint.Z I.rs.tc := rfl
            omega)
          iexact Htlb
        iapply sentW_of_lb γ net' v₁.pend[i] (Hpre'.2 _ List.mem_cons_self)
        iexact Hlb'
    wp_apply wp_send c γ l' I.ms[i].st qp $$ [$Hpkg $Hc $Hadd $Htt $Hsm] as ⟨Hadd, Htt⟩
    isplitr
    · ipureintro; rfl
    iframe Hs
    iexists { ({ vv with told := b } : AntSim.NodeView) with pend := v₁.pend.drop (i + 1) }, net',
      I.ms[i].loc
    iframe Hm Hown Hadd Htt
    isplitl
    · unfold drainMid
      iframe Hcp Hnp Hbp Hrdp Hrn Hraw Hdur Hce
      isplitl
      · iunfold loopRest
        iexists ms, si, null, applied
        iframe Hms Hbs Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hvf Hl Hlb'
        isplitr
        · ipureintro; exact Hsto
        isplitl [Hco]
        · unfold causeOwn; simp only; iexact Hco
        ipureintro; exact ⟨Hby, HN⟩
      ipureintro; exact Hv
    ipureintro; rfl
  iintro ⟨%vv, %net, %x, Hmid, %Hpend, Hm, -, Hadd, Htt⟩ -
  rw [List.length_map, ← hlen, List.drop_length] at Hpend
  wp_auto
  iapply HΦ
  iframe
  ipureintro; exact Hpend

end send

end AntHarness
end EtcdGrove
end Perennial
