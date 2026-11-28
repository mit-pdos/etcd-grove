/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E: `DrainB1Phases.lean`'s
`drainAdvanceB1.stmt` proved (`drainAdvanceB1`; `node.drain.tailE`: `reads`, `applyCommitted`,
`Advance`, the `sent` loop), the loop head closed at the view after the reports (`nodeOwn_loop_close`:
`Reach.advance` from `Advance`'s `AdvanceEndR`/`AdvanceEndRNoSnap`, whose premise (the configuration kept,
`CfgKeep`) holds as the view's entries are normal; `n.applied` the delivered length as the log's indices
are its positions, `lastIdx_len`). The reports' pieces: The `read` reports (`readsAfter_intro`: per read state, `report_upd`
at `readHstep`, the read's index past every committed length its context was asked at from
`readsOwn` and raft's `readStateRaw`, `reads_fl`), the `apply` report's event (`applyEv_eq`,
`evApply_numsOk_b1`), the cause cell peeked when nothing is reported (`causeOwn_peek`), `Advance`
without a snapshot in the Sim's vocabulary (`advanceNoSnap_of`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1SendWp
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1ReadStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__reads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__applyCommitted
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__sent
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

/-- `reads`' report of a read state within `2 ^ 61` at node `id` is the Sim's `evRead`. -/
theorem readEv_eq (id : w64) (r : ReadStateM) (h : uint.Z r.Index' < 2 ^ 61) :
    atNode (AntSim.nameOf id) (readEvM r) = AntSim.evRead id r.RequestCtx' r.Index' := by
  have e : sint.Z r.Index' = uint.Z r.Index' := by word
  unfold atNode readEvM AntSim.evRead
  rw [e]

theorem evRead_numsOk (id : w64) (ctx : List w8) (i : w64) (h : uint.Z i < 2 ^ 61) :
    (AntSim.evRead id ctx i).NumsOk := by
  have h0 : 0 ≤ uint.Z i := by word
  simp only [AntSim.evRead, AntCheck.Event.NumsOk, AntCheck.optNumOk, AntCheck.numOk,
    AntCheck.numBound]
  and_intros
  all_goals try exact True.intro
  all_goals try (intro _ h; cases h; done)
  all_goals omega

theorem evRead_chgOk (id : w64) (ctx : List w8) (i : w64) : (AntSim.evRead id ctx i).ChgOk 0 := by
  simp [AntCheck.Event.ChgOk, AntCheck.Event.entryLists, AntSim.evRead]

theorem evRead_weight (id : w64) (ctx : List w8) (i : w64) : (AntSim.evRead id ctx i).weight = 2 := by
  simp [AntCheck.Event.weight, AntCheck.Event.size, AntSim.evRead]

/-- Entries with terms below `2 ^ 61` read by `entryOf` as the binding's (`sint` is `uint`). -/
theorem entOfE_logOf {es : List EntryM} (h : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61) :
    es.map entOfE = AntSim.logOf es := by
  unfold AntSim.logOf
  apply List.map_congr_left
  intro e he
  have := h e he
  have e6 : sint.Z e.Term' = uint.Z e.Term' := by word
  unfold entOfE AntSim.entOf
  rw [e6]

/-- `applyCommitted`'s report of entries within `2 ^ 61` at node `id` is the Sim's `evApply`. -/
theorem applyEv_eq (id : w64) (b : AntCheck.Str) {es : List EntryM}
    (h : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61) :
    atNode (AntSim.nameOf id) (applyEvM b es) = AntSim.evApply id b es := by
  have hf : sint.Z (firstIdx es) = AntSim.firstOf es := by
    cases es with
    | nil => simp only [firstIdx, AntSim.firstOf, List.head?_nil, Option.map_none, Option.getD_none]; rfl
    | cons e _ =>
      have := (h e List.mem_cons_self).2
      simp only [firstIdx, AntSim.firstOf, List.head?_cons, Option.map_some, Option.getD_some]
      word
  unfold atNode applyEvM AntSim.evApply
  rw [hf, entOfE_logOf (fun e he => (h e he).1)]

theorem evApply_numsOk_b1 {id : w64} {b : AntCheck.Str} {ce : List EntryM}
    (h : ∀ e ∈ ce, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61) :
    (AntSim.evApply id b ce).NumsOk := by
  simp only [AntSim.evApply, AntCheck.Event.NumsOk, AntCheck.optNumOk, AntCheck.numOk,
    AntCheck.numBound, AntCheck.entriesOk, AntSim.logOf]
  and_intros
  all_goals try exact True.intro
  all_goals try (intro _ h; cases h; done)
  · cases ce with
    | nil => simp only [AntSim.firstOf]; omega
    | cons e _ =>
      have := (h e List.mem_cons_self).2
      simp only [AntSim.firstOf]; word
  · cases ce with
    | nil => simp only [AntSim.firstOf]; omega
    | cons e _ =>
      have := (h e List.mem_cons_self).2
      simp only [AntSim.firstOf]; word
  · intro es hes
    simp only [Option.some.injEq] at hes
    subst hes
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    have := (h e he).1
    unfold AntSim.entOf
    split
    · exact ⟨by word, by word⟩
    · split <;> exact ⟨by word, by word⟩

theorem evApply_weight_b1 (id : w64) (b : AntCheck.Str) (ce : List EntryM) :
    (AntSim.evApply id b ce).weight = ce.length + 2 := by
  simp [AntSim.evApply, AntCheck.Event.weight, AntCheck.Event.size, AntSim.logOf]

theorem evApply_chgOk (id : w64) (b : AntCheck.Str) (ce : List EntryM) :
    (AntSim.evApply id b ce).ChgOk 0 := by
  intro l hl e he
  simp only [AntCheck.Event.entryLists, AntSim.evApply, Option.getD_some, Option.map_none,
    Option.getD_none, List.nil_append, List.flatMap_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hl
  subst hl
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
  exact Nat.le_of_eq (entOf_chgSize x)

/-- (antithesis parity B1) `Advance` without a snapshot, from raft's vocabulary to the Sim's. -/
theorem advanceNoSnap_of {Adm : List EntryM → CCState → Prop} {dec : CCDec} {k : NodeK} {id : w64}
    {r r' : RState} {qs : List Msg} (h : AdvanceEndRNoSnap Adm dec k id r qs r') :
    AntSim.AdvanceNoSnap Adm dec k id r qs r' := by
  induction h with
  | nil r r' ha => exact .nil _ _ ha
  | cons r r1 r' q qs hr _ ih => exact .cons _ _ _ _ _ hr ih

/-- The view after `reads`: the read states reported, `told` as the cause's report left it, the
answered read requests dropped. -/
abbrev readsV (v : AntSim.NodeView) (b : Bool) (R : List (AntCheck.Str × Nat)) : AntSim.NodeView :=
  { v with told := b, rpend := [], reads := R }

/-- The view after `applyCommitted`: unchanged without committed entries; else the cause reported
(`told := b`) and the `apply` report made (`applyView`). -/
def applyV (v : AntSim.NodeView) (b : Bool) : AntSim.NodeView :=
  if v.ce = [] then v else applyView { v with told := b }

theorem applyV_eq (v : AntSim.NodeView) (b : Bool) :
    ∃ (b' : Bool) (U : Option AntSim.DurW) (M : Bool), applyV v b =
      { v with told := b', delivered := v.delivered ++ v.ce, ce := [], undo := U, made := M } := by
  unfold applyV
  split
  · rename_i h
    refine ⟨v.told, v.undo, v.made, ?_⟩
    cases v; simp_all
  · exact ⟨b, none, true, rfl⟩

/-- The last committed entry's index is the length of what is handed out through it (the log's
indices its positions). `applyCommitted`'s `n.applied` against the view. -/
theorem lastIdx_len {l D ce : List EntryM} (hl : AntSim.LogIdx l) (hp : D ++ ce <+: l)
    (hne : ce ≠ []) (a : w64) :
    uint.nat ((ce.getLast?.map (·.Index')).getD a) = (D ++ ce).length := by
  have hL := logIdx_prefix hl hp
  obtain ⟨x, hx⟩ : ∃ x, ce.getLast? = some x := by
    cases h : ce.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some x => exact ⟨x, rfl⟩
  have hpos : 0 < ce.length := by
    cases ce with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hget : (D ++ ce)[(D ++ ce).length - 1]? = some x := by
    rw [List.getLast?_eq_getElem?] at hx
    rw [List.getElem?_append_right (by simp only [List.length_append]; omega)]
    rw [← hx]; congr 1; simp only [List.length_append]; omega
  have h1 := hL _ _ hget
  rw [hx]
  simp only [Option.map_some, Option.getD_some]
  have h2 : uint.nat x.Index' = (uint.Z x.Index').toNat := rfl
  rw [h2, h1]
  simp only [List.length_append]
  omega

theorem noConf_of_normal {l : List EntryM} (h : AllNormal l) (lo hi : Nat) : NoConfIn l lo hi :=
  fun _ e _ _ hk hc => by
    have hn := h e (List.mem_of_getElem? hk)
    unfold IsConfEnt at hc
    rcases hc with hc | hc <;> rw [hn] at hc <;> simp at hc

theorem drainBy_of_byOk {b : AntCheck.Str} (h : ByOk b) : AntSim.DrainBy b := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr ⟨.recv (Msg.plain .appResp (W64 0) (W64 0) (W64 0) false), rfl⟩
  · exact .inr ⟨.tick, rfl⟩
  · exact .inr ⟨.propose [], rfl⟩
  · exact .inr ⟨.readIndex [], rfl⟩
  · exact .inr ⟨.campaign, rfl⟩
  · exact .inr ⟨.transfer (W64 0), rfl⟩

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- **The cause cell, when nothing is reported**: its pending report, given back unchanged. -/
theorem causeOwn_peek (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (cl : Loc) :
    causeOwn (GF := GF) γ j v cl ⊢
      ∃ o, pendingCause cl o ∗ (pendingCause cl o -∗ causeOwn γ j v cl) := by
  unfold causeOwn
  split
  · iintro (⟨%m, %Hm, Hpc, #Hw, Hr⟩ | ⟨%x, %Hx, Hpc, #Hw, Hr⟩)
    · iexists _
      iframe Hpc
      iintro Hpc
      ileft
      iexists m
      iframe Hpc Hw Hr
      ipureintro; exact Hm
    · iexists _
      iframe Hpc
      iintro Hpc
      iright
      iexists x
      iframe Hpc Hw Hr
      ipureintro; exact Hx
  · iintro Hpc
    iexists none
    iframe Hpc
    iintro Hpc
    iexact Hpc

theorem bigSepL_filter_drop {A : Type} (Φ : A → IProp GF) (p : A → Bool) :
    ∀ l : List A, ([∗list] x ∈ l, Φ x) ⊢ [∗list] x ∈ l.filter p, Φ x
  | [] => by simp only [List.filter_nil]; exact .rfl
  | a :: l => by
    rw [List.filter_cons]
    split
    · iintro H
      icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Ha, Hl⟩
      iapply (BigSepL.bigSepL_cons).2
      iframe Ha
      iapply bigSepL_filter_drop Φ p l
      iexact Hl
    · iintro H
      icases (BigSepL.bigSepL_cons).1 $$ H with ⟨-, Hl⟩
      iapply bigSepL_filter_drop Φ p l
      iexact Hl

/-- **A read state's index is past every committed length its context was asked at**: the view's
request (`readsOwn`) and raft's certificate (`readStateRaw`) name the same committed log
(`readReq_agree`). `readHstep`'s `hfl`. -/
theorem reads_fl (γ : AntNames) (v : AntSim.NodeView) (st : ReadStateM) :
    readsOwn (GF := GF) γ v ∗ readStateRaw γ.raft.raftNames st ⊢
      ⌜∀ f, (st.RequestCtx', f) ∈ v.reads → f ≤ uint.nat st.Index'⌝ := by
  refine (forall_intro fun f => ?_).trans pure_forall.2
  refine (forall_intro fun hf => ?_).trans pure_forall.2
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hf
  iintro ⟨#Hro, #Hst⟩
  iunfold readsOwn at Hro
  ihave ⟨%Lc, #Hq, %Hle⟩ := BigSepL.bigSepL_lookup (Φ := fun _ (p : AntCheck.Str × Nat) =>
    iprop(∃ Lc : List EntryM, readReq γ.raft.raftNames p.1 Lc ∗ ⌜p.2 ≤ Lc.length⌝)) hi $$ Hro
  iunfold readStateRaw at Hst
  icases Hst with ⟨%c, %hc, Hok⟩
  iunfold EtcdGrove.readOk at Hok
  icases Hok with ⟨%Lc', #Hq', %Hle'⟩
  subst hc
  ihave %Heq := readReq_agree γ.raft.raftNames _ _ _ $$ Hq Hq'
  ipureintro
  subst Heq
  simp only at Hle
  have : (uint.nat st.Index' : Int) = uint.Z st.Index' := by word
  omega

/-- **The `read` reports** (`reads`' `readsAfter`): from the view `v` whose read states to report
are `L` (`Told`: the cause reported), each reported in order through `report_upd` at `readHstep`;
then `Φ` at a view with none left, the rest of `v` kept but its read requests (`readView` drops
the answered ones; `readsOwn` kept for what is left). -/
theorem readsAfter_intro (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (c : Loc) (γ : AntNames) (j : Fin γ.R.N)
    (hinm : ∀ S V net xnet, AntSim.AntSim γ.R γ.dec S V net xnet →
      AntSim.InMask AntSim.mskB1 γ.R net xnet) (Φ : IProp GF) :
    ∀ (L : List ReadStateM) (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg),
    v.rpend = L → AntSim.Told v → (∀ st ∈ L, uint.Z st.Index' < 2 ^ 61) →
    antCluster c γ ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗ readsOwn γ v ∗
      ([∗list] st ∈ L, readStateRaw γ.raft.raftNames st) ∗ viewFrag γ j v ∗ nodeLive γ j ∗
      (∀ (v' : AntSim.NodeView) (net : List Msg) (xnet : List XMsg),
        ⌜v' = { v with rpend := [], reads := v'.reads } ∧ net₀ <+: net ∧ xnet₀ <+: xnet⌝ -∗
        readsOwn γ v' -∗ sentLb γ net -∗ xsentLb γ xnet -∗ viewFrag γ j v' -∗ nodeLive γ j -∗ Φ) ⊢
    readsAfter γ.strm (AntSim.nameOf (AntSim.nodeId j)) L Φ
  | [], v, net₀, xnet₀, hrp, _, _ => by
    iintro ⟨#Hc, #Hlb, #Hxlb, #Hro, -, Hv, Hl, HΦ⟩
    simp only [readsAfter]
    iapply HΦ $$ %v %net₀ %xnet₀ [] Hro Hlb Hxlb Hv Hl
    ipureintro
    exact ⟨by rw [← hrp], List.prefix_refl _, List.prefix_refl _⟩
  | st :: L, v, net₀, xnet₀, hrp, htold, hidx => by
    iintro ⟨#Hc, #Hlb, #Hxlb, #Hro, Hst, Hv, Hl, HΦ⟩
    icases (BigSepL.bigSepL_cons).1 $$ Hst with ⟨#Hst1, Hst⟩
    ihave %hfl := reads_fl γ v st $$ [$Hro $Hst1]
    simp only [readsAfter]
    iintro Hr
    have hi := hidx st List.mem_cons_self
    rw [readEv_eq _ st hi]
    iapply report_upd h_vu h_lo c γ j v (readView v st L) (AntSim.evRead (AntSim.nodeId j)
      st.RequestCtx' st.Index') net₀ [] xnet₀ [] (fun G0 G => G = G0) _
      (evRead_numsOk _ _ _ hi) (evRead_chgOk _ _ _)
      (readHstep j v st L net₀ xnet₀ hinm hrp htold hfl)
    iframe Hc Hlb Hxlb Hv Hl
    isplitl []
    · iapply factsExt_none
    isplitl [Hr]
    · rw [evRead_weight]; iexact Hr
    iintro ⟨Hv, Hl, %net, %xnet, #Hlb2, #Hxlb2, %Hp2⟩
    ihave #Hro2 : readsOwn (GF := GF) γ (readView v st L) $$ [Hro]
    · iunfold readsOwn
      iunfold readsOwn at Hro
      iapply bigSepL_filter_drop
      iexact Hro
    iapply readsAfter_intro h_vu h_lo c γ j hinm Φ L (readView v st L) net xnet rfl htold
      (fun s hs => hidx s (List.mem_cons_of_mem _ hs))
    iframe Hc Hlb2 Hxlb2 Hro2 Hst Hv Hl
    iintro %v' %net' %xnet' %Hv' Hro' Hlb' Hxlb' Hv Hl
    iapply HΦ $$ %v' %net' %xnet' [] Hro' Hlb' Hxlb' Hv Hl
    ipureintro
    obtain ⟨h1, h2, h3⟩ := Hv'
    exact ⟨h1, Hp2.1.trans h2, Hp2.2.2.1.trans h3⟩

end proof

/-! ## The iteration's end -/

attribute [-instance] pure_wp_slice_for_range

section tail
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem entsRO_open_a (s : GoSlice) (es : List EntryM) :
    entsRO (GF := GF) s es ⊢ ∃ ls : List Loc, s ↦*{DFrac.discard} ls ∗ [∗list] l;e ∈ ls;es, entRO l e := by
  unfold entsRO entsPts; exact .rfl

theorem nodeRaft_trace (γ : AntNames) (j : Fin γ.R.N) (rs : RNState) :
    nodeRaft (GF := GF) γ j rs ⊢ ⌜γ.raft.raftNames.reTrace = none⌝ ∗ nodeRaft γ j rs := by
  iintro H
  iunfold nodeRaft at H
  icases H with ⟨%x, %g, Hgv, Hsf, Hdg, Htlb, Hbud, %Hγ⟩
  isplitr
  · ipureintro; exact Hγ.1
  iunfold nodeRaft
  iexists x, g
  iframe Hgv Hsf Hdg Htlb Hbud
  ipureintro; exact Hγ

theorem nodeRaft_adv (γ : AntNames) (j : Fin γ.R.N) (rs : RNState) (t : w64) (ca : Nat) :
    nodeRaft (GF := GF) γ j rs ⊢
      nodeRaft γ j { rs with steps := [], term := t, capplied := ca, flw := false } := by
  unfold nodeRaft; exact .rfl

/-- **`loopRest` opened for the iteration's end**: the right to report, the cause and `applied`
cells, the cause cell against the view, the view's fragment, the sent lists' lower bounds, the
view's read requests, the raft ghost state; closed again at a view with the same disk, liveness,
role and configuration, `applied` its delivered length, a record with the same storage. -/
theorem loopRest_openA (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (net : List Msg) (xnet : List XMsg) (rs : RNState) :
    loopRest (GF := GF) γ j n v net xnet rs ⊢ ∃ (cl : Loc) (a : w64),
      emitOk n ∗ n.[H.node, go!"cause"] ↦ cl ∗ n.[H.node, go!"applied"] ↦ a ∗ causeOwn γ j v cl ∗
      viewFrag γ j v ∗ nodeLive γ j ∗ sentLb γ net ∗ xsentLb γ xnet ∗ readsOwn γ v ∗
      nodeRaft γ j rs ∗ ⌜uint.nat a = v.delivered.length⌝ ∗
      (∀ (v' : AntSim.NodeView) (net' : List Msg) (xnet' : List XMsg) (cl' : Loc) (a' : w64)
          (rs' : RNState),
        ⌜v'.dur = v.dur ∧ v'.alive = v.alive ∧ AntSim.roleS v' = AntSim.roleS v ∧ v'.conf = v.conf ∧
          uint.nat a' = v'.delivered.length ∧ rs'.storage = rs.storage⌝ -∗
        emitOk n -∗ n.[H.node, go!"cause"] ↦ cl' -∗ n.[H.node, go!"applied"] ↦ a' -∗
        causeOwn γ j v' cl' -∗ viewFrag γ j v' -∗ nodeLive γ j -∗ sentLb γ net' -∗
        xsentLb γ xnet' -∗ readsOwn γ v' -∗ nodeRaft γ j rs' -∗ loopRest γ j n v' net' xnet' rs') := by
  iintro Hrest
  iunfold loopRest at Hrest
  icases Hrest with ⟨%d, %ms, %hsl, %cl, %csl, %role, %applied, %si, #Hd, Hmem, Hms, Hrole, Hhs,
    Hcause, Happ, Hconf, Hv, Hl, Hdisk, Hstor, %Hsto, Hnr, %Hpv, #Hhsro, #Hcs, #Hrq, %Hc0, #Hlb,
    #Hxlb, Hco⟩
  icases nodeMemB1_emit n $$ Hmem with ⟨Hemit, Hmemc⟩
  iexists cl, applied
  iframe Hemit Hcause Happ Hco Hv Hl Hlb Hxlb Hrq Hnr
  isplitr
  · ipureintro; exact Hpv.2.2
  iintro %v' %net' %xnet' %cl' %a' %rs' %Heq Hemit Hcause Happ Hco Hv Hl #Hlb' #Hxlb' #Hrq' Hnr
  obtain ⟨hd, ha, hr, hc, happ, hst⟩ := Heq
  ihave Hmem := Hmemc $$ Hemit
  iunfold loopRest
  iexists d, ms, hsl, cl', csl, role, a', si
  rw [hd]
  iframe Hd Hmem Hms Hrole Hhs Hcause Happ Hconf Hv Hl Hdisk Hstor Hnr Hhsro Hcs Hrq' Hlb' Hxlb' Hco
  isplitr
  · ipureintro; rw [hst]; exact Hsto
  isplitr
  · ipureintro; exact ⟨by rw [ha]; exact Hpv.1, by rw [hr]; exact Hpv.2.1, happ⟩
  ipureintro; rw [hc]; exact Hc0

/-- **`nodeOwn`'s loop phase closed** (`nodeOwn_loop_open`'s converse). -/
theorem nodeOwn_loop_close (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n rn : Loc)
    (v : AntSim.NodeView) (net : List Msg) (xnet : List XMsg) (r : RState) (rs : RNState) (ip : Nat)
    (h : RsView rs v ∧ AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net xnet j v r ∧
      ip = lcpLen v.r.p.log r.p.log ∧ ByOk v.byE ∧ ViewNormal v ∧ rs.k = γ.R.k j) :
    n.[H.node, go!"rn"] ↦ rn ∗
        rawNode (GF := GF) γ.raft.raftNames γ.R.md rn (AntSim.nodeId j) rs r [] ip ∗
        loopRest γ j n v net xnet rs ⊢
      nodeOwn c γ j n v (.loop net xnet r []) := by
  iintro ⟨Hrn, Hraw, Hrest⟩
  iunfold loopRest at Hrest
  icases Hrest with ⟨%d, %ms, %hsl, %cl, %csl, %role, %applied, %si, #Hd, Hmem, Hms, Hrole, Hhs,
    Hcause, Happ, Hconf, Hv, Hl, Hdisk, Hstor, %Hsto, Hnr, %Hpv, #Hhsro, #Hcs, #Hrq, %Hc0, #Hlb,
    #Hxlb, Hco⟩
  obtain ⟨hrv, hR, hip, hby, hN, hk⟩ := h
  unfold nodeOwn
  iexists d, rn, ms, hsl, cl, csl, role, applied
  iframe Hd Hmem Hrn Hms Hrole Hhs Hcause Happ Hconf Hv Hl
  isplitr
  · ipureintro; exact hN
  dsimp only
  iframe Hdisk
  iexists si, rs, [], ip, r
  iframe Hstor Hraw Hnr Hhsro Hcs Hrq Hco Hlb Hxlb
  isplitr
  · ipureintro; exact Hsto
  isplitr
  · ipureintro; exact ⟨hrv, Hpv.1, Hpv.2.1, Hpv.2.2, hk⟩
  isplitr
  · ipureintro; exact Hc0
  ipureintro
  exact ⟨rfl, hR, rfl, hip, hby⟩

/-! ### `reads` -/

/-- **After `reads`** (its `Q`): the view `readsV v b R` (the cause reported when there were read
states), the sent lists' lower bounds grown; with no read state, the cause cell given back. -/
def afterReads (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (net₀ : List Msg)
    (xnet₀ : List XMsg) (cl : Loc) (o : Option AntCheck.Event) (L : List ReadStateM) : IProp GF :=
  iprop(∃ (b : Bool) (R : List (AntCheck.Str × Nat)) (net : List Msg) (xnet : List XMsg),
    ⌜(L ≠ [] → v.byE = go!"recv" → b = true) ∧ net₀ <+: net ∧ xnet₀ <+: xnet⌝ ∗
    readsOwn γ (readsV v b R) ∗ sentLb γ net ∗ xsentLb γ xnet ∗ viewFrag γ j (readsV v b R) ∗
    nodeLive γ j ∗
    (if L = [] then iprop(pendingCause cl o -∗ causeOwn γ j (readsV v b R) cl) else iprop(emp)))

theorem afterReads_o (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (net₀ : List Msg)
    (xnet₀ : List XMsg) (cl : Loc) (o o' : Option AntCheck.Event) {L : List ReadStateM}
    (hL : L ≠ []) :
    afterReads (GF := GF) γ j v net₀ xnet₀ cl o L = afterReads γ j v net₀ xnet₀ cl o' L := by
  unfold afterReads; simp only [hL, ↓reduceIte]

/-- **`reads`' precondition**: from the cause cell against the view, the pending report `o` and
the reports of the cause (with read states) and of each read state (`readsAfter_intro`). -/
theorem reads_pre (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (c : Loc) (γ : AntNames) (j : Fin γ.R.N)
    (hinm : ∀ S V net xnet, AntSim.AntSim γ.R γ.dec S V net xnet →
      AntSim.InMask AntSim.mskB1 γ.R net xnet)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (cl : Loc) (L : List ReadStateM)
    (hrp : v.rpend = L) (hidx : ∀ st ∈ L, uint.Z st.Index' < 2 ^ 61) :
    antCluster c γ ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗ readsOwn γ v ∗
        ([∗list] st ∈ L, readStateRaw γ.raft.raftNames st) ∗ causeOwn γ j v cl ∗ viewFrag γ j v ∗
        nodeLive γ j ⊢
      ∃ o : Option AntCheck.Event, pendingCause cl o ∗
        reports γ.strm ((if L = [] then [] else o.toList).map
            (atNode (AntSim.nameOf (AntSim.nodeId j))))
          (readsAfter γ.strm (AntSim.nameOf (AntSim.nodeId j)) L
            (afterReads γ j v net₀ xnet₀ cl o L)) := by
  iintro ⟨#Hc, #Hlb, #Hxlb, #Hro, Hst, Hco, Hvf, Hl⟩
  by_cases hL : L = []
  · subst hL
    icases causeOwn_peek γ j v cl $$ Hco with ⟨%o, Hpc, Hcl⟩
    have hv : readsV v v.told v.reads = v := by cases v; simp_all
    iexists o
    iframe Hpc
    simp only [↓reduceIte, List.map_nil, reports, readsAfter]
    iunfold afterReads
    iexists v.told, v.reads, net₀, xnet₀
    rw [hv]
    simp only [↓reduceIte]
    iframe Hro Hlb Hxlb Hvf Hl Hcl
    ipureintro
    exact ⟨fun h => absurd rfl h, List.prefix_refl _, List.prefix_refl _⟩
  · ihave Hrep := causeOwn_report h_vu h_lo c γ j v net₀ xnet₀ cl
      (readsAfter γ.strm (AntSim.nameOf (AntSim.nodeId j)) L
        (afterReads γ j v net₀ xnet₀ cl none L)) hinm $$ [Hco Hvf Hl Hst]
    · iframe Hc Hlb Hxlb Hco Hvf Hl
      iintro %b %net %xnet %Hb Hlb' Hxlb' Hvf Hl
      iapply readsAfter_intro h_vu h_lo c γ j hinm _ L { v with told := b } net xnet hrp
        (fun h => Hb.1 h) hidx
      rw [show readsOwn (GF := GF) γ { v with told := b } = readsOwn γ v from rfl]
      iframe Hc Hlb' Hxlb' Hro Hst Hvf Hl
      iintro %v' %net' %xnet' %Hv' Hro' Hlb'' Hxlb'' Hvf Hl
      have hv' : v' = readsV v b v'.reads := Hv'.1
      iunfold afterReads
      iexists b, v'.reads, net', xnet'
      rw [← hv']
      simp only [hL, ↓reduceIte]
      iframe Hro' Hlb'' Hxlb'' Hvf Hl
      ipureintro
      exact ⟨fun _ h => Hb.1 h, Hb.2.1.trans Hv'.2.1, Hb.2.2.trans Hv'.2.2⟩
    icases Hrep with ⟨%o, Hpc, Hrep⟩
    iexists o
    iframe Hpc
    simp only [hL, ↓reduceIte]
    rw [afterReads_o γ j v net₀ xnet₀ cl o none hL]
    iexact Hrep

/-- The cause cell after `reads`: as it was (no read state) or `nil` (the cause reported). -/
theorem cause_afterReads (γ : AntNames) (j : Fin γ.R.N) (n cl : Loc) (o : Option AntCheck.Event)
    (L : List ReadStateM) (v : AntSim.NodeView) (htold : L ≠ [] → AntSim.Told v) :
    (if L = [] then iprop(n.[H.node, go!"cause"] ↦ cl ∗ pendingCause cl o)
      else iprop(n.[H.node, go!"cause"] ↦ null)) ∗
      (if L = [] then iprop(pendingCause cl o -∗ causeOwn (GF := GF) γ j v cl) else iprop(emp)) ⊢
    ∃ cl' : Loc, n.[H.node, go!"cause"] ↦ cl' ∗ causeOwn γ j v cl' := by
  by_cases hL : L = []
  · simp only [hL, ↓reduceIte]
    iintro ⟨⟨Hc, Hpc⟩, Hw⟩
    iexists cl
    iframe Hc
    iapply Hw; iexact Hpc
  · simp only [hL, ↓reduceIte]
    iintro ⟨Hc, -⟩
    iexists null
    iframe Hc
    iapply (causeOwn_told (GF := GF) γ j v (htold hL))

/-! ### `applyCommitted` -/

/-- **After `applyCommitted`** (its `Q`): the view `applyV v b`, the sent lists' lower bounds
grown; with no committed entry, the cause cell given back. -/
def afterApply (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (net₀ : List Msg)
    (xnet₀ : List XMsg) (cl : Loc) (o : Option AntCheck.Event) : IProp GF :=
  iprop(∃ (b : Bool) (net : List Msg) (xnet : List XMsg),
    ⌜(v.ce ≠ [] → v.byE = go!"recv" → b = true) ∧ net₀ <+: net ∧ xnet₀ <+: xnet⌝ ∗
    sentLb γ net ∗ xsentLb γ xnet ∗ viewFrag γ j (applyV v b) ∗ nodeLive γ j ∗
    (if v.ce = [] then iprop(pendingCause cl o -∗ causeOwn γ j (applyV v b) cl) else iprop(emp)))

theorem afterApply_o (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (net₀ : List Msg)
    (xnet₀ : List XMsg) (cl : Loc) (o o' : Option AntCheck.Event) (hL : v.ce ≠ []) :
    afterApply (GF := GF) γ j v net₀ xnet₀ cl o = afterApply γ j v net₀ xnet₀ cl o' := by
  unfold afterApply; simp only [hL, ↓reduceIte]

/-- **`applyCommitted`'s precondition**: the pending report `o`; with committed entries `ce` (the
view's), the cause's report and the `apply` report (`report_upd` at `applyHstep`). -/
theorem apply_pre (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (c : Loc) (γ : AntNames) (j : Fin γ.R.N)
    (hinm : ∀ S V net xnet, AntSim.AntSim γ.R γ.dec S V net xnet →
      AntSim.InMask AntSim.mskB1 γ.R net xnet) (has : γ.R.md.async = false)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (cl : Loc) (ce : List EntryM)
    (by_ : AntCheck.Str) (hce : v.ce = ce) (hby : v.byE = by_)
    (hN : ∀ e ∈ ce, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61) :
    antCluster c γ ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗ causeOwn γ j v cl ∗ viewFrag γ j v ∗
        nodeLive γ j ⊢
      ∃ o : Option AntCheck.Event, pendingCause cl o ∗
        reports γ.strm ((if ce = [] then [] else o.toList).map
            (atNode (AntSim.nameOf (AntSim.nodeId j))))
          (if ce = [] then afterApply γ j v net₀ xnet₀ cl o else
            iprop(⧗ (ce.length + 2) -∗ reports γ.strm
              [atNode (AntSim.nameOf (AntSim.nodeId j)) (applyEvM by_ ce)]
              (afterApply γ j v net₀ xnet₀ cl o))) := by
  subst hce hby
  iintro ⟨#Hc, #Hlb, #Hxlb, Hco, Hvf, Hl⟩
  by_cases hL : v.ce = []
  · icases causeOwn_peek γ j v cl $$ Hco with ⟨%o, Hpc, Hcl⟩
    have hv : applyV v v.told = v := by unfold applyV; rw [if_pos hL]
    iexists o
    iframe Hpc
    simp only [hL, ↓reduceIte, List.map_nil, reports]
    iunfold afterApply
    iexists v.told, net₀, xnet₀
    rw [hv]
    simp only [hL, ↓reduceIte]
    iframe Hlb Hxlb Hvf Hl Hcl
    ipureintro
    exact ⟨fun h => (h rfl).elim, List.prefix_refl _, List.prefix_refl _⟩
  · ihave Hrep := causeOwn_report h_vu h_lo c γ j v net₀ xnet₀ cl
      (iprop(⧗ (v.ce.length + 2) -∗ reports γ.strm
        [atNode (AntSim.nameOf (AntSim.nodeId j)) (applyEvM v.byE v.ce)]
        (afterApply γ j v net₀ xnet₀ cl none))) hinm $$ [Hco Hvf Hl]
    · iframe Hc Hlb Hxlb Hco Hvf Hl
      iintro %b %net %xnet %Hb Hlb' Hxlb' Hvf Hl Hr
      rw [applyEv_eq _ v.byE hN]
      have htold : AntSim.Told ({ v with told := b } : AntSim.NodeView) := fun h => Hb.1 h
      iapply report_upd h_vu h_lo c γ j { v with told := b } (applyView { v with told := b })
        (AntSim.evApply (AntSim.nodeId j) v.byE v.ce) net [] xnet [] (fun G0 G => G = G0) _
        (evApply_numsOk_b1 hN) (evApply_chgOk _ _ _)
        (applyHstep j { v with told := b } net xnet hinm has hL htold)
      iframe Hc Hlb' Hxlb' Hvf Hl
      isplitl []
      · iapply factsExt_none
      isplitl [Hr]
      · rw [evApply_weight_b1]; iexact Hr
      iintro ⟨Hvf, Hl, %net', %xnet', #Hlb'', #Hxlb'', %Hp⟩
      iunfold afterApply
      iexists b, net', xnet'
      rw [show applyV v b = applyView { v with told := b } by unfold applyV; rw [if_neg hL]]
      simp only [hL, ↓reduceIte]
      iframe Hlb'' Hxlb'' Hvf Hl
      ipureintro
      exact ⟨fun _ h => Hb.1 h, Hb.2.1.trans Hp.1, Hb.2.2.trans Hp.2.2.1⟩
    icases Hrep with ⟨%o, Hpc, Hrep⟩
    iexists o
    iframe Hpc
    simp only [hL, ↓reduceIte]
    rw [afterApply_o γ j v net₀ xnet₀ cl o none hL]
    iexact Hrep

/-- The cause and `applied` cells after `applyCommitted`: as they were (no committed entry), or
`nil` and the last entry's index. -/
theorem cause_afterApply (γ : AntNames) (j : Fin γ.R.N) (n cl : Loc) (o : Option AntCheck.Event)
    (v : AntSim.NodeView) (b : Bool) (a : w64) (es : List EntryM) (hes : v.ce = es)
    (hold : es = [] → uint.nat a = (applyV v b).delivered.length)
    (hnew : es ≠ [] → uint.nat ((es.getLast?.map (·.Index')).getD a) = (applyV v b).delivered.length)
    (htold : es ≠ [] → AntSim.Told (applyV v b)) :
    (if es = [] then iprop(n.[H.node, go!"applied"] ↦ a ∗ n.[H.node, go!"cause"] ↦ cl ∗
        pendingCause cl o)
      else iprop(n.[H.node, go!"applied"] ↦ (es.getLast?.map (·.Index')).getD a ∗
        n.[H.node, go!"cause"] ↦ null)) ∗
      (if v.ce = [] then iprop(pendingCause cl o -∗ causeOwn (GF := GF) γ j (applyV v b) cl)
        else iprop(emp)) ⊢
    ∃ (cl' : Loc) (a' : w64), n.[H.node, go!"applied"] ↦ a' ∗ n.[H.node, go!"cause"] ↦ cl' ∗
      causeOwn γ j (applyV v b) cl' ∗ ⌜uint.nat a' = (applyV v b).delivered.length⌝ := by
  subst hes
  by_cases hL : v.ce = []
  · simp only [hL, ↓reduceIte]
    iintro ⟨⟨Ha, Hc, Hpc⟩, Hw⟩
    iexists cl, a
    iframe Ha Hc
    isplitl
    · iapply Hw; iexact Hpc
    ipureintro; exact hold hL
  · simp only [hL, ↓reduceIte]
    iintro ⟨⟨Ha, Hc⟩, -⟩
    iexists null, _
    iframe Ha Hc
    isplitl
    · iapply (causeOwn_told (GF := GF) γ j (applyV v b) (htold hL))
    ipureintro; exact hnew hL

/-! ### The iteration's end -/

set_option maxHeartbeats 4000000 in
/-- **`drainAdvanceB1.stmt`**: `reads` (`reads_pre`), `applyCommitted` (`apply_pre`), `Advance`
(`Reach.advance` at the view after the reports, `AdvanceEndR` and `AdvanceNoSnap` from its post,
the premise of no undecided conf entry from the view's normal entries), the `sent` loop over the
frozen messages; the loop head closed (`nodeOwn_loop_close`). -/
theorem drainAdvanceB1
    (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG))
    (h_wf : rawNode_wf.law (GF := GF) (hG := hG))
    (wp_reads : node.reads.spec (GF := GF) (hG := hG))
    (wp_applyCommitted : node.applyCommitted.spec (GF := GF) (hG := hG))
    (wp_Advance : RawNode.Advance.apiSpec (GF := GF) (hG := hG))
    (wp_sent : node.sent.spec (GF := GF) (hG := hG)) :
    drainAdvanceB1.stmt (GF := GF) (hG := hG) := by
  intro np bp rdp c n γ j I v₂ net₂ xnet₂ Φ hp2 hx2
  iintro ⟨#Hpkg, #Hc, #Hn, %Hb1, Hmid, Hsent, HΦ⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop,
    #Hbc, #Hnj, #Hmu, #Hinv, %Hfits, #Hpm, #Hrdm, #Hasi, %Hnames⟩
  obtain ⟨hs, hcc, hfw, has⟩ := rMd_flags_d Hmode.2 Hb1
  have hinm : ∀ S V net xnet, AntSim.AntSim γ.R γ.dec S V net xnet →
      AntSim.InMask AntSim.mskB1 γ.R net xnet := by
    intro S V net xnet hA
    obtain ⟨-, -, -, -, hmd', hdrv⟩ := Hmode.2
    obtain ⟨hb', -, hp', hs', -, hr', hsn', hcc', hfw', has'⟩ := Hb1
    refine inMask_b1_of ?_ ?_ ?_ ?_ ?_ hA
    · rw [hmd']; exact rnLe_scopeMd_b1 _ hfw' has' hsn' hcc'
    · rw [hdrv]; exact hb'
    · rw [hdrv]; exact hp'
    · rw [hdrv]; simp [modeDrv, hs']
    · rw [hdrv]; exact hr'
  -- the view's facts (the queue's, `NodeOk`'s)
  imod drainMid_peek h_vu h_lo h_tlp np bp rdp n γ j I v₂ net₂ xnet₂ $$ [$Hinv $Hmid] with
    ⟨%Hpk, Hmid⟩
  obtain ⟨S₀, netS, hok0⟩ := Hpk
  iunfold drainMidB1 at Hmid
  icases Hmid with ⟨Hnp, Hbp, Hrdp, Hrn, Hraw, Hrest, Hdur, Hce, #Hrs, Hrsok, %Hv⟩
  obtain ⟨hvr, hvqs, hvce, hvrp, hvby, hrv, hN, hOk⟩ := Hv
  obtain ⟨-, hk, hbyok, -, hout, hip, -, -, -, -, -, hnums, hidx⟩ := hOk
  ihave ⟨%Hwf, Hraw⟩ := h_wf γ.R.md hs hcc hfw has γ.raft.raftNames I.rn (AntSim.nodeId j) I.rs₂
    (rAccepted I.r) I.qs I.ip $$ Hraw
  have hlidx : AntSim.LogIdx I.r.p.log := logIdx_of_wf Hwf.1
  have hpre : I.rs.delivered ++ I.ce <+: I.r.p.log := hout.2.2.2.2.2.2.1
  have hfullN : AllNormal (rAccepted I.r).full := by
    have := hN.1; rw [hvr] at this; exact this
  have hlogN : AllNormal I.r.p.log := fun e he => hfullN e (List.mem_append_right _ he)
  have hceN : ∀ e ∈ I.ce, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61 := fun e he =>
    hnums.2.2.2.2 e (hpre.subset (List.mem_append_right _ he))
  have hceNorm : AllNormal I.ce := fun e he => hlogN e (hpre.subset (List.mem_append_right _ he))
  have hdlv2 : v₂.delivered = I.rs.delivered := by
    have h : I.rs.delivered ++ I.ce = v₂.delivered ++ v₂.ce := hrv.2.2.1
    rw [hvce] at h; exact (List.append_cancel_right h).symm
  have hnpv : ∀ md, md = γ.R.md → md.prevote = false → ∀ q ∈ I.qs, q.ty ≠ .preVoteResp := by
    rintro md rfl hpv q hq
    have hkp : (γ.R.k j).prevote = false := by
      cases h : (γ.R.k j).prevote
      · rfl
      · have := γ.R.hpv j h; rw [hpv] at this; cases this
    have hq2 : q ∈ v₂.qs := by rw [hvqs]; exact hq
    obtain ⟨-, -, -, -, h | h⟩ := AntSim.QsOk.old (hok0.qs q hq2) hkp
    · intro h'; rw [h.1] at h'; cases h'
    · intro h'; rw [h.1] at h'; cases h'
  icases loopRest_openA γ j n v₂ net₂ xnet₂ I.rs₂ $$ Hrest with
    ⟨%cl, %a, Hemit, Hcl, Happ, Hco, Hvf, Hl, #Hlb, #Hxlb, #Hro, Hnr, %Ha, Hclose⟩
  icases nodeRaft_trace γ j I.rs₂ $$ Hnr with ⟨%Htr, Hnr⟩
  -- `reads`
  icases reads_pre h_vu h_lo c γ j hinm v₂ net₂ xnet₂ cl I.sts hvrp hidx
    $$ [$Hc $Hlb $Hxlb $Hro $Hrsok $Hco $Hvf $Hl] with ⟨%o, Hpc, Hrep⟩
  unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.drain.tailE
  wp_auto
  wp_apply wp_reads c γ n j I.rd I.sts cl o _ $$ [$Hpkg $Hc $Hn $Hemit $Hrs $Hcl $Hpc $Hrep]
    as ⟨Hemit, -, Hcc, HQ⟩
  iunfold afterReads at HQ
  icases HQ with ⟨%b, %R, %net₃, %xnet₃, %Hb3, #Hro3, #Hlb3, #Hxlb3, Hvf, Hl, Hif⟩
  icases cause_afterReads γ j n cl o I.sts (readsV v₂ b R) (fun hL h => Hb3.1 hL h)
    $$ [$Hcc $Hif] with ⟨%cl₃, Hcl, Hco⟩
  -- `applyCommitted`
  have hce3 : (readsV v₂ b R).ce = I.ce := hvce
  have hby3 : (readsV v₂ b R).byE = I.v.byE := hvby
  icases apply_pre h_vu h_lo c γ j hinm has (readsV v₂ b R) net₃ xnet₃ cl₃ I.ce I.v.byE hce3 hby3
    hceN $$ [$Hc $Hlb3 $Hxlb3 $Hco $Hvf $Hl] with ⟨%o', Hpc, Hrep⟩
  ihave ⟨%els, #Hsl, #Hbig⟩ := entsRO_open_a _ _ $$ Hce
  wp_apply wp_applyCommitted c γ n j I.v.byE I.rd.CommittedEntries' DFrac.discard els I.ce a cl₃ o' _
    hceNorm $$ [$Hpkg $Hc $Hn $Hemit $Hsl $Hbig $Happ $Hcl $Hpc $Hrep] as ⟨Hemit, -, -, Hcc, HQ⟩
  iunfold afterApply at HQ
  icases HQ with ⟨%b', %net₄, %xnet₄, %Hb4, #Hlb4, #Hxlb4, Hvf, Hl, Hif⟩
  have hne3 : ∀ h : I.ce ≠ [], (readsV v₂ b R).ce ≠ [] := fun h h' => h (hce3.symm.trans h')
  icases cause_afterApply γ j n cl₃ o' (readsV v₂ b R) b' a I.ce hce3
    (fun h => by unfold applyV; rw [if_pos (hce3.trans h)]; exact Ha)
    (fun h => by
      unfold applyV; rw [if_neg (hne3 h)]
      show _ = (v₂.delivered ++ v₂.ce).length
      rw [hdlv2, hvce]; exact lastIdx_len hlidx hpre h a)
    (fun h => by
      unfold applyV; rw [if_neg (hne3 h)]
      exact fun hb => Hb4.1 (hne3 h) hb)
    $$ [$Hcc $Hif] with ⟨%cl₄, %a₄, Happ, Hcl, Hco, %Ha4⟩
  obtain ⟨b'', U, M, hv4⟩ := applyV_eq (readsV v₂ b R) b'
  -- `Advance`
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave Hret : loanRet (GF := GF) I.rs₂ $$ []
  · unfold loanRet DrainIterB1.rs₂; simp only; iempintro
  ihave #HA1 : □ (⌜I.rs₂.slent = none⌝ -∗ cfgKeepIn γ.raft.raftNames I.rs₂.mode I.rs₂.delivered
      I.rs₂.capplied I.rs₂.delivered.length I.rs₂.cfg) $$ []
  · imodintro; iintro -
    iapply cfgKeepIn_noConf
    exact noConf_of_normal (fun e he => hlogN e (hpre.subset he)) _ _
  ihave Hdur : durFrags (GF := GF) γ.raft.raftNames (AntSim.nodeId j) I.rs₂.bw $$ [Hdur]
  · rw [show I.rs₂.bw = I.W from rfl]; iexact Hdur
  wp_apply wp_Advance γ.R.md hs hcc hfw has γ.raft.raftNames I.rn (AntSim.nodeId j) I.rs₂
      (rAccepted I.r) I.qs I.ip I.rd (fun _ => rfl) rfl (fun h => absurd Htr h) hnpv
      $$ [$Hrpkg $Hraw $Hret $HA1 $Hdur] as %t %ca %r' %ip' ⟨Hraw, -, -, -, -, %Hend⟩
  obtain ⟨hadvF, hipF⟩ := Hend γ.R.md rfl Htr
  obtain ⟨hadvR, hns⟩ := hadvF (AdmFold γ.dec γ.R.c0) γ.dec
    (CfgKeep.of_noConf (noConf_of_normal hfullN _ _))
  have hrs2 : advRS I.rs₂ t ca = { I.rs₂ with steps := [], term := t, capplied := ca, flw := false } :=
    advRS_none t ca rfl
  have hR : AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₄ xnet₄ j
      (applyV (readsV v₂ b R) b') r' := by
    rw [hv4]
    refine .advance _ _ hp2 hx2 rfl rfl
      (by show AntSim.DrainBy v₂.byE; rw [hvby]; exact drainBy_of_byOk hbyok) ?_ ?_
    · show AdvanceEndR _ _ _ _ v₂.r v₂.qs r'
      rw [hvr, hvqs, ← hk]; exact hadvR
    · intro _
      show AntSim.AdvanceNoSnap _ _ _ _ v₂.r v₂.qs r'
      rw [hvr, hvqs, ← hk]; exact advanceNoSnap_of (hns hs)
  have hrv4 : RsView (advRS I.rs₂ t ca) (applyV (readsV v₂ b R) b') := by
    rw [hrs2, hv4]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrv
    refine ⟨h1, h2, ?_, rfl, h5, rfl, h7, h8⟩
    show I.rs.delivered ++ I.ce = (v₂.delivered ++ v₂.ce) ++ []
    rw [List.append_nil]; exact h3
  have hip4 : ip' = lcpLen (applyV (readsV v₂ b R) b').r.p.log r'.p.log := by
    rw [hipF hip, hv4]
    show min I.ip (lcpLen (rAccepted I.r).p.log r'.p.log) = lcpLen v₂.r.p.log r'.p.log
    rw [hvr]
    show min I.ip (lcpLen I.r.p.log r'.p.log) = lcpLen I.r.p.log r'.p.log
    rw [hip]
    exact Nat.min_eq_right (lcpLen_le_left _ _)
  ihave Hnr' : nodeRaft (GF := GF) γ j (advRS I.rs₂ t ca) $$ [Hnr]
  · rw [hrs2]; iapply nodeRaft_adv; iexact Hnr
  ihave #Hro4 : readsOwn (GF := GF) γ (applyV (readsV v₂ b R) b') $$ []
  · rw [hv4]
    iunfold readsOwn
    iunfold readsOwn at Hro3
    iexact Hro3
  ihave Hrest := Hclose $$ %(applyV (readsV v₂ b R) b') %net₄ %xnet₄ %cl₄ %a₄ %(advRS I.rs₂ t ca) []
    Hemit Hcl Happ Hco Hvf Hl Hlb4 Hxlb4 Hro4 Hnr'
  · ipureintro
    exact ⟨by rw [hv4], by rw [hv4], by rw [hv4]; rfl, by rw [hv4], Ha4, by rw [hrs2]⟩
  ihave Hown := nodeOwn_loop_close c γ j n I.rn (applyV (readsV v₂ b R) b') net₄ xnet₄ r'
    (advRS I.rs₂ t ca) ip'
    ⟨hrv4, hR, hip4, by rw [hv4]; show ByOk v₂.byE; rw [hvby]; exact hbyok,
      by rw [hv4]; exact hN, by rw [hrs2]; exact hk⟩ $$ [$Hrn $Hraw $Hrest]
  -- the `sent` loop
  iunfold drainSentB1 at Hsent
  icases Hsent with ⟨Hsl2, Hall, %Hns⟩
  wp_apply (wp_slice_range_ro (V := Loc) _ I.rd.Messages' (I.ms.map QMsg.loc) (DFrac.own 1) _
    (fun _ => iprop(∃ x : Loc, m_ptr ↦ x ∗ np ↦ n ∗
      [∗list] q ∈ I.ms, msgPtsC (GF := GF) q.loc DFrac.discard DFrac.discard false q.st)))
    $$ Hsl2 [Hnp m Hall]
  · iexists _
    iframe
  · imodintro
    iintro %i %x %hx ⟨%x0, Hm, Hnp, Hall⟩ Hs
    have hi : i < I.ms.length := by
      have := (List.getElem?_eq_some_iff.1 hx).1; simpa using this
    have hxe : x = I.ms[i].loc := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi] at hx
      exact (Option.some.inj hx).symm
    subst hxe
    icases (BigSepL.bigSepL_lookup_acc (Φ := fun _ (q : QMsg) =>
      msgPtsC (GF := GF) q.loc DFrac.discard DFrac.discard false q.st)
      (List.getElem?_eq_getElem hi)).1 $$ Hall with ⟨Hq, Hback⟩
    wp_auto
    wp_apply wp_sent n I.ms[i].loc DFrac.discard DFrac.discard false I.ms[i].st
      (Hns _ (List.getElem_mem hi)) $$ [$Hpkg $Hq] as Hq
    ihave Hall := Hback $$ %I.ms[i] Hq
    rw [List.set_getElem_self]
    isplitr
    · ipureintro; rfl
    iframe Hs
    iexists I.ms[i].loc
    iframe
  iintro ⟨%x, Hm, Hnp, Hall⟩ Hs
  iapply HΦ $$ %(applyV (readsV v₂ b R) b') %net₄ %xnet₄ %r'
  iframe Hnp Hbp Hown
  ipureintro; rw [hv4]; exact hvby

end tail

end AntHarness
end EtcdGrove
end Perennial
