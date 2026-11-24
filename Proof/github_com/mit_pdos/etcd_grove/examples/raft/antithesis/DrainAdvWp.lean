/-
Lean-first (no Rocq counterpart). #33 S4: `DrainPhases.lean`'s `drainAdvance.stmt` proved: the end of
`Cluster.drain`'s iteration (`Cluster.drain.tailE`): with committed entries, the cause reported
(`reportCause`), the `apply` report recorded (`report_au` at `applyStep`, nothing added to raft's
facts: `factsExt_none`), `n.applied` set; then `RawNode.Advance` (`AdvanceEnd`), the next loop head
(`rsView_next`, `reach_next`, `nodeOwn_loop_close`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainPhases
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainReports
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__reportCause
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder__record
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.entriesOf
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRunLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainMsgs
-- (#33 S4) `selfOut_reach`, for `qs_noPreVote`
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyKind
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

/-- The `apply` report's numbers, its entries' within `2 ^ 61`. -/
theorem evApply_numsOk {id : w64} {b : AntCheck.Str} {ce : List EntryM}
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
    split <;> exact ⟨by word, by word⟩

theorem evApply_weight (id : w64) (b : AntCheck.Str) (ce : List EntryM) :
    (AntSim.evApply id b ce).weight = ce.length + 2 := by
  simp [AntSim.evApply, AntCheck.Event.weight, AntCheck.Event.size, AntSim.logOf]

theorem reportedView_byE (v : AntSim.NodeView) : (reportedView v).byE = v.byE := by
  unfold reportedView; split <;> rfl

theorem reportedView_ce (v : AntSim.NodeView) : (reportedView v).ce = v.ce := by
  unfold reportedView; split <;> rfl

theorem reportedView_told (v : AntSim.NodeView) :
    (reportedView v).byE = go!"recv" → (reportedView v).told = true := by
  unfold reportedView
  split
  · intro _; rfl
  · rename_i h; intro hb; simp only [not_and, Bool.not_eq_false] at h; exact h hb

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem entsRO_open (s : GoSlice) (es : List EntryM) :
    entsRO (GF := GF) s es ⊢ ∃ ls : List Loc, s ↦*{DFrac.discard} ls ∗ [∗list] l;e ∈ ls;es, entRO l e := by
  unfold entsRO entsPts; exact .rfl

theorem nodeRaft_facts (γ : AntNames) (j : Fin 3) (rs : RNState) :
    nodeRaft (GF := GF) γ j rs ⊢
      ⌜γ.raft.raftNames.reTrace = none ∧ γ.raft.raftNames.reCfg = AntSim.voters3⌝ ∗ nodeRaft γ j rs := by
  unfold nodeRaft
  iintro ⟨%x, %g, Hgv, Hsf, Hdg, Htc, Hb, %Hst⟩
  isplitr
  · ipureintro; exact ⟨Hst.1, Hst.2.1⟩
  iexists x, g
  iframe
  ipureintro; exact Hst

theorem nodeRaft_congr (γ : AntNames) (j : Fin 3) {rs rs' : RNState} (h1 : rs'.dur = rs.dur)
    (h2 : rs'.tc = rs.tc) : nodeRaft (GF := GF) γ j rs ⊢ nodeRaft γ j rs' := by
  unfold nodeRaft; rw [h1, h2]

/-- (#33 S4, 2026-11-24) **No queued pre-vote response after a `Ready`**: the queue is the outbox's
self-addressed messages (`hqs`), which are a leader's self-acknowledgement or a candidate's self-vote
(`selfOut_reach`, from the view's `NodeOk`). `RawNode.Advance.form`'s premise. -/
theorem qs_noPreVote {S : AntCheck.State} {net net' : List Msg} {j : Fin 3} {v : AntSim.NodeView}
    {ps : PState} {qs : List Msg}
    (hR : AntSim.Reach (AntSim.nodeId j) net v ps) (hnet : AntSim.NetOk S net')
    (hv : AntSim.NodeOk S net' j v) (hpre : net <+: net')
    (hqs : qs ≡ₚ ps.outbox.filter (fun m => decide (m.dst = AntSim.nodeId j))) :
    ∀ q ∈ qs, q.ty ≠ .preVoteResp := by
  obtain ⟨hd, -, -, -, hQ, -, -, hlo, -⟩ := hv
  have hX : v.ps.outbox = [] := hd.2.2.2.2.2.2.1
  have hin : ∀ m ∈ net', AntSim.InMsg m := fun m hm => ⟨(hnet.1 m hm).1, hnet.2.2.1 m hm⟩
  have hqsS : ∀ q ∈ v.qs, AntSim.SelfMsg (AntSim.nodeId j) v.ps.term q := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hQ q hq
    exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩
  have hso := AntSim.selfOut_reach (hR.mono hpre) hX hlo hin hqsS
  intro q hq
  obtain ⟨hmem, hd'⟩ := List.mem_filter.1 (hqs.mem_iff.1 hq)
  rcases hso q hmem (of_decide_eq_true hd') with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simp [pselfAck]
  · simp [Msg.plain]

/-- **`Advance` and the next loop head** (both arms of the `apply` report end here): from the view
`v₃` with nothing pending or unreported (its committed entries the iteration's, delivered),
`RawNode.Advance` steps the queue (`AdvanceEnd`), and the loop head closes at `v₃`. -/
theorem drainAdvance_close
    (wp_Advance : RawNode.Advance.apiSpec (GF := GF) (hG := hG))
    (cp np bp rdp c n : Loc) (γ : AntNames) (j : Fin 3) (I : DrainIter) (v₃ : AntSim.NodeView)
    (net₃ : List Msg) (Φ : val → IProp GF)
    (hps : v₃.ps = pAccepted I.ps₁) (hqs : v₃.qs = I.qs) (hce : v₃.ce = []) (hpend : v₃.pend = [])
    (hdl : v₃.delivered = I.v.delivered ++ I.ce) (hby : v₃.byE = I.v.byE)
    (hOk : I.Ok (AntSim.nodeId j)) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      cp ↦ c ∗ np ↦ n ∗ bp ↦ I.v.byE ∗ rdp ↦ I.rd ∗
      n.[H.node, go!"rn"] ↦□ I.rn ∗
      rawNode γ.raft.raftNames I.rn (AntSim.nodeId j) I.rs₂ (pAccepted I.ps₁) I.qs I.ip ∗
      loopRest γ j n v₃ net₃ I.rs₂ ∗ durFrags γ.raft.raftNames (AntSim.nodeId j) I.W ∗
      (∀ (v' : AntSim.NodeView) (net' : List Msg) (ps' : PState),
        cp ↦ c ∗ np ↦ n ∗ bp ↦ I.v.byE ∗ nodeOwn c γ j n v' (.loop net' ps') ∗
          ⌜v'.byE = I.v.byE⌝ -∗ Φ executeVal) ⊢
    WP (App (Val doExecute)
      (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.raft.v3.Ready.ty))) (Val #rdp))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.RawNode.ty) go!"Advance"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.raft.v3.RawNode.ty)))) (App (Val (GoInstruction (StructFieldRef github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty go!"rn"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty)))) (Val #np))))) (Var "$a0"))))
      {{ Φ }} := by
  iintro ⟨#Hpkg, Hcp, Hnp, Hbp, Hrdp, #Hrn, Hraw, Hrest, #Hdur, HΦ⟩
  obtain ⟨hrv, hvce, hout, hqsp, hip, hbyI, hnums, hnpv⟩ := hOk
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iunfold loopRest at Hrest
  icases Hrest with ⟨%ms, %si, %cl, %applied, #Hms, Hbs, %Hsto, Hnr, Hrole, Hterm, Hvote, Hcommit,
    Happ, Hcause, Hv, Hl, #Hlb, Hco, %Hby, %HN⟩
  icases nodeRaft_facts γ j I.rs₂ $$ Hnr with ⟨%Hst, Hnr⟩
  ihave Hret : loanRet (GF := GF) I.rs₂ $$ []
  · unfold loanRet DrainIter.rs₂; simp only; iempintro
  ihave #HA1 : □ (⌜I.rs₂.slent = none⌝ -∗ undecFree γ.raft.raftNames I.rs₂.mode I.rs₂.delivered
      I.rs₂.capplied I.rs₂.delivered.length) $$ []
  · imodintro; iintro -
    iapply undecFree_noConf
    intro k e _ _ hk hc
    have hl : AllNormal I.ps₁.log := by have := HN.1; rw [hps] at this; exact this
    have hmem : e ∈ I.ps₁.log :=
      hout.2.2.2.2.2.2.1.subset (List.mem_of_getElem? hk : e ∈ I.rs.delivered ++ I.ce)
    have hn := hl e hmem
    unfold IsConfEnt at hc
    rcases hc with h | h <;> rw [hn] at h <;> simp at h
  ihave #Hdur' : durFrags (GF := GF) γ.raft.raftNames (AntSim.nodeId j) I.rs₂.bw $$ []
  · rw [show I.rs₂.bw = I.W from rfl]; iexact Hdur
  wp_auto
  wp_apply wp_Advance γ.raft.raftNames I.rn (AntSim.nodeId j) I.rs₂ (pAccepted I.ps₁) I.qs I.ip I.rd
      (fun _ => rfl) rfl (fun h => absurd Hst.1 h) (fun _ => hnpv) $$ [$Hrpkg $Hraw $Hret $HA1 $Hdur']
      as %t %ca %ps' %ip' ⟨Hraw, -, -, -, -, %Hend⟩
  obtain ⟨hadv, hipo⟩ := Hend trivial Hst.1
  have hR := reach_next (net := net₃) hps hpend hce (hby ▸ hbyI)
    (by rw [hqs, ← rnCfg_cfgM3 Hst.2]; exact hadv) hip (hipo hip)
  have hrv' : RsView (advRS I.rs₂ t ca) v₃ := rsView_next hrv hvce hout hps hdl hce
  have hadvn : advRS I.rs₂ t ca = { I.rs₂ with steps := [], term := t, capplied := ca, flw := false } :=
    advRS_none _ _ rfl
  ihave Hnr := nodeRaft_congr γ j (rs := I.rs₂) (rs' := advRS I.rs₂ t ca) (by rw [hadvn])
    (by rw [hadvn]) $$ Hnr
  ihave Hown := nodeOwn_loop_close c γ j n v₃ net₃ ps' I.rn (advRS I.rs₂ t ca) ip' hrv' hR.1 hR.2
    $$ [Hraw Hbs Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl Hco]
  · iframe Hrn Hraw
    iunfold loopRest
    iexists ms, si, cl, applied
    iframe Hms Hbs Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl Hlb Hco
    ipureintro
    exact ⟨by rw [hadvn]; exact Hsto, Hby, HN⟩
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro; exact hby

theorem drainAdvance
    (wp_record : Recorder.record.spec (GF := GF) (hG := hG))
    (wp_reportCause : Cluster.reportCause.spec (GF := GF) (hG := hG))
    (wp_entriesOf : entriesOf.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Advance : RawNode.Advance.apiSpec (GF := GF) (hG := hG)) :
    drainAdvance.stmt (GF := GF) (hG := hG) := by
  intro cp np bp rdp c n γ j I v₂ net₂ Φ hpend
  iintro ⟨#Hpkg, #Hc, #Hn, Hmid, HΦ⟩
  unfold drainMid
  icases Hmid with ⟨Hcp, Hnp, Hbp, Hrdp, #Hrn, Hraw, Hrest, #Hdur, #Hce, %Hv⟩
  unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.drain.tailE
  icases typedPointsto_not_null_dup _ _ _ $$ Hrdp with ⟨Hrdp, %Hrnn⟩
  iStructNamed Hrdp
  wp_pure
  wp_auto
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, #Hr, #Hrec, #Hro, %Hlen, #Hn0, #Hn1, #Hn2,
    #Hstop, #Hbc, #Hnj, #Hinv, %Hfits⟩
  ihave #Hn' := Hn
  iunfold nodeRO at Hn'
  icases Hn' with ⟨%ch, #Hid, #Hname, #Hin, #Hbag⟩
  ihave %Hcelen := entsPts_len _ _ _ $$ Hce
  ihave ⟨%els, #Hsl, #Hbig⟩ := entsRO_open _ _ $$ Hce
  ihave %Hll := entsBig_length $$ Hbig
  wp_if_destruct
  · iunfold loopRest at Hrest
    icases Hrest with ⟨%ms, %si, %cl, %applied, #Hms, Hbs, %Hsto, Hnr, Hrole, Hterm, Hvote, Hcommit,
      Happ, Hcause, Hv, Hl, #Hlb, Hco, %Hby, %HN⟩
    (try wp_auto)
    wp_apply wp_reportCause c γ n j v₂ cl $$ [$Hpkg $Hc $Hn $Hcause $Hco $Hv $Hl] as ⟨Hcause, Hco, Hv, Hl⟩
    (try wp_auto)
    have hcepos : 0 < I.ce.length := by
      have h1 := Hcelen.1; have h2 := Hif
      have : sint.Z (W64 0) = 0 := by word
      rw [this] at h2; rw [h1]
      show 0 < (sint.Z I.rd.CommittedEntries'.len).toNat
      omega
    obtain ⟨e0, he0⟩ : ∃ e0, I.ce[0]? = some e0 := ⟨_, List.getElem?_eq_getElem hcepos⟩
    ihave ⟨%l0, %hl0, #He0⟩ := entsBig_lookup els I.ce 0 e0 he0 $$ Hbig
    ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
    · iPkgInit
    have hz : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z I.rd.CommittedEntries'.len :=
      ⟨by word, Hif⟩
    simp only [hz, _root_.and_self, ↓reduceIte]
    wp_apply +noauto (wp_load_slice_index (t := go.GoType.PointerType raftpb.Entry.ty)
      I.rd.CommittedEntries' (sint.Z (W64 0)) els DFrac.discard l0 (by word)) $$ [] as -
    · iframe Hsl; ipureintro; exact hl0
    wp_take_receipt as Hr1
    wp_apply +noauto wp_GetIndex.1 l0 DFrac.discard e0 $$ [$Hpb $He0] as -
    wp_take_receipt as Hr2
    have hceNorm : AllNormal I.ce := by
      have hl : AllNormal I.ps₁.log := by
        have := HN.1; rw [Hv.1] at this; exact this
      exact ce_normal hl Hv.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
    wp_apply +noauto wp_entriesOf I.rd.CommittedEntries' DFrac.discard els I.ce hceNorm
      $$ [$Hpkg $Hsl $Hbig] as %out ⟨-, #Hout, Hr3⟩
    (try wp_auto)
    obtain ⟨hps, hqs, hce2, hdl, hby2, hOk⟩ := Hv
    have hOk' := hOk
    obtain ⟨hrv, hvce, hout, hqsp, hip, hbyI, hnums, hnpv⟩ := hOk
    have hceN : ∀ e ∈ I.ce, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61 := fun e he =>
      hnums.2.2.2.2 e (hout.2.2.2.2.2.2.1.subset (List.mem_append_right _ he))
    have hfirst : sint.Z e0.Index' = AntSim.firstOf I.ce := by
      obtain ⟨e1, rest, hcons⟩ : ∃ e1 rest, I.ce = e1 :: rest := by
        cases h : I.ce with
        | nil => rw [h] at hcepos; simp at hcepos
        | cons a b => exact ⟨a, b, rfl⟩
      rw [hcons] at he0
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he0
      subst he0
      have := (hceN e1 (by rw [hcons]; exact List.mem_cons_self)).2
      rw [hcons]; simp only [AntSim.firstOf]; word
    have hev : AntSim.evApply (AntSim.nodeId j) (reportedView v₂).byE (reportedView v₂).ce =
        AntSim.evApply (AntSim.nodeId j) I.v.byE I.ce := by
      rw [reportedView_byE, reportedView_ce, hby2, hce2]
    ipersist «$a0»
    ihave #Hev : AntCheck.eventRO «$a0_ptr» (AntSim.evApply (AntSim.nodeId j) I.v.byE I.ce) $$ []
    · iunfold AntCheck.eventRO
      iexists _
      iframe «$a0»
      simp only [AntSim.evApply, AntCheck.fieldRO]
      isplitr
      · ipureintro
        simp only [AntCheck.fieldRel, AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy,
          AntCheck.fRole, AntCheck.fTerm, AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst,
          AntCheck.fLastIndex, AntCheck.fLastTerm, AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW,
          AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx, hfirst]
        and_intros <;> first | rfl | decide
      simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing,
        AntCheck.fMsg, AntCheck.fCause]
      rw [← entOfE_logOf (fun e he => (hceN e he).1)]
      iframe Hout
      ipureintro
      and_intros <;> decide
    have hce' : (reportedView v₂).ce ≠ [] := by
      rw [reportedView_ce, hce2]; intro h; rw [h] at hcepos; simp at hcepos
    have hstep := applyStep GF j (reportedView v₂) net₂ hce' (reportedView_told v₂)
      (by rw [hev]; exact evApply_numsOk hceN) Hfits
    rw [hev] at hstep
    ihave HAU := report_au γ j (reportedView v₂)
      { reportedView v₂ with delivered := (reportedView v₂).delivered ++ (reportedView v₂).ce, ce := [] }
      (AntSim.evApply (AntSim.nodeId j) I.v.byE I.ce) net₂ [] (fun _ => True) hstep $$ [Hv Hl]
    · iframe Hinv Hlb Hv Hl
      imodintro
      iapply factsExt_none
    ihave Hrc : ⧗ (AntSim.evApply (AntSim.nodeId j) I.v.byE I.ce).weight $$ [Hr1 Hr2 Hr3]
    · rw [evApply_weight]
      iapply (receipt_add (GF := GF) (I.ce.length + 1) 1).2
      iframe Hr2
      iapply (receipt_add (GF := GF) I.ce.length 1).2
      iframe Hr3 Hr1
    wp_apply +noauto wp_record γ.strm r «$a0_ptr» (AntSim.evApply (AntSim.nodeId j) I.v.byE I.ce) _
      $$ [$Hpkg $Hrec $Hev $Hrc $HAU] as ⟨Hv, Hl, %net₃, #Hlb3, %Hpre3⟩
    (try wp_auto)
    have hlenZ : sint.Z (I.rd.CommittedEntries'.len - W64 1) = (I.ce.length - 1 : Nat) := by
      have h1 := Hcelen.1
      have h2 : sint.Z (W64 0) = 0 := by word
      rw [h2] at Hif
      rw [show sint.nat I.rd.CommittedEntries'.len = (sint.Z I.rd.CommittedEntries'.len).toNat from rfl] at h1
      word
    have hz' : 0 ≤ sint.Z (I.rd.CommittedEntries'.len - W64 1) ∧
        sint.Z (I.rd.CommittedEntries'.len - W64 1) < sint.Z I.rd.CommittedEntries'.len := by
      have h1 := Hcelen.1
      rw [show sint.nat I.rd.CommittedEntries'.len = (sint.Z I.rd.CommittedEntries'.len).toNat from rfl] at h1
      rw [hlenZ]; omega
    simp only [hz', _root_.and_self, ↓reduceIte]
    obtain ⟨eL, heL⟩ : ∃ eL, I.ce[I.ce.length - 1]? = some eL :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave ⟨%lL, %hlL, #HeL⟩ := entsBig_lookup els I.ce _ eL heL $$ Hbig
    wp_apply +noauto (wp_load_slice_index (t := go.GoType.PointerType raftpb.Entry.ty)
      I.rd.CommittedEntries' _ els DFrac.discard lL hz'.1) $$ [] as -
    · iframe Hsl; ipureintro; rw [hlenZ]; simp only [Int.toNat_natCast]; exact hlL
    (try wp_auto)
    wp_apply wp_GetIndex.1 lL DFrac.discard eL $$ [$Hpb $HeL] as -
    (try wp_auto)
    ihave Hrdp : (rdp ↦ I.rd : IProp GF) $$ [SoftState HardState ReadStates Entries Snapshot
        CommittedEntries Messages MustSync]
    · iapply typedPointsto_combine _ _ _ Hrnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    obtain ⟨b, hb, hbt⟩ : ∃ b, reportedView v₂ = { v₂ with told := b } ∧
        (v₂.byE = go!"recv" → b = true) := by
      unfold reportedView
      split
      · exact ⟨true, rfl, fun _ => rfl⟩
      · rename_i h
        refine ⟨v₂.told, rfl, fun hb => ?_⟩
        simp only [not_and, Bool.not_eq_false] at h; exact h hb
    rw [hb]
    iapply drainAdvance_close wp_Advance cp np bp rdp c n γ j I
      { v₂ with told := b, delivered := v₂.delivered ++ v₂.ce, ce := [] } net₃ Φ hps hqs rfl hpend
      (by simp only; rw [hdl, hce2]) hby2 hOk'
    iframe Hpkg Hcp Hnp Hbp Hrdp Hrn Hraw Hdur HΦ
    iunfold loopRest
    iexists ms, si, null, eL.Index'
    iframe Hms Hbs Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl Hlb3
    isplitr
    · ipureintro; exact Hsto
    isplitl
    · unfold causeOwn
      rw [if_neg]
      · ipureintro; rfl
      · rintro ⟨h1, h2⟩
        simp only at h1 h2
        rw [hbt h1] at h2; cases h2
    ipureintro
    exact ⟨Hby, HN⟩
  · ihave Hrdp : (rdp ↦ I.rd : IProp GF) $$ [SoftState HardState ReadStates Entries Snapshot
        CommittedEntries Messages MustSync]
    · iapply typedPointsto_combine _ _ _ Hrnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    obtain ⟨hps, hqs, hce2, hdl, hby2, hOk⟩ := Hv
    have hce0 : I.ce = [] := by
      have h1 := Hcelen.1
      have h2 : sint.Z (W64 0) = 0 := by word
      rw [h2] at Hif
      rw [show sint.nat I.rd.CommittedEntries'.len = (sint.Z I.rd.CommittedEntries'.len).toNat from rfl] at h1
      apply List.eq_nil_of_length_eq_zero; omega
    iapply drainAdvance_close wp_Advance cp np bp rdp c n γ j I v₂ net₂ Φ hps hqs
      (by rw [hce2, hce0]) hpend (by rw [hdl, hce0, List.append_nil]) hby2 hOk
    iframe Hpkg Hrn Hdur
    iframe

end proof

end AntHarness
end EtcdGrove
end Perennial
