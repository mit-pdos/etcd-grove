/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__readIndex.lean`: the `readreq`
report (`report_updG`: the view records the context with the committed length of raft's facts at the
report, `antSim_readreq_in`; its receipts the emit resolution's and `readOk`'s), `RawNode.ReadIndex`
with `readOk`'s fresh token and read update, a read credit (`rdMinter`, the receipt of `ReadIndex`'s
resolution) and the committed log of those facts (`raftFactsOwn`'s `isCommitted`), the view noted
(`view_input`), the drain from its loop head (`Reach.input` at `.readIndex`: `RecvEndR` at `readMsg`, the
log kept), through `input` (by `read`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__readIndex
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__input
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__emit
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessStep
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReport
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Reads
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Outbox
public import Perennial.Golang.Theory.String
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

theorem atNode_readReqEvM (id : w64) (ctx : List w8) :
    atNode (AntSim.nameOf id) (readReqEvM ctx) = AntSim.evReadReq id ctx := rfl

theorem evReadReq_nums (id : w64) (ctx : List w8) : (AntSim.evReadReq id ctx).NumsOk := by
  simp [AntCheck.Event.NumsOk, AntSim.evReadReq, AntCheck.optNumOk]

theorem evReadReq_chg (id : w64) (ctx : List w8) : (AntSim.evReadReq id ctx).ChgOk 0 := by
  simp [AntCheck.Event.ChgOk, AntCheck.Event.entryLists, AntSim.evReadReq]

theorem evReadReq_weight (id : w64) (ctx : List w8) : (AntSim.evReadReq id ctx).weight = 2 := by
  simp [AntCheck.Event.weight, AntCheck.Event.size, AntSim.evReadReq]

/-- The view after the `readreq` report at raft's facts `G`. -/
abbrev readreqView (v : AntSim.NodeView) (ctx : List w8) (G : AntSim.RaftFacts) : AntSim.NodeView :=
  { v with reads := AntSim.readsAsk v.reads (ctx, G.committed.length) }

theorem mskB1_le' : AntSim.mskB1 ≤ AntSim.mskB1 := by
  simp [LE.le, AntSim.SimMask.Le, AntSim.RnMode.Le, AntSim.NodeK.Le, AntSim.BLe]

/-- **The `readreq` report's Sim step** (`report_updG`'s `hstep`, raft's facts kept): `antSim_readreq_in`
at `mskB1` (the run within it: `runInMask`). -/
theorem readreq_hstep (h_mask : runInMask.law AntSim.mskB1) (γ : AntNames) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (ctx : List w8)
    (hrun : InScope γ.scope γ.mode ∧ ModeRun γ.scope γ.mode γ.R) (hb1 : DrainB1 γ.scope γ.mode)
    (hI : v.Idle) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin γ.R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntRun γ.R γ.dec evs S V net xnet →
      AntSim.SimPre γ.R γ.dec S V net xnet evs G0 → (∀ i : Fin γ.R.N, (V i).r.full ∈ G0.logs) →
      G = G0 → V j = v → ([] : List Msg) <+: net → ([] : List XMsg) <+: xnet →
      AntSim.SimStep γ.R γ.dec evs G (AntSim.evReadReq (AntSim.nodeId j) ctx)
          (AntSim.setV V j (readreqView v ctx G)) (net ++ []) (xnet ++ []) ∧
        AntSim.RaftLaws G ∧ ∀ i : Fin γ.R.N, (AntSim.setV V j (readreqView v ctx G) i).r.full ∈ G.logs := by
  intro evs S V net xnet G0 G hR hpre hlogs hQ hVj _ _
  subst hQ hVj
  simp only [List.append_nil]
  refine ⟨AntSim.antSim_readreq_in AntSim.mskB1 mskB1_le' γ.R γ.dec S V net xnet evs G j ctx
    (h_mask γ evs S V net xnet hrun.1 hrun.2 hb1 hR) hpre hI, hpre.2.2.1, ?_⟩
  intro i
  unfold AntSim.setV
  by_cases h : i = j
  · subst h; simp only [ite_true]; exact hlogs i
  · simp only [h, ite_false]; exact hlogs i

end pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- **Node `j` between inputs, opened for a read** (`nodeOwn_idle_open` with the right to emit,
`nodeMemB1`'s `emitOk`, and the view's pending reads' raft requests, `readsOwn`): the loop head after
the input `inp` at the view with any reads `rd`, given their requests. -/
theorem nodeOwn_read_open (hbp : rnBudget_persistent.law (GF := GF)) (c : Loc) (γ : AntNames)
    (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) :
    nodeOwn (GF := GF) c γ j n v .idle ⊢
      ∃ (rn : Loc) (rs : RNState),
        emitOk n ∗ n.[H.node, go!"rn"] ↦ rn ∗
        rawNode γ.raft.raftNames γ.R.md rn (AntSim.nodeId j) rs v.r [] v.r.p.log.length ∗
        rnTermLB γ.raft rs.tc ∗ □ rnBudget γ.raft ∗
        ⌜γ.raft.raftNames.reTrace = none ∧ γ.raft.raftNames.reCfg = γ.R.voters0 ∧
          γ.raft.raftNames.maxData = none⌝ ∗
        n.[H.node, go!"cause"] ↦ (null : Loc) ∗ viewFrag γ j v ∗ nodeLive γ j ∗ readsOwn γ v ∗
        ⌜RsView rs v ∧ v.Idle ∧ PIdle rs v.r.p ∧ ViewNormal v ∧ rs.k = γ.R.k j⌝ ∗
        (∀ (rd : List (AntCheck.Str × Nat)) (rs' : RNState) (r₁ : RState) (ip' : Nat)
            (inp : AntSim.Input) (net₀ : List Msg) (xnet₀ : List XMsg) (xs₁ : List XMsg) (cl : Loc),
          emitOk n -∗ n.[H.node, go!"rn"] ↦ rn -∗
          rawNode γ.raft.raftNames γ.R.md rn (AntSim.nodeId j) rs' r₁ [] ip' -∗
          ⌜rs'.storage = rs.storage ∧ rs'.dur = rs.dur ∧ rs'.k = rs.k ∧
            RsView rs' ({ v with reads := rd }.noteInput inp) ∧
            AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j ({ v with reads := rd }.noteInput inp) r₁ ∧
            ip' = lcpLen v.r.p.log r₁.p.log ∧ ByOk inp.byE ∧
            ViewNormal ({ v with reads := rd }.noteInput inp)⌝ -∗
          rnTermLB γ.raft rs'.tc -∗
          n.[H.node, go!"cause"] ↦ cl -∗ viewFrag γ j ({ v with reads := rd }.noteInput inp) -∗
          nodeLive γ j -∗ sentLb γ net₀ -∗ xsentLb γ xnet₀ -∗
          causeOwn γ j ({ v with reads := rd }.noteInput inp) cl -∗ readsOwn γ { v with reads := rd } -∗
          nodeOwn c γ j n ({ v with reads := rd }.noteInput inp) (.loop net₀ xnet₀ r₁ xs₁)) := by
  unfold nodeOwn
  iintro ⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, #Hd, Hmem, Hrn, Hms, Hrole, Hhs, Hcause,
    Happ, Hconf, Hv, Hl, %HN, Hdisk, %si, %rs, %qs, %ip, %r, Hstor, %Hsto, Hraw, Hnr, %Hrv, #Hhsro,
    #Hcs, #Hrq, %Hc0, %Hph⟩
  obtain ⟨hI, rfl, rfl, rfl, hP, rfl⟩ := Hph
  iunfold nodeMemB1 at Hmem
  icases Hmem with ⟨%mhs, %rhs, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, Hem⟩
  icases nodeRaft_open hbp γ j rs $$ Hnr with ⟨Htc, #Hb, %Hst, Hnrc⟩
  iexists rn, rs
  iframe Hem Hrn Hraw Htc Hcause Hv Hl Hrq
  isplitr
  · iexact Hb
  isplitr
  · ipureintro; exact Hst
  isplitr
  · ipureintro; exact ⟨Hrv.1, hI, hP, HN, Hrv.2.2.2.2⟩
  iintro %rd %rs' %r₁ %ip' %inp %net₀ %xnet₀ %xs₁ %cl' Hem Hrn Hraw %Hf Htc Hcause Hv Hl Hlb Hxlb Hco #Hrq'
  obtain ⟨hsto, hdur, hk, hrv, hR, hip, hby, hN'⟩ := Hf
  ihave Hnr := Hnrc $$ %rs' %hdur Htc
  iexists d, rn, ms, hsl, cl', csl, role, applied
  iframe Hd Hrn Hms Hrole Hhs Hcause Happ Hconf Hv Hl
  isplitl [M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 Hem]
  · iunfold nodeMemB1
    iexists mhs, rhs
    iframe M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 Hem
  isplitr
  · ipureintro; exact hN'
  dsimp only
  rw [show (({ v with reads := rd } : AntSim.NodeView).noteInput inp).dur = v.dur from rfl]
  iframe Hdisk
  iexists si, rs', [], ip', r₁
  rw [show readsOwn (GF := GF) γ (({ v with reads := rd } : AntSim.NodeView).noteInput inp) =
    readsOwn γ { v with reads := rd } from rfl]
  iframe Hstor Hraw Hnr Hhsro Hcs Hrq' Hlb Hxlb Hco
  ipureintro
  exact ⟨by rw [hsto]; exact Hsto, ⟨hrv, Hrv.2.1, Hrv.2.2.1, Hrv.2.2.2.1, by rw [hk]; exact Hrv.2.2.2.2⟩,
    Hc0, rfl, hR, rfl, hip, hby⟩

/-- `readsTrunc` keeps a sublist (the oldest dropped). -/
theorem bigSepL_readsTrunc {A : Type} (Φ : A → IProp GF) (l : List A) :
    ([∗list] x ∈ l, Φ x) ⊢ [∗list] x ∈ AntSim.readsTrunc l, Φ x := by
  unfold AntSim.readsTrunc
  split
  · cases l with
    | nil => iintro H; simp only [List.drop_nil]; iexact H
    | cons a l =>
      show ([∗list] x ∈ a :: l, Φ x) ⊢ [∗list] x ∈ l, Φ x
      iintro H
      icases (BigSepL.bigSepL_cons).1 $$ H with ⟨-, Hl⟩
      iexact Hl
  · iintro H; iexact H

/-- **The reads after a `readreq`, their requests** (`readsAsk`: the new one appended, the oldest
dropped past `MaxReads`). -/
theorem readsOwn_ask (γ : AntNames) (v : AntSim.NodeView) (p : AntCheck.Str × Nat) (Lc : List EntryM)
    (hp : p.2 ≤ Lc.length) :
    readsOwn (GF := GF) γ v ∗ readReq γ.raft.raftNames p.1 Lc ⊢
      readsOwn γ { v with reads := AntSim.readsAsk v.reads p } := by
  unfold readsOwn
  refine BIBase.Entails.trans ?_ (bigSepL_readsTrunc (GF := GF) (fun q : AntCheck.Str × Nat =>
    iprop(∃ Lc : List EntryM, readReq γ.raft.raftNames q.1 Lc ∗ ⌜q.2 ≤ Lc.length⌝)) (v.reads ++ [p]))
  iintro ⟨#Hr, #Hq⟩
  iapply (BigSepL.bigSepL_snoc).2
  isplitl [Hr]
  · iexact Hr
  · iexists Lc; iframe Hq; ipureintro; exact hp

end laws

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.readIndex.wp_proof
    (wp_ReadIndex : RawNode.ReadIndex.apiSpec (GF := GF) (hG := hG))
    (wp_input : node.input.spec (GF := GF) (hG := hG))
    (wp_emit : node.emit.spec (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_vu : view_update.law (GF := GF) (hG := hG))
    (h_lo : nodeLive_over.law (GF := GF) (hG := hG))
    (h_quiet : antSim_quiet_in.law AntSim.mskB1) (h_mask : runInMask.law AntSim.mskB1) :
    node.readIndex.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v q ctx
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok, %Hb1, Hrok, %Hreads⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm, #Hrdm, -⟩
  obtain ⟨hs, hcc, hfw, has⟩ := rMd_flags Hmode.2 Hb1
  have hrd : γ.R.md.reads = true := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hR, -⟩ := Hmode.1
    rw [Hmode.2.2.2.2.2.1]; exact hR Hreads
  iunfold readOk at Hrok
  icases Hrok with ⟨-, Hfr, #Hau, Hrk⟩
  icases nodeOwn_read_open h_bp c γ j n v $$ Hown with
    ⟨%rn, %rs, Hem, Hrnf, Hraw, Htc, #Hb, %Hst, Hcause, Hv, Hl, #Hrq, %Hpr, Hclose⟩
  obtain ⟨hrv0, hI, hP, hN0, hk⟩ := Hpr
  -- the `readreq` report
  wp_take_receipt as Hr1
  ihave Hw : ⧗ (AntSim.evReadReq (AntSim.nodeId j) ctx).weight $$ [Hr1 Hrk]
  · rw [evReadReq_weight]
    iapply (receipt_add (GF := GF) 1 1).2
    iframe Hr1 Hrk
  ihave Hev : eventOwn «$a0_ptr» (readReqEvM ctx) $$ [«$a0»]
  · iunfold eventOwn
    iexists _
    iframe «$a0»
    simp only [readReqEvM, AntCheck.fieldRO]
    isplitr
    · ipureintro
      simp only [AntCheck.fieldRel, AntCheck.fieldIs, AntCheck.fieldZ, AntCheck.hasBit, AntCheck.fB,
        AntCheck.fA, AntCheck.fBy, AntCheck.fRole, AntCheck.fTerm, AntCheck.fVote, AntCheck.fCommit,
        AntCheck.fFirst, AntCheck.fLastIndex, AntCheck.fLastTerm, AntCheck.fApplied, AntCheck.fSnap,
        AntCheck.fW, AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx]
      decide
    simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing, AntCheck.fMsg,
      AntCheck.fCause]
    itrivial
  imod (monoListLbOwn_nil (GF := GF) (A := Msg) γ.sent) with #Hlb0
  imod (monoListLbOwn_nil (GF := GF) (A := XMsg) γ.xsent) with #Hxlb0
  ihave #Hlb : sentLb γ [] $$ []
  · iunfold sentLb; iexact Hlb0
  ihave #Hxlb : xsentLb γ [] $$ []
  · iunfold xsentLb; iexact Hxlb0
  ihave #Hfx := factsExt_none (GF := GF) γ
  wp_apply wp_emit c γ n j «$a0_ptr» (readReqEvM ctx)
      (iprop(∃ G : AntSim.RaftFacts, raftFactsOwn γ.raft.raftNames G ∗
        viewFrag γ j (readreqView v ctx G) ∗ nodeLive γ j))
    $$ [$Hpkg $Hc $Hn Hem $Hev Hw Hv Hl] as ⟨Hem, %G, #HF, Hv, Hl⟩
  · iframe Hem
    rw [atNode_readReqEvM]
    iapply report_updG h_vu h_lo c γ j v (readreqView v ctx) (AntSim.evReadReq (AntSim.nodeId j) ctx)
      [] [] [] [] (fun G0 G => G = G0) _ (evReadReq_nums _ _) (evReadReq_chg _ _)
      (readreq_hstep h_mask γ j v ctx Hmode Hb1 hI)
    iframe Hc Hlb Hxlb Hfx Hw Hv Hl
    iintro %G %_ #HF Hv Hl -
    iexists G
    iframe HF Hv Hl
  iunfold raftFactsOwn at HF
  icases HF with ⟨-, -, -, -, #HL0, -⟩
  -- `ReadIndex`
  have hI1 : (readreqView v ctx G).Idle := hI
  have hrv : RsView rs (readreqView v ctx G) := hrv0
  have hN : ViewNormal (readreqView v ctx G) := hN0
  try wp_auto
  wp_apply +noauto wp_string_to_bytes as %ds ⟨Hds, -⟩
  imod ownSlice_persist $$ Hds with #Hds
  wp_take_receipt as Hr2
  iunfold rdMinter at Hrdm
  imod Hrdm $$ Hr2 with Hcred
  wp_apply wp_ReadIndex γ.R.md hs hcc hfw has γ.raft.raftNames rn (AntSim.nodeId j) rs v.r []
      v.r.p.log.length ds ctx (fun _ => iprop(True)) G.committed (fun md h => by rw [h]; exact hrd)
      Hst.1 $$ [$Hrpkg $Hraw $Hds $Hfr $Hau $HL0 $Hcred] as %r' ⟨Hraw, #Hrqr, %Hend⟩
  · ipureintro; intro b hb; rw [Hst.2.2] at hb; cases hb
  have hRE := Hend γ.R.md rfl (AdmFold γ.dec γ.R.c0)
  rw [hk] at hRE
  have hlog : r'.p.log = v.r.p.log := by
    have h := AntSim.readIdxEnd_keep (AntSim.recvEnd_readMsg hRE.1)
    rw [h]
  icases Hrqr with ⟨%Lc, %hLc, #Hrr, -⟩
  ihave #Hrq1 := readsOwn_ask (GF := GF) γ v (ctx, G.committed.length) Lc hLc.length_le $$ [Hrq Hrr]
  · iframe Hrq Hrr
  -- the view notes the input
  ihave #Hsw : □ (∀ m, ⌜AntSim.Input.readIndex ctx = .recv m⌝ -∗ sentW (GF := GF) γ m) $$ []
  · imodintro; iintro %m %h; cases h
  ihave #Hsx : □ (∀ x, ⌜AntSim.Input.readIndex ctx = .recvX x⌝ -∗ xsentW (GF := GF) γ x) $$ []
  · imodintro; iintro %x %h; cases h
  imod view_input h_vu h_lo AntSim.mskB1 h_quiet h_mask γ j (readreqView v ctx G) (.readIndex ctx) Hmode Hb1
      (show AntSim.mskB1.md.reads = true from rfl) hI1 (fun m h => by cases h) (fun x h => by cases h)
      $$ [Hv Hl] with ⟨%net₀, %xnet₀, Hv, Hl, #Hlb, #Hxlb, -⟩
  · iframe Hinv Hsw Hsx Hv Hl
  ihave Hco := causeOwn_noRecv (GF := GF) γ j (readreqView v ctx G) (.readIndex ctx)
    (by simp only [AntSim.Input.byE]; decide)
  have hR : AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j
      ((readreqView v ctx G).noteInput (.readIndex ctx)) r' :=
    AntSim.Reach.input _ (.readIndex ctx) r' hI1 rfl rfl rfl (fun m h => by cases h) (fun x h => by cases h)
      ⟨hrd, hRE⟩
  have hip' : v.r.p.log.length = lcpLen (readreqView v ctx G).r.p.log r'.p.log := by
    show v.r.p.log.length = lcpLen v.r.p.log r'.p.log
    rw [hlog, lcpLen_self]
  ihave Hown := Hclose $$ %(AntSim.readsAsk v.reads (ctx, G.committed.length)) %_ %r' %_ %(.readIndex ctx)
    %net₀ %xnet₀ %([] : List XMsg) %null Hem Hrnf Hraw
    %(⟨rfl, rfl, rfl, rsView_noteInput (.readIndex ctx) hrv rfl rfl rfl rfl rfl rfl, hR, hip',
      .inr (.inr (.inr (.inr (.inl rfl)))), viewNormal_noteInput hN (fun _ h => by cases h)⟩)
    Htc Hcause Hv Hl Hlb Hxlb Hco Hrq1
  try wp_auto
  have hin := wp_input c γ n j ((readreqView v ctx G).noteInput (.readIndex ctx)) net₀ xnet₀ r' [] q slice.nil
  rw [show ((readreqView v ctx G).noteInput (.readIndex ctx)).byE = go!"read" from rfl] at hin
  wp_apply hin $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as %v' ⟨Hown, Had, Htok, %Hby⟩
  · ipureintro; exact Hb1
  try wp_auto
  iapply HΦ
  iframe Hown Had Htok
  ipureintro; exact Hby

end proof

end AntHarness
end EtcdGrove
end Perennial
