/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.newNode
public import Spec.go_etcd_io.raft.v3.node__run
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvAdvance
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Proof.go_etcd_io.raft.v3.ApiVocab
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView
import Proof.go_etcd_io.raft.v3.InvApiDec
import Proof.go_etcd_io.raft.v3.InvApiJoin
import all Proof.go_etcd_io.raft.v3.InvNodeRule
import Proof.go_etcd_io.raft.v3.SnapValidCert
import Proof.go_etcd_io.raft.v3.StepGhostMode
import Proof.go_etcd_io.raft.v3.InvStorageRead
import Proof.go_etcd_io.raft.v3.ConfchangeApiImpl
import Proof.go_etcd_io.raft.v3.ConfchangeApi

@[expose] public section

noncomputable section


namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

What the proof over raft's internals shows, from which the wrapper (below) derives the spec. Its documentation, as when it was the spec (until 2026-10-28):
-/

/-! Lean-first (no Rocq counterpart).

## `RestartNode(c)` (node.go:281)

`NewRawNode(c)` (its premises: a node of a new cluster, `Spec/NewRawNode.lean`) in a
`node` whose goroutine `run` it starts, for the cluster's term budget `bud`
(`budget_alloc`, `InvNode.lean`). It returns the node (`isNodeChan`, persistent: what
`Propose`, `Step`, `Tick` and `Ready` take) and the driver's token (`nodeDriverChan`, at
the empty committed log: what `node_ready_receive` and `Advance` take). Since 2026-10-10
also the cluster's proposed slices (`propDataInv`, allocated once with the raft ghost
state), which `isNodeChan` keeps with the commit invariant. Since 2026-10-15 (stage N) in either
mode (`md`, `NewRawNode`'s `rnInit`: statically `ownRaftGhost` at the initial state, dynamically
B5's `ownRaftGhostR` at `rinit c0`), and with the driver's view of the configuration
(`nodeCfg`, at index `0` and the initial configuration) for `ApplyConfChange` and `Advance`.

raft v3.7 (2026-10-16, stage R5): `NewRawNode`'s premises as they are now (the storage's
`InitialState` in `newRaft`'s D7 shape, the conf state's record `csm`; 2026-10-16, stage R6b: the
conf state's `AutoLeave` cell set or not, `csPts cs □ csm al`); **no proposed slices'
invariant** (D6: an entry's data is its bytes; until then `inv propDataN (propDataInv γ)`, which
`isNodeChan` kept).
-/

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. (raft-final phase 1, 2026-10-29: over `NewRawNode`'s boot bundle, raft's
storage names `sn` and frame `R`/`R'`; until then raft's view of an empty storage with an
`InitialState` closure, and `NodeNames.snapIn`, deleted.) -/
private abbrev RestartNode.specRaw : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (bud : BudgetNames) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk) (sn : StorNames)
    -- (raft-final phase 2) the node's configuration names, allocated by the caller, so that the
    -- node's table entry (`nodeTabOk`) exists before the storage's contract is read
    (gdlm gcap gccq gcam glive : GName)
    (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM) (R R' : IProp GF),
  -- `NewRawNode`'s premises
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  -- `ReadOnlySafe` (2026-10-12)
  cv.ReadOnlyOption' = W64 0 →
  -- conf-change validation on (2026-10-13; `newRaft`'s premise)
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  -- (2026-10-25, T-M M2b: pre-vote either way; 2026-10-17 to 2026-10-25 off in the dynamic mode,
  -- which did not model pre-candidates; until then off in either mode)
  cv.Applied' = W64 0 →
  σ.prev = entryID.mk (W64 0) (W64 0) → σ.ents = [] → σ.pend = [] →
  σ.fr = 0 → σ.sg = 0 → σ.dt = ∅ →
  HsEmpty hs →
  -- (2026-10-16, stage R5) the conf state's record `csm`, as `NewRawNode`'s
  csm.Voters' ≠ [] → csm.Voters'.Nodup → W64 0 ∉ csm.Voters' →
  (csm.Voters'.length : Int) ≤ 2 ^ 62 →
  csm.VotersOutgoing' = [] →
  csm.Learners' = [] →
  csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  -- (2026-10-29, stage U4: only in the static mode; a dynamic node, a newcomer, need not be one of
  -- the conf state's voters)
  (md = .static → γ.reCfg = GMap.listToSet csm.Voters') →
  (md = .static → cv.ID' ∈ csm.Voters') →
  -- (2026-10-25, T-M M2c: `StepDownOnRemoval` either way; 2026-10-15 to 2026-10-25 on in the dynamic
  -- mode)
  -- (D19i part 1) the floor not raised yet: the storage's view, fresh to raft
  σ.fl = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗ R ∗
      -- (raft-final phase 1) `NewRawNode`'s boot bundle
      (□ {{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 1) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 0) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #()))
         {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
            hsOpt hp hs ∗ csPts cs DFrac.discard csm al ∗
            |={⊤}=> isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ ∗ R' }}) ∗
      -- (2026-10-15, stage N) the ghost state in the mode `md` (`NewRawNode`'s `rnInit`; until
      -- then `ownRaftGhost γ cv.ID' initPState`, the static mode's)
      rnInit γ md cv.ID' (GMap.listToSet csm.Voters') ∗ isCommitted γ [] ∗
      -- the cluster's term budget
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 0) ∗
      -- (D22 S-b′3, 2026-10-20) the storage's certificate link (`certLink`; raft-final phase 1: of
      -- the storage names, U8 v2)
      certLink γ sn ∗
      -- (raft-final phase 2) the configuration names' initial states
      monoListAuthOwn gdlm 1 ([] : List EntryM) ∗ monoListLbOwn gdlm ([] : List EntryM) ∗
      dghostVar gcap (DFrac.own 1) ((0 : Nat), cfgState (GMap.listToSet csm.Voters') ∅) ∗
      dghostVar gccq (DFrac.own 1) ((0 : Nat), cfgState (GMap.listToSet csm.Voters') ∅) ∗
      monoNatAuthOwn gcam 1 0 ∗ monoNatLbOwn gcam 0 ∗ dghostVar glive (DFrac.own 1) false }}
    (App (Val #(functions RestartNode [])) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (γn : NodeNames) (n : Loc),
        ⌜γn.raft = γ ∧ γn.bud = bud ∧ γn.stor = interface.ok si ∧ γn.mode = md ∧ γn.sn = sn ∧
         nd = interface.mkOk (go.GoType.PointerType node.ty) #n ∧
         γn.dlm = gdlm ∧ γn.cap = gcap ∧ γn.ccq = gccq ∧ γn.cam = gcam ∧ γn.live = glive⌝ ∗
        -- (raft-final phase 1) the frame `InitialState` gave back
        R' ∗
        isNodeChan γn cv.ID' n ∗ nodeDriverChan γn cv.ID' n [] hsZero ∗
        -- (2026-10-29, stage U9a) the client's half of `live`, for `Stop`
        nodeLiveRaw γn 1 ∗
        -- (2026-10-15, stage N) the driver's view of the configuration: the initial one
        nodeCfg γn 0 (cfgState (GMap.listToSet csm.Voters') ∅) }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `NewRawNode` (its result the node open, `rawNodeFresh`, closed here with the ghost state in
the mode `md`: 2026-10-16, stage R8b; until then `NewRawNode` closed it), `newNode`, then the
node's ghost state: the channels' hand-shakes (with `P := False` on those nobody sends on), the
tick channel's invariant (no credit yet), `dlv` and `rof`; `run` takes its halves. (Raft v3.7,
stage R5: `NewRawNode`'s premises over the conf state's record `csm` and D7's `InitialState`; no
proposed slices' invariant (D6).) -/
private theorem RestartNode.wp_raw
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG))
    (wp_newNode : newNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    RestartNode.specRaw (GF := GF) (hG := hG) := by
  intro γ md bud c cv lok si sn γdlm γcap γccq γcam γlive σ hs csm R R' P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14
    P15 P16 P17 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 P28
  wp_start as ⟨Hc, #Hlg, HR, #HFI, #HLI, #HInit, Hghost, #Hcommitted, #Hbud, #Hlb0, #Hcl, Hdlm,
    #Hdlb, Hcap, Hccq, Hcam, #Hcamlb, Hlive⟩
  ihave #Hcinv : raftCommitInv γ $$ [Hghost]
  · cases md with
    | static =>
      iunfold rnInit at Hghost
      iapply ownRaftGhost_inv γ cv.ID' initPState $$ Hghost
    | dyn dec c0 h0 h1 =>
      iunfold rnInit at Hghost
      icases Hghost with ⟨-, Hg⟩
      iunfold ownRaftGhostR at Hg
      icases Hg with ⟨Hg, -⟩
      iapply ownRaftGhost_inv_md $$ Hg
  -- (2026-10-19, D21 M3) a fresh node with nothing committed: not in the no-snapshot mode
  ihave %Hns0 : ⌜γ.reNoSnap = false⌝ $$ [Hghost]
  · cases md with
    | static =>
      iunfold rnInit at Hghost
      icases ownRaftGhost_noSnap_of_commit γ cv.ID' initPState rfl $$ Hghost with ⟨%H, -⟩
      ipureintro; exact H
    | dyn dec c0 h0 h1 =>
      iunfold rnInit at Hghost
      icases Hghost with ⟨-, Hg⟩
      iunfold ownRaftGhostR at Hg
      icases Hg with ⟨Hg, -⟩
      icases ownRaftGhost_noSnap_of_commit γ cv.ID' _ rfl $$ Hg with ⟨%H, -⟩
      ipureintro; exact H
  -- (2026-10-20, D22 S-c) nor in the no-transfer mode (`RaftNames.reNoXfer_ok`)
  ihave %Hnx0 : ⌜γ.reNoXfer = false⌝ $$ [Hghost]
  · cases md with
    | static =>
      iunfold rnInit at Hghost
      icases ownRaftGhost_noXfer_of_commit γ cv.ID' initPState rfl $$ Hghost with ⟨%H, -⟩
      ipureintro; exact H
    | dyn dec c0 h0 h1 =>
      iunfold rnInit at Hghost
      icases Hghost with ⟨-, Hg⟩
      iunfold ownRaftGhostR at Hg
      icases Hg with ⟨Hg, -⟩
      icases ownRaftGhost_noXfer_of_commit γ cv.ID' _ rfl $$ Hg with ⟨%H, -⟩
      ipureintro; exact H
  wp_auto
  wp_apply wp_NewRawNode c cv lok si sn σ hs csm R R' P1 P2 P3 P4 P5 P6 P7 P8 P9 P10
    P11 P12 P13 P14 P15 P16 P17 P19 P20 P21 P22 P23 P24 P25 P28
    $$ [$Hc $Hlg $HR $HFI $HLI $HInit] as %rn %err ⟨HR', %s, Hfresh, %Herr, %Hsn2⟩
  subst Herr
  -- the node closed with the ghost state, in the mode `md` (2026-10-16, stage R8b: `NewRawNode`
  -- leaves it open, `rawNodeFresh`)
  iunfold rawNodeFresh at Hfresh
  icases Hfresh with ⟨%rnv, %sv, %hprev, Hfresh⟩
  iNamed Hfresh
  obtain ⟨Hp, Hse, Hue, Hsd, Hcm, Hap, Hapg, Hun, Hsn, Hsg, Hdtk⟩ := Hlog
  obtain ⟨Hlsn, Hgsn⟩ := Hsn2
  -- (D22l) `prevHardSt` zero, `RNState.phs`'s default
  ihave #Hhard0 := prevHS_of_zero γ _ _ Hhz $$ Hhard
  obtain ⟨Ht0, Hv0, Hr, -, -, -⟩ := Hterm0
  have Hdlen0 : ([] : List EntryM).length = (uint.Z s.logst.applying).toNat := by
    rw [Hapg]; rfl
  -- (2026-10-17) the term ceiling at the term, `0`
  have Hrnpv : ∀ fp, RNPv
      { delivered := [], unpersisted := [], steps := [], term := W64 0,
        storage := interface.ok si, sn := sn, mode := md,
        cfg := cfgState (GMap.listToSet csm.Voters') ∅ } fp s := fun _ =>
    ⟨fun _ _ h => (by rw [Hr] at h; cases h), by rw [Hgh], by rw [Ht0, Hgh]; exact Int.le_refl _,
      fun h => (by rw [Hr] at h; cases h), fun _ => Hr⟩
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  icases ownRaftPhysC_sdr _ rnv.raft' cv.ID' s $$ Hphys with ⟨#Hsd0, Hphys⟩
  -- (D19i part 1) the floor at most `applying`, which is `applied` (`0`)
  icases ownRaftPhysC_log_same _ rnv.raft' cv.ID' s $$ Hphys with ⟨HL, Hback0⟩
  icases ownRaftLog_fl _ _ $$ HL with ⟨%Hflk, HL⟩
  ihave Hphys := Hback0 $$ HL
  have HrnflR : ∀ rs0 : RNState, rs0.steps = [] → RNFl rs0 s := fun rs0 _ =>
    ⟨fun _ => by rw [Hap]; rw [Hapg] at Hflk; exact Hflk.1,
     fun h => absurd h (by rw [Hap, Hapg]; exact Int.lt_irrefl _)⟩
  ihave Hrn : ownRawNode γ rn cv.ID'
      { delivered := [], unpersisted := [], steps := [], term := W64 0,
        storage := interface.ok si, sn := sn, mode := md,
        cfg := cfgState (GMap.listToSet csm.Voters') ∅ } $$ [Hrn Hphys Hghost Hsteps Hsteps_cap]
  · cases md with
    | static =>
      have P25 := P26 rfl
      have P26 := P27 rfl
      iunfold rnInit at Hghost
      ihave #Hsdrf : sdrOk (GF := GF) rnv.raft' RNMode.static $$ []
      · iunfold sdrOk; iexists s.sdr; iexact Hsd0
      ihave Hphys := ownRaftPhysC_toS $$ Hphys
      ihave Hphys : ownRaftPhys γ.reCfg rnv.raft' cv.ID' s $$ [Hphys]
      · rw [P25]; iexact Hphys
      iapply ownRawNode_intro_static γ rn cv.ID'
          { delivered := [], unpersisted := [], steps := [], term := W64 0,
            storage := interface.ok si, sn := sn, mode := .static,
            cfg := cfgState (GMap.listToSet csm.Voters') ∅ }
          s initPState rnv sv hprev [] rfl Hrel
          (by rw [P25]; exact (GMap.elem_of_list_to_set _ _).2 P26) Hasync
          Hdlen0 (by rw [Hun]) (fun _ => Hsn) trivial
          (by rw [Ht0]) ⟨by rw [Hsg], by rw [Hlsn]⟩ (Hrnpv []) (by rw [Hgh]) (by rw [Hgh])
          (uint_Z_nonneg _) (HrnflR _ rfl)
          -- (D22 S-d3a) no snapshot lent
          ⟨by rw [Hgh]; try rfl, fun _ => ⟨by rw [Hgh]; try rfl, fun _ _ _ _ h => (by cases h)⟩,
            fun l h => (by cases h)⟩
          (SdtTie.of_none (by rw [Hdtk]; rfl))
          (TrackedOk.of_sub (by rw [Hdom, P25]; exact GMap.subseteq_refl _)
            (by rw [P25]; exact (GMap.elem_of_list_to_set _ _).2 P26))
          (by unfold NsLink; rw [Hgh, Hns0])
          $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard0 Hsteps Hsteps_cap [] Hcommitted [] [] [] [] [] []
      · iapply pendList_nil
      · iapply ackInv_none; intro _ _ _ _ h; cases h
      · ipureintro; trivial
      · rw [Hgsn]; iexact Hcl
      · rw [Hsn]; iapply snapLocOk_none
      · -- (raft-final phase 2) a fresh node: no leader, no transfer record
        iapply leadW_none γ cv.ID' _ (by rw [Hrel.1]; rfl)
      · unfold xfW; rw [Hgh]
        iapply BigSepM.bigSepM_empty.2; iempintro
    | dyn dec c0 h0 h1 =>
      iunfold rnInit at Hghost
      icases Hghost with ⟨%HD, Hgr⟩
      obtain ⟨HD, rfl⟩ := HD
      ihave #Hsdrf : sdrOk (GF := GF) rnv.raft'
          (RNMode.dyn dec (cfgState (GMap.listToSet csm.Voters') ∅) h0 h1) $$ []
      · iunfold sdrOk; iexists s.sdr; iexact Hsd0
      have Hro : rOf s ⟨0, cfgState (GMap.listToSet csm.Voters') ∅, [], ∅⟩ =
          rinit (cfgState (GMap.listToSet csm.Voters') ∅) := by
        unfold rOf rinit pciR
        rw [Hrel.1, Hap, Hsn]
        simp [Hr]
      have Hdiff : domSet s.progress \ GMap.listToSet csm.Voters' = ∅ := by
        rw [Hdom]
        apply GMap.set_eq; intro k
        rw [GMap.elem_of_difference]
        constructor
        · rintro ⟨h1, h2⟩; exact absurd h1 h2
        · intro h; exact absurd h (GMap.not_elem_of_empty _)
      ihave Hghost : ownStepGhost γ
          (RNMode.toG (.dyn dec (cfgState (GMap.listToSet csm.Voters') ∅) h0 h1)
            ⟨0, cfgState (GMap.listToSet csm.Voters') ∅, [], ∅⟩)
          (CfgM.simple (GMap.listToSet csm.Voters') (domSet s.progress \ GMap.listToSet csm.Voters'))
          cv.ID' s $$ [Hgr]
      · simp only [RNMode.toG]
        iapply (ownStepGhost_dyn γ dec _ h0 _ _ cv.ID' s).2
        rw [Hro, effDec_empty]
        iframe Hgr
        isplitr
        · ipureintro
          refine ⟨HD, ?_, by unfold NsLink; rw [Hgh, Hns0]⟩
          rw [Hdiff]; rfl
        isplitr; · iapply decLb_empty
        isplitr; · rw [Hgsn]; iexact Hcl
        isplitr; · iapply leadW_none γ cv.ID' _ (by rw [Hrel.1]; rfl)
        unfold xfW; rw [Hgh]
        iapply BigSepM.bigSepM_empty.2; iempintro
      iapply ownRawNode_intro γ rn cv.ID'
          { delivered := [], unpersisted := [], steps := [], term := W64 0,
            storage := interface.ok si, sn := sn, mode := .dyn dec (cfgState (GMap.listToSet csm.Voters') ∅) h0 h1,
            cfg := cfgState (GMap.listToSet csm.Voters') ∅ }
          s _ [] rnv sv hprev [] Hrel.2 (fun h => by cases h) Hasync
          Hdlen0 (by rw [Hun]) (fun _ => Hsn) trivial
          (by rw [Ht0]) ⟨by rw [Hsg], by rw [Hlsn]⟩ (Hrnpv _) (by rw [Hgh]) (by rw [Hgh])
          (uint_Z_nonneg _) (HrnflR _ rfl)
          -- (D22 S-d3a) no snapshot lent
          ⟨by rw [Hgh]; try rfl, fun _ => ⟨by rw [Hgh]; try rfl, fun _ _ _ _ h => (by cases h)⟩,
            fun l h => (by cases h)⟩
          (SdtTie.of_none (by rw [Hdtk]; rfl)) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard0 Hsteps Hsteps_cap [] Hcommitted [] [] []
      · iapply pendList_nil
      · iapply ackInv_none; intro _ _ _ _ h; cases h
      · ipureintro; trivial
      · rw [Hsn]; iapply snapLocOk_none
  wp_auto
  wp_apply wp_newNode rn as %nv ⟨%Hnvrn, Hchans⟩
  ipersist n
  -- the node's ghost state
  imod dghostVar_alloc ((([] : List EntryM), hsZero) : List EntryM × HardStateM) with ⟨%γdlv, Hdlv⟩
  icases dghostVar_halves _ _ $$ Hdlv with ⟨Hdlv1, Hdlv2⟩
  imod dghostVar_alloc (([], [], [], hsZero, none) : List EntryM × List EntryM ×
    List EntryM × HardStateM × Option SnapLoan) with ⟨%γrof, Hrof⟩
  icases dghostVar_halves _ _ $$ Hrof with ⟨Hrof1, Hrof2⟩
  -- (2026-10-15, stage N) the configuration shared with the driver
  icases dghostVar_halves _ _ $$ Hcap with ⟨Hcap1, Hcap2⟩
  icases dghostVar_halves _ _ $$ Hccq with ⟨Hccq1, Hccq2⟩
  -- (D19i part 1) the driver's request on `advancec`
  imod dghostVar_alloc (((none, none) : AdvReq)) with ⟨%γreq, Hreq⟩
  icases dghostVar_halves _ _ $$ Hreq with ⟨Hreq1, Hreq2⟩
  -- (2026-10-29, stage U9a) whether the node is stopped: the client's half and `run`'s
  icases dghostVar_halves _ _ $$ Hlive with ⟨Hlive1, Hlive2⟩
  unfold newNodeChans
  icases Hchans with ⟨%γp, %γr, %γc, %γcs, %γrd, %γa, %γt, %γd, %γs, %γst, #Hcp, Hop, #Hcr, Hor,
    #Hcc, Hoc, #Hccs, Hocs, #Hcrd, Hord, #Hca, Hoa, #Hct, Hot, #Hcd, Hod, #Hcs, Hos, #Hcst, Host⟩
  let γn : NodeNames := { raft := γ, id := cv.ID', bud := bud, stor := interface.ok si, propc := γp,
                          recvc := γr, confc := γc, confstatec := γcs, readyc := γrd, advancec := γa, tick := γt,
                          done := γd, stop := γs, status := γst, dlv := γdlv, rof := γrof,
                          mode := md, dlm := γdlm, cap := γcap, ccq := γccq, cam := γcam, req := γreq,
                          sn := sn, live := γlive }
  ihave Hlive1 : nodeLiveRaw (GF := GF) γn 1 $$ [Hlive1]
  · unfold nodeLiveRaw; iexact Hlive1
  ihave Hlive2 : nodeLiveRaw (GF := GF) γn 1 $$ [Hlive2]
  · unfold nodeLiveRaw; iexact Hlive2
  imod start_handshake nv.propc' (propP γn) iprop(True) γp $$ Hcp Hop with #Hhp
  imod start_handshake nv.recvc' (netP γn cv.ID') iprop(True) γr $$ Hcr Hor with #Hhr
  imod start_handshake nv.confc' (confcP γn) iprop(True) γc $$ Hcc Hoc with #Hhc
  imod start_handshake nv.confstatec' (confstateP γn) iprop(True) γcs $$ Hccs Hocs with #Hhcs
  imod start_handshake nv.readyc' (readyP γn) iprop(True) γrd $$ Hcrd Hord with #Hhrd
  imod adv_start γn nv.rn' cv.ID' nv.advancec' $$ Hca Hoa with #Hha
  imod alloc_broadcast_chan (nodeStoppedRaw γn) γd nv.done' $$ Hcd Hod with Hpend
  icases ownBroadcastChan_pending_unknown nv.done' γd (nodeStoppedRaw γn) $$ Hpend with ⟨Hpend, #Hhd⟩
  imod start_handshake nv.stop' (fun (_ : Unit) => nodeLiveRaw γn 1) iprop(True) γs $$ Hcs Hos
    with #Hhs
  imod start_handshake nv.status' statusChP iprop(True) γst
    $$ Hcst Host with #Hhst
  imod tickCred_zero bud with Hcr0
  imod inv_alloc tickN ⊤ (tickInv γn) $$ [Hot Hcr0] with #Htickinv
  · inext
    unfold tickInv
    iexists []
    iframe
  icases ownRawNode_shared γ rn cv.ID' _ $$ Hrn with ⟨%r, %lok', #Hrr, #Hrid, #Hrlg, #Hlg', Hrn⟩
  ihave #Hnode : isNodeChan γn cv.ID' n_ptr $$ []
  · unfold isNodeChan
    iexists nv, r, lok'
    simp only [named]
    rw [Hnvrn]
    iframe #
    ipureintro; rfl
  -- `go n.run()`
  wp_apply wp_fork $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam Hpend Hlive1]
  · wp_apply wp_node_run γn cv.ID' n_ptr $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam Hpend Hlive1]
    · iframe Hnode
      unfold runPre
      iexists nv, _, (([], [], [], hsZero, none) : List EntryM × List EntryM × List EntryM ×
        HardStateM × Option SnapLoan)
      rw [Hnvrn]
      iframe n Hrn Hrof1 Hrof2
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iframe Hdlv1 Hlb0
      iframe Hpend Hlive1
      unfold runCfg
      isplitr
      · ipureintro
        exact ⟨rfl, Nat.le_refl _, rfl, fun _ h => by simp at h, rfl⟩
      isplitl [Hdlm]
      · iExactEq Hdlm; rfl
      isplitr
      · simp only [rsDlv]
        iapply dlvKeysAt_nil
      iexists 0
      iframe Hcap1 Hcam
      isplitr
      · ipureintro; exact Nat.le_refl _
      iapply undecFree_empty
    itrivial
  iapply HΦ
  iexists γn, n_ptr
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  iframe Hnode Hlive2 HR'
  isplitl [Hdlv2 Hreq1 Hreq2]
  · unfold nodeDriverChan dlvLb
    iframe Hnode Hdlv2 Hdlb
    isplitr
    · iapply dlvKeysAt_nil
    iexists _
    iframe Hreq1 Hreq2
  unfold nodeCfg
  iframe Hcap2 Hcamlb
  iexists _
  iframe Hccq1 Hccq2

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Raft's log namespace is in the cluster's. -/
private theorem raftLogN_sub (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (HNs : γ.raft.reNs = N .@ "raft") : (↑(raftLogN γ.raft) : CoPset) ⊆ E := by
  intro p hp
  unfold raftLogN raftN at hp; rw [HNs] at hp
  exact HE p (nclose_subseteq N "raft" p (nclose_subseteq (N .@ "raft") "log" p hp))

/-- **A valid snapshot's certificates** (the API's `snapshotValid` read back at raft's level). -/
private theorem snapValid_raftCert (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (_HU : UniNames γ N) (sv : SnapshotM) :
    ⊢ clusterInv (GF := GF) γ N -∗ EtcdGrove.snapshotValid (GF := GF) γ sv ={E}=∗
      raftSnapCertD γ.raft (snapTrip sv sv.Metadata'.ConfState'.lists) := by
  iintro #Hci Hv
  unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.confAt EtcdGrove.snapMade
  icases Hv with ⟨%l, %m, #Hlb, #Ha, #Hm, %Hp⟩
  obtain ⟨Hlen, -, Hlast, Hcs, H61, Hsz⟩ := Hp
  ihave %Hval := confAt_valid_impl γ l.length m $$ Ha
  ihave %Hres := confAtU_restorable γ l.length m $$ Ha
  iunfold confAtU at Ha
  icases Ha with ⟨%l2, %M, #Hlb2, #HM, %P2⟩
  obtain ⟨hk, c0, g, hm, hf⟩ := P2
  icases isCommittedLogLb_agree_impl γ l l2 $$ [Hlb Hlb2] with %Hcm
  · iframe Hlb Hlb2
  have Hfold : decFold M c0 l = some m := by
    rw [← List.take_length (l := l), take_eq_of_cmp l l2 l.length Hcm (Nat.le_refl _) hk]
    exact hf
  iunfold snapMadeU at Hm
  icases Hm with ⟨%gr, %K, %key, %Hk, #HK, -⟩
  obtain ⟨Hreg, HkK, Hmat⟩ := Hk
  have hm' := hm
  obtain ⟨⟨h0, -, hd, -, Hsok, -, -⟩, -⟩ := hm'
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, -, -⟩
  imod api_lb_committed γ N E HE l $$ Hci Hlb with ⟨%L, %HL, #HLc⟩
  have HD : (DynCfg.ofFold noDec (stOf c0) h0).fold M L = some (cfgOf m) := by
    rw [hm.fold _ hd M L, HL, Hfold]; rfl
  have HLlen : L.length = uint.nat sv.Metadata'.Index' := by rw [← Hlen, ← HL, strip_length]
  have HLlast : L.getLast?.map EntryM.Term' = some sv.Metadata'.Term' := by
    rw [← Hlast, ← HL]; unfold strip; rw [List.getLast?_map, Option.map_map]; rfl
  obtain ⟨hcv, hco, hcl, hcn, hal⟩ := Hcs
  unfold EtcdGrove.Membership.Valid memValid at Hval
  obtain ⟨Hz, Hni⟩ := Hres
  iapply raftSnapCertD_snapTrip γ.raft E L sv (cfgOf m) _ M gr K key
    (raftLogN_sub γ N E HE HNs) hd Hreg Hsok HLlen (by rw [HLlen, ← Hlen]; exact H61) HLlast
    hcv hco hcl hcn hal Hval.1
    (fun x hx h0x => Hz (by
      subst h0x
      simp only [Membership.ids, GMap.elem_of_union]
      rcases hx with h | h | h | h
      · exact .inl (.inl (.inl h))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h))
    (fun x hx => Hni x hx) Hsz HD HkK (by rw [HLlen, ← Hlen]; exact Hmat.1) Hmat.2
    $$ Hcinv HLc HM HK

/-- Raft's reading of the contract's `Bnd`: an applied lower bound or a snapshot handed out of the
node's storage names (its table's entry). -/
private theorem storBnd_raftBnd (γ : Cluster) (id : w64) (sn : StorNames) (c : Nat) :
    ⊢ nodeStorNames (GF := GF) γ id sn -∗ monoNatLbOwn sn.ga 0 -∗ EtcdGrove.storBnd γ id c -∗
      raftBnd sn c := by
  iintro #Hsn #H0 Hb
  unfold EtcdGrove.storBnd EtcdGrove.nodeAppliedLb EtcdGrove.snapGiven nodeAppliedLbU snapGivenU
    raftBnd
  icases Hb with ⟨%k, %Hk, ((%Hk0 | ⟨%sn', #Hsn', (#Hl | #Hl)⟩) | ⟨%sn', #Hsn', #Hl⟩)⟩
  · iexists 0
    isplitr; · ipureintro; omega
    ileft; iexact H0
  · ihave %He := nodeStorNames_agree γ id sn' sn $$ Hsn' Hsn
    subst He
    iexists k
    isplitr; · ipureintro; exact Hk
    ileft; iexact Hl
  · ihave %He := nodeStorNames_agree γ id sn' sn $$ Hsn' Hsn
    subst He
    iexists k
    isplitr; · ipureintro; exact Hk
    iright; iexact Hl
  · ihave %He := nodeStorNames_agree γ id sn' sn $$ Hsn' Hsn
    subst He
    iexists k
    isplitr; · ipureintro; exact Hk
    iright; iexact Hl

/-- Raft's reading of the contract's `DL` for a valid snapshot: the node's delivered committed log
reaches its index, so raft certified the term there (`dlvKeys`, of the node's storage names). -/
private theorem storDL_raftDL (γ : Cluster) (id : w64) (sn : StorNames) (sv : SnapshotM)
    (Hdyn : ∀ γn : NodeNames, NodeOk γ γn → γn.mode.isDyn = true) :
    ⊢ nodeStorNames (GF := GF) γ id sn -∗ EtcdGrove.snapshotValid γ sv -∗
      EtcdGrove.storDL γ id (uint.nat sv.Metadata'.Index') -∗
      raftDL sn (uint.nat sv.Metadata'.Index') sv.Metadata'.Term' := by
  iintro #Hsn Hv Hdl
  unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.storDL EtcdGrove.isNode
    EtcdGrove.deliveredLogLb
  icases Hv with ⟨%l1, %m, #Hlb1, -, -, %Hp⟩
  obtain ⟨Hlen, Hpos, Hlast, -⟩ := Hp
  icases Hdl with ⟨%n, %N', %l, Hnode, Hdlv, %Hi⟩
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn0, -, #Hch0, -⟩
  iunfold deliveredLogLb at Hdlv
  icases Hdlv with ⟨⟨%γn, %id', %ds, %Hf, #Hch, (%Hnd | #Htab), #Hdk⟩, #Hlb⟩
  · exfalso; rw [Hdyn γn Hf.1] at Hnd; cases Hnd
  ihave %Hid := isNode_id_agree γn0 γn id id' n $$ Hch0 Hch
  subst Hid
  ihave #Hsn2 := nodeTabOk_storNames γ id γn $$ Htab
  ihave %Hs := nodeStorNames_agree γ id γn.sn sn $$ Hsn2 Hsn
  icases isCommittedLogLb_agree_impl γ l1 l $$ [Hlb1 Hlb] with %Hcm
  · iframe Hlb1 Hlb
  have Hpre : l1 <+: l := by
    rcases Hcm with h | h
    · exact h
    · have e := h.eq_of_length (by have := h.length_le; omega)
      rw [e]
      exact ⟨[], List.append_nil _⟩
  obtain ⟨t, Ht⟩ := Hpre
  have Hj : l1.length - 1 < l1.length := by omega
  have Hl1j : l1[l1.length - 1]?.map LogEntry.term = some sv.Metadata'.Term' := by
    rw [← List.getLast?_eq_getElem?]; exact Hlast
  have Hlj : l[l1.length - 1]? = l1[l1.length - 1]? := by
    rw [← Ht, List.getElem?_append_left Hj]
  rw [← Hlj, ← Hf.2] at Hl1j
  unfold strip at Hl1j
  rw [List.getElem?_map, Option.map_map] at Hl1j
  cases hde : ds[l1.length - 1]? with
  | none => rw [hde] at Hl1j; cases Hl1j
  | some e =>
    rw [hde] at Hl1j
    simp only [Option.map_some, Option.some.injEq, Function.comp] at Hl1j
    iunfold dlvLb at Hdk
    icases Hdk with ⟨-, #Hk⟩
    iunfold dlvKeys at Hk
    iunfold dlvKeysAt at Hk
    ihave #Hke := (BigSepL.bigSepL_lookup (Φ := fun j (e : EntryM) =>
      iprop((0 + j + 1) ↪[γn.sn.gd]□ e.Term' : IProp GF)) hde) $$ Hk
    unfold raftDL
    ileft
    rw [← Hs, show uint.nat sv.Metadata'.Index' = 0 + (l1.length - 1) + 1 by omega, ← Hl1j]
    iExactEq Hke; rfl

/-- **The certificate link of fresh storage names** (`certLink`): their `SV` pin the API's
`snapshotValid`, their snapshot pin raft's certificate. -/
private theorem certLink_make (γ : Cluster) (N : Namespace) (HU : UniNames γ N) (sn : StorNames) :
    ⊢ clusterInv (GF := GF) γ N -∗
      savedPredOwn sn.gsv DFrac.discard (EtcdGrove.snapshotValid (GF := GF) γ) -∗
      savedPredOwn sn.gk DFrac.discard (raftSnapCertD (GF := GF) γ.raft) -∗ certLink γ.raft sn := by
  iintro #Hci #Hsv #Hgk
  have HcN : raftCertN γ.raft = N := HU.2.2.1
  unfold certLink storCertOk
  isplitr
  · iintro !> %sv %E %HE Hc
    rw [HcN] at HE
    unfold svCert
    icases Hc with ⟨%SV, #Hp, #HSV⟩
    ihave #Heq := saved_pred_agree sn.gsv DFrac.discard DFrac.discard SV
      (EtcdGrove.snapshotValid (GF := GF) γ) sv $$ Hp Hsv
    ihave Hv : ▷ EtcdGrove.snapshotValid (GF := GF) γ sv $$ []
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ HSV
    have : Timeless (EtcdGrove.snapshotValid (GF := GF) γ sv) := by
      have : ∀ s, Timeless (snapMadeU (GF := GF) γ s) := fun s => by
        unfold snapMadeU; infer_instance
      have : ∀ l, Timeless (isCommittedLogLb (GF := GF) γ l) := fun l => by
        unfold isCommittedLogLb; infer_instance
      unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.confAt EtcdGrove.snapMade
      infer_instance
    icases Hv with >Hv
    iapply snapValid_raftCert γ N E HE HU sv $$ Hci Hv
  isplitr
  · iintro !> %k %E %HE Hc
    unfold ksnCert
    icases Hc with ⟨%P, #Hp, #HP⟩
    ihave #Heq := saved_pred_agree sn.gk DFrac.discard DFrac.discard P
      (raftSnapCertD (GF := GF) γ.raft) k $$ Hp Hgk
    ihave Hv : ▷ raftSnapCertD (GF := GF) γ.raft k $$ []
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ HP
    icases Hv with >#Hv
    imodintro; iexact Hv
  · iintro !> %k %E %HE #Hc
    unfold ksnCert
    imodintro
    iexists raftSnapCertD γ.raft
    iframe Hgk
    imodintro; iexact Hc

/-- `RestartNode.spec` from the raw triple (2026-10-28, stage U4a): the node in the cluster's
dynamic mode (of the client's decisions, since the decision switch; until then the rule's), taking `MsgSnap`s (`snapIn`), its ghost state the dynamic one at the
initial state (`ownRaftGhostR_rinit`), its table entry inserted (`nodeTabOk`), its view at the
voters' membership. -/
private theorem wp_RestartNode_impl
    (hS : EtcdGrove.RestartNode.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.RestartNode.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.RestartNode.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.nodeDriver
    EtcdGrove.nodeFounder EtcdGrove.nodeJoin EtcdGrove.confAt EtcdGrove.bootStorage
    EtcdGrove.nodeConfig EtcdGrove.nodeRunning
  intro γ N vs c cv lok si hs csm Q H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hhs Hv Hvo Hl Hln Hal
  iintro %Φ ⟨#Hinit, Hc, #Hlog, Hboot, Htok⟩ HΦ
  -- (2026-10-29, stage U4) a newcomer's token is a founder's of the initial membership's voters
  ihave Htok : nodeFounderU (GF := GF) γ N vs cv.ID' $$ [Htok]
  · icases Htok with (Htok | ⟨Hj, #Hca, %Hnd⟩)
    · iexact Htok
    · iapply nodeJoin_founder_impl γ N vs cv.ID' Hnd $$ [Hj Hca]
      iframe Hj Hca
  iunfold nodeFounderU at Htok
  iunfold nodeJoinU at Htok
  iunfold joinBaseU at Htok
  iunfold joinSlotU at Htok
  icases Htok with ⟨⟨#Hcl, %-, ⟨-, #Hc0, #Hbinv, #Htlb⟩, ⟨Hg, ⟨%g, %Hg0, Ha⟩⟩⟩, %Hpf⟩
  obtain ⟨Hcfg, ⟨gd, Hmr⟩, Hne, Hnd, Hnz, Hlen⟩ := Hpf
  ihave #Hcl' := Hcl
  iunfold isClusterU at Hcl'
  icases Hcl' with ⟨%HU, #Hci, #Hpool⟩
  have Hsl := HU.2.1
  have Hdyn := Hmr.1.2.2.1
  obtain ⟨h0, h1, Hmd⟩ := Hmr.mode
  subst Hv
  have HdynOk : ∀ γn : NodeNames, NodeOk γ γn → γn.mode.isDyn = true := fun γn h => by
    rw [h.2.2.2, Hmd]; rfl
  -- the boot bundle
  icases Hboot with ⟨%i, %Rb, %Hi, HRb, #HFI, #HLI, #HIS⟩
  cases Hi
  -- the node's configuration names (`run`'s and the driver's), allocated here so that its table
  -- entry exists before the storage's contract is read
  imod mono_list_own_alloc (GF := GF) ([] : List EntryM) with ⟨%gdlm, Hdlm, #Hdlb⟩
  imod dghostVar_alloc (GF := GF) ((0 : Nat), cfgState (GMap.listToSet csm.Voters') ∅)
    with ⟨%gcap, Hcap⟩
  imod dghostVar_alloc (GF := GF) ((0 : Nat), cfgState (GMap.listToSet csm.Voters') ∅)
    with ⟨%gccq, Hccq⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%gcam, Hcam, #Hcamlb⟩
  imod dghostVar_alloc (GF := GF) false with ⟨%glive, Hlive⟩
  -- raft's storage names: the applied floor, the snapshot handed out, the certified terms, the
  -- contract's `SV` and the received snapshots' certificate
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%ga, Hga, #Hga0⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%gg, Hgg, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := w64) with ⟨%gdd, Hgd⟩
  imod saved_pred_alloc (EtcdGrove.snapshotValid (GF := GF) γ) DFrac.discard trivial
    with ⟨%gsv, #Hsv⟩
  imod saved_pred_alloc (raftSnapCertD (GF := GF) γ.raft) DFrac.discard trivial with ⟨%gk, #Hgk⟩
  let sn : StorNames := ⟨ga, gg, gsv, gdd, gk⟩
  -- the node's table entry
  imod ghost_map_insert_persist cv.ID'
    ((gdlm, gcap, gccq, gcam, glive, ga, gg, gsv, gdd, gk) : CfgNames) (GMap.lookup_empty _)
    $$ Ha with ⟨-, #He⟩
  ihave #Hsn : nodeStorNames (GF := GF) γ cv.ID' sn $$ []
  · unfold nodeStorNames
    iexists g, ((gdlm, gcap, gccq, gcam, glive, ga, gg, gsv, gdd, gk) : CfgNames)
    iframe He
    ipureintro; exact ⟨Hg0, rfl⟩
  ihave #Hlink := certLink_make γ N HU sn $$ Hci Hsv Hgk
  iapply wp_fupd
  iapply (hS γ.raft (γ.mode inferInstance) γ.bud c cv lok si sn gdlm gcap gccq gcam glive
    ({ prev := entryID.mk (W64 0) (W64 0), ents := [], pend := [] } : StorState) hs csm
    iprop(Rb ∗ storAuths sn ({ prev := entryID.mk (W64 0) (W64 0), ents := [], pend := [] } :
      StorState)) Q
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 rfl rfl rfl rfl rfl rfl Hhs Hne Hnd Hnz (by omega) Hvo Hl Hln
    Hal (fun _ => Hcfg) (fun h => by rw [Hmd] at h; cases h) rfl)
    $$ [Hc HRb Hga Hgg Hgd Hg Hdlm Hcap Hccq Hcam Hlive]
  · iframe Hinit Hc Hlog Hc0 Hbinv Htlb Hlink Hdlm Hdlb Hcap Hccq Hcam Hcamlb Hlive
    isplitl [HRb Hga Hgg Hgd]
    · iframe HRb
      unfold storAuths
      isplitl [Hga]
      · iExactEq Hga; rfl
      iframe Hgg
      iExactEq Hgd; rfl
    isplitr
    · iintro !> %Φ' !> ⟨HRb, HA⟩ HΦ'
      iapply HFI $$ HRb [HA HΦ']
      inext
      iintro HRb
      iapply HΦ'
      iframe HRb HA
    isplitr
    · iintro !> %Φ' !> ⟨HRb, HA⟩ HΦ'
      iapply HLI $$ HRb [HA HΦ']
      inext
      iintro HRb
      iapply HΦ'
      iframe HRb HA
    isplitr
    · iintro !> %Φ' !> ⟨HRb, HA⟩ HΦ'
      iapply HIS $$ HRb [HA HΦ']
      inext
      iintro %hp %cs %al ⟨Hhs, Hcs, Hup⟩
      iapply HΦ'
      iframe Hhs Hcs
      imod Hup with ⟨Hst, ⟨%e0, %He0, #Hl0, Hend⟩, HQ⟩
      imodintro
      iframe HQ
      isplitl [Hst]
      · iapply isStorage_of_V
        unfold isStorageV
        iexists EtcdGrove.snapshotValid (GF := GF) γ, EtcdGrove.storBnd (GF := GF) γ cv.ID',
          EtcdGrove.storDL (GF := GF) γ cv.ID'
        isplitl [Hst]
        · iunfold EtcdGrove.isStorage at Hst
          iexact Hst
        isplitr; · iexact Hsv
        isplitr
        · unfold EtcdGrove.snapshotValid EtcdGrove.isCommittedLogLb EtcdGrove.confAt
            EtcdGrove.snapMade
          iintro !> %sv #H
          imodintro; iexact H
        isplitr
        · iintro !> %c' Hb
          iapply storBnd_raftBnd γ cv.ID' sn c' $$ Hsn Hga0 Hb
        · iintro !> %sv Hv Hd
          imodintro
          iapply storDL_raftDL γ cv.ID' sn sv HdynOk $$ Hsn Hv Hd
      unfold ownStorage
      iexists e0
      isplitr
      · ihave H := StorageModel.storCompacted_zero (GF := GF) (interface.ok si)
        iExactEq H; rfl
      isplitr
      · iExactEq Hl0; rfl
      isplitr
      · ihave Hn := StorageModel.storLog_nil (GF := GF) (interface.ok si) 1 (DFrac.own 1)
        iExactEq Hn; rfl
      isplitl [Hend]
      · iright; iExactEq Hend; rfl
      iframe HA
      ipureintro
      exact ⟨He0, Nat.le_refl _, by simp [StorState.kOut], by simp [StorState.kOut], Nat.le_refl _⟩
    · rw [Hmd]
      unfold rnInit
      isplitr
      · ipureintro; exact ⟨Hdyn, stOf_simple _⟩
      iapply ownRaftGhostR_rinit $$ Hg
  iintro !> %nd ⟨%γn, %n, %Hf, HQ, #Hnode, Hdrv, Hlive, Hcf⟩
  obtain ⟨Hγr, Hγb, Hγs, Hmd', Hsn', Hnd', Hd1, Hd2, Hd3, Hd4, Hd5⟩ := Hf
  have Hnok : NodeOk γ γn := ⟨Hγr, Hγb, Hsl, Hmd'⟩
  have Hdy : γn.mode.isDyn = true := HdynOk γn Hnok
  ihave #Htb : nodeTabOk (GF := GF) γ cv.ID' γn $$ []
  · unfold nodeTabOk
    iexists g
    isplitr; · ipureintro; exact Hg0
    have Hx : cfgNamesOf γn = ((gdlm, gcap, gccq, gcam, glive, ga, gg, gsv, gdd, gk) : CfgNames) := by
      simp only [cfgNamesOf, Hd1, Hd2, Hd3, Hd4, Hd5, Hsn', sn]
    rw [Hx]
    iexact He
  imodintro
  iapply HΦ
  iexists n
  isplitr
  · ipureintro; exact Hnd'
  isplitr
  · unfold isNode
    iexists γn
    isplitr; · ipureintro; exact Hnok
    iframe Hnode Htb Hci Hpool
    ipureintro; exact HU
  isplitl [Hdrv]
  · unfold nodeDriver NodeDriverState.init
    iexists γn, cv.ID', []
    isplitr
    · ipureintro; exact ⟨Hnok, Hγs, rfl⟩
    isplitr; · iexact Hci
    isplitr; · iapply isCommittedLogLb_nil_impl
    isplitr; · ipureintro; exact Hdy
    isplitr; · iexact Htb
    isplitr
    · unfold hsCommitted; ileft; ipureintro; rfl
    ileft
    isplitr
    · ipureintro; rfl
    iexact Hdrv
  isplitl [Hcf]
  · isplitl [Hcf]
    · unfold nodeConfig
      iexists γn, cv.ID'
      iframe Hnode Htb
      isplitr
      · ipureintro
        refine ⟨Hnok, Hdy, ?_⟩
        show CCGood (stOf (Membership.simple (GMap.listToSet csm.Voters')))
        rw [stOf_simple]; exact ccGood_cfgState _
      rw [stOf_simple]; iexact Hcf
    -- (2026-10-30, stage R3) the initial membership, of no entry
    unfold confAtU
    iexists [], ∅
    isplitr; · iapply isCommittedLogLb_nil_impl
    isplitr; · iapply decLb_empty
    ipureintro
    exact ⟨Nat.le_refl _, _, gd, Hmr, rfl⟩
  isplitl [Hlive]
  · -- (2026-10-29, stage U9a) the node runs
    unfold nodeRunning
    iexists γn, cv.ID'
    iframe Hnode Htb Hlive
    ipureintro; exact ⟨Hnok, Hdy⟩
  iexact HQ

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem RestartNode.wp_proof
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG))
    (wp_newNode : newNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    RestartNode.spec (GF := GF) (hG := hG) :=
  ApiImpl.wp_RestartNode_impl (RestartNode.wp_raw wp_NewRawNode wp_newNode wp_node_run)

end proof

end EtcdGrove
end Perennial
