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
import Proof.go_etcd_io.raft.v3.InvApiDyn
import Proof.go_etcd_io.raft.v3.InvApiRule
import all Proof.go_etcd_io.raft.v3.InvNodeRule

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

/-- See the file header. -/
private abbrev RestartNode.specRaw : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (bud : BudgetNames) (c : Loc) (cv : Config)
    (lok si : GoInterfaceOk)
    (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM) (sn : Bool),
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
  σ.prev = entryID.mk (W64 0) (W64 0) →
  σ.ents = [] →
  (uint.Z σ.ss.index' = 0 ∨ σ.ss = σ.prev) →
  σ.pend = [] →
  HsEmpty hs →
  -- (2026-10-16, stage R5) the conf state's record `csm`, as `NewRawNode`'s
  csm.Voters' ≠ [] → csm.Voters'.Nodup → W64 0 ∉ csm.Voters' →
  (csm.Voters'.length : Int) ≤ 2 ^ 62 →
  csm.VotersOutgoing' = [] →
  csm.Learners' = [] →
  csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  γ.reCfg = GMap.listToSet csm.Voters' →
  cv.ID' ∈ csm.Voters' →
  -- (2026-10-25, T-M M2c: `StepDownOnRemoval` either way; 2026-10-15 to 2026-10-25 on in the dynamic
  -- mode)
  -- (D19i part 1) the floor not raised yet: the storage's view, fresh to raft
  σ.fl = W64 0 →
  -- (D22 S-d4, 2026-10-21) the node takes a `MsgSnap` from the network (`NodeNames.snapIn`) only
  -- outside the no-snapshot mode (until 2026-10-28, stage U3d, also in the static mode)
  (sn = true → γ.reNoSnap = false) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      -- (2026-10-16, stage R5) `NewRawNode`'s (`newRaft`'s, stage R4, D7; stage R6b: `al`)
      □ (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (interface.ok si) { σ with ss := ss' } -∗
            hsOpt hp hs -∗ csPts cs DFrac.discard csm al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      -- (2026-10-15, stage N) the ghost state in the mode `md` (`NewRawNode`'s `rnInit`; until
      -- then `ownRaftGhost γ cv.ID' initPState`, the static mode's)
      rnInit γ md cv.ID' (GMap.listToSet csm.Voters') ∗ isCommitted γ [] ∗
      -- the cluster's term budget
      inv budgetN (budgetInv bud) ∗ termLB bud (W64 0) ∗
      -- (D22 S-b′3, 2026-10-20) the storage's certificate link (`certLink`: none needed in the
      -- no-snapshot mode)
      certLink γ (interface.ok si) }}
    (App (Val #(functions RestartNode [])) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (γn : NodeNames) (n : Loc),
        ⌜γn.raft = γ ∧ γn.bud = bud ∧ γn.stor = interface.ok si ∧ γn.mode = md ∧
         γn.snapIn = sn ∧ nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNodeChan γn cv.ID' n ∗ nodeDriverChan γn cv.ID' n [] hsZero ∗
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
  intro γ md bud c cv lok si σ hs csm sn P1 P2 P3 P4 P5 P6 P7 P8 P9 P11 P12 P13 P14
    P15 P16 P17 P18 P19 P20 P21 P22 P23 P24 P25 P26 P28 HsnIn
  wp_start as ⟨Hc, #Hlg, #Hsto, Hown, #Hinit, Hghost, #Hcommitted, #Hbud, #Hlb0, #Hcl⟩
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
  -- (D17d) `NewRawNode`'s `InitialState` premise at `R = emp`: the `□` closure gives nothing back
  wp_apply wp_NewRawNode c cv lok si σ hs csm iprop(emp) P1 P2 P3 P4 P5 P6 P7 P8 P9
    P11 P12 P13 P14 P15 P16 P18 P19 P20 P21 P22 P23 P24 P28
    $$ [$Hc $Hlg $Hsto $Hown] as %rn %err ⟨-, %s0, Hfresh0, %Herr⟩
  · iintro %Φ %ss' Hs HK
    iapply Hinit $$ Hs
    iintro %hp %cs %al Hs Hhs Hcs
    iapply HK $$ Hs [] Hhs Hcs
    iempintro
  subst Herr
  -- the node closed with the ghost state, in the mode `md` (2026-10-16, stage R8b: `NewRawNode`
  -- leaves it open, `rawNodeFresh`)
  -- (2026-10-19, D21 M2r) out of the no-snapshot mode: leader transfer on; (D22 S-a) at the
  -- cluster's no-transfer mode (`RaftNames.reNoXfer`), either way
  icases rawNodeFresh_set_xf _ _ _ _ _ _ s0 γ.reNoXfer $$ Hfresh0 with ⟨%s, Hfresh⟩
  iunfold rawNodeFresh at Hfresh
  icases Hfresh with ⟨%rnv, %sv, %hprev, Hfresh⟩
  iNamed Hfresh
  obtain ⟨Hp, Hse, Hue, Hsd, Hcm, Hap, Hapg, Hun, Hsn, Hsg⟩ := Hlog
  -- (D22l) `prevHardSt` zero, `RNState.phs`'s default
  ihave #Hhard0 := prevHS_of_zero γ _ _ Hhz $$ Hhard
  obtain ⟨Ht0, Hv0, Hr, -, -, -⟩ := Hterm0
  have Hdlen0 : ([] : List EntryM).length = (uint.Z s.logst.applying).toNat := by
    rw [Hapg]; rfl
  -- (2026-10-17) the term ceiling at the term, `0`
  have Hrnpv : ∀ fp, RNPv
      { delivered := [], unpersisted := [], steps := [], term := W64 0,
        storage := interface.ok si, mode := md,
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
        storage := interface.ok si, mode := md,
        cfg := cfgState (GMap.listToSet csm.Voters') ∅ } $$ [Hrn Hphys Hghost Hsteps Hsteps_cap]
  · cases md with
    | static =>
      iunfold rnInit at Hghost
      ihave #Hsdrf : sdrOk (GF := GF) rnv.raft' RNMode.static $$ []
      · iunfold sdrOk; iexists s.sdr; iexact Hsd0
      ihave Hphys := ownRaftPhysC_toS $$ Hphys
      ihave Hphys : ownRaftPhys γ.reCfg rnv.raft' cv.ID' s $$ [Hphys]
      · rw [P25]; iexact Hphys
      iapply ownRawNode_intro_static γ rn cv.ID'
          { delivered := [], unpersisted := [], steps := [], term := W64 0,
            storage := interface.ok si, mode := .static,
            cfg := cfgState (GMap.listToSet csm.Voters') ∅ }
          s initPState rnv sv hprev [] rfl Hrel
          (by rw [P25]; exact (GMap.elem_of_list_to_set _ _).2 P26) Hasync
          Hdlen0 (by rw [Hun]) (fun _ => Hsn) trivial
          (by rw [Ht0]) (by rw [Hsg]) (Hrnpv []) (by rw [Hgh]) (by rw [Hgh])
          (uint_Z_nonneg _) (HrnflR _ rfl)
          -- (D22 S-d3a) no snapshot lent
          ⟨by rw [Hgh]; try rfl, fun _ => ⟨by rw [Hgh]; try rfl, fun _ _ _ _ h => (by cases h)⟩,
            fun l h => (by cases h)⟩
          (SdtTie.of_none Hsn)
          (TrackedOk.of_sub (by rw [Hdom, P25]; exact GMap.subseteq_refl _)
            (by rw [P25]; exact (GMap.elem_of_list_to_set _ _).2 P26))
          (by unfold NsLink; rw [Hgh, Hns0, Hnx0]; exact ⟨rfl, rfl, rfl⟩)
          $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard0 Hsteps Hsteps_cap [] Hcommitted [] [] [] []
      · iapply pendList_nil
      · iapply ackInv_none; intro _ _ _ _ h; cases h
      · ipureintro; trivial
      · rw [Hsg]; iexact Hcl
      · rw [Hsn]; iapply snapLocOk_none
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
          refine ⟨HD, ?_, by unfold NsLink; rw [Hgh, Hns0, Hnx0]; exact ⟨rfl, rfl, rfl⟩⟩
          rw [Hdiff]; rfl
        isplitr; · iapply decLb_empty
        rw [Hsg]; iexact Hcl
      iapply ownRawNode_intro γ rn cv.ID'
          { delivered := [], unpersisted := [], steps := [], term := W64 0,
            storage := interface.ok si, mode := .dyn dec (cfgState (GMap.listToSet csm.Voters') ∅) h0 h1,
            cfg := cfgState (GMap.listToSet csm.Voters') ∅ }
          s _ [] rnv sv hprev [] Hrel.2 (fun h => by cases h) rfl Hasync
          Hdlen0 (by rw [Hun]) (fun _ => Hsn) trivial
          (by rw [Ht0]) (by rw [Hsg]) (Hrnpv _) (by rw [Hgh]) (by rw [Hgh])
          (uint_Z_nonneg _) (HrnflR _ rfl)
          -- (D22 S-d3a) no snapshot lent
          ⟨by rw [Hgh]; try rfl, fun _ => ⟨by rw [Hgh]; try rfl, fun _ _ _ _ h => (by cases h)⟩,
            fun l h => (by cases h)⟩
          (SdtTie.of_none Hsn) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard0 Hsteps Hsteps_cap [] Hcommitted [] [] []
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
  imod mono_list_own_alloc ([] : List EntryM) with ⟨%γdlm, Hdlm, #Hdlb⟩
  imod dghostVar_alloc ((0 : Nat), cfgState (GMap.listToSet csm.Voters') ∅) with ⟨%γcap, Hcap⟩
  icases dghostVar_halves _ _ $$ Hcap with ⟨Hcap1, Hcap2⟩
  imod dghostVar_alloc ((0 : Nat), cfgState (GMap.listToSet csm.Voters') ∅) with ⟨%γccq, Hccq⟩
  icases dghostVar_halves _ _ $$ Hccq with ⟨Hccq1, Hccq2⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γcam, Hcam, #Hcamlb⟩
  -- (D19i part 1) the driver's request on `advancec`
  imod dghostVar_alloc (((none, none) : AdvReq)) with ⟨%γreq, Hreq⟩
  icases dghostVar_halves _ _ $$ Hreq with ⟨Hreq1, Hreq2⟩
  unfold newNodeChans
  icases Hchans with ⟨%γp, %γr, %γc, %γcs, %γrd, %γa, %γt, %γd, %γs, %γst, #Hcp, Hop, #Hcr, Hor,
    #Hcc, Hoc, #Hccs, Hocs, #Hcrd, Hord, #Hca, Hoa, #Hct, Hot, #Hcd, Hod, #Hcs, Hos, #Hcst, Host⟩
  let γn : NodeNames := { raft := γ, id := cv.ID', bud := bud, stor := interface.ok si, propc := γp,
                          recvc := γr, confc := γc, confstatec := γcs, readyc := γrd, advancec := γa, tick := γt,
                          done := γd, stop := γs, status := γst, dlv := γdlv, rof := γrof,
                          mode := md, dlm := γdlm, cap := γcap, ccq := γccq, cam := γcam, req := γreq,
                          snapIn := sn }
  imod start_handshake nv.propc' (propP γn) iprop(True) γp $$ Hcp Hop with #Hhp
  imod start_handshake nv.recvc' (netP γn cv.ID') iprop(True) γr $$ Hcr Hor with #Hhr
  imod start_handshake nv.confc' (confcP γn) iprop(True) γc $$ Hcc Hoc with #Hhc
  imod start_handshake nv.confstatec' (confstateP γn) iprop(True) γcs $$ Hccs Hocs with #Hhcs
  imod start_handshake nv.readyc' (readyP γn) iprop(True) γrd $$ Hcrd Hord with #Hhrd
  imod adv_start γn nv.rn' cv.ID' nv.advancec' $$ Hca Hoa with #Hha
  imod start_handshake nv.done' (fun (_ : Unit) => iprop(False)) iprop(True) γd $$ Hcd Hod
    with #Hhd
  imod start_handshake nv.stop' (fun (_ : Unit) => iprop(False)) iprop(True) γs $$ Hcs Hos
    with #Hhs
  imod start_handshake nv.status' (fun (_ : GoChan) => iprop(False)) iprop(True) γst
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
  wp_apply wp_fork $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam]
  · wp_apply wp_node_run γn cv.ID' n_ptr $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam]
    · iframe Hnode
      unfold runPre
      iexists nv, _, (([], [], [], hsZero, none) : List EntryM × List EntryM × List EntryM ×
        HardStateM × Option SnapLoan)
      rw [Hnvrn]
      iframe n Hrn Hrof1 Hrof2
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iframe Hdlv1 Hlb0
      unfold runCfg
      isplitr
      · ipureintro
        exact ⟨rfl, Nat.le_refl _, rfl, fun _ => ⟨rfl, rfl⟩, HsnIn, fun _ h => by cases h⟩
      isplitl [Hdlm]
      · iExactEq Hdlm; rfl
      iexists 0
      iframe Hcap1 Hcam
      isplitr
      · ipureintro; exact Nat.le_refl _
      iapply undecFree_empty
    itrivial
  iapply HΦ
  iexists γn, n_ptr
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  iframe Hnode
  isplitl [Hdlv2 Hreq1 Hreq2]
  · unfold nodeDriverChan dlvLb
    iframe Hnode Hdlv2 Hdlb
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

/-- `RestartNode.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem wp_RestartNode_impl
    (hS : EtcdGrove.RestartNode.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.RestartNode.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.RestartNode.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.nodeDriver EtcdGrove.nodeRestartBoot EtcdGrove.storageCertLink
  intro γ N vs c cv lok si σ hs csm H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss Hpe Hhs Hv Hvo Hl Hln
    Hal Hid Hfl
  iintro %Φ ⟨#Hinit, Hc, #Hlog, #Hstor, Hown, #Hinst, Hboot, #Hlink⟩ HΦ
  iunfold nodeRestartBoot at Hboot
  icases Hboot with ⟨⟨%so, #Hst⟩, Hg, #Hc0, #Hbinv, #Htlb⟩
  iunfold isStaticCluster at Hst
  icases Hst with ⟨%Hsn, #Hci⟩
  obtain ⟨Hcfg, Hdyn, Hns, -, Hγm, Hsl, Hcert, -, -, Hne, Hnd, Hnz, Hlen⟩ := Hsn
  subst Hv
  ihave #Hok' := storCertOk_of_link γ N _ Hcert Hns $$ Hci Hlink
  iapply (hS γ.raft .static γ.bud c cv lok si σ hs csm true
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss Hpe Hhs Hne Hnd Hnz Hlen Hvo Hl Hln Hal Hcfg Hid
    Hfl (fun _ => Hns)) $$ [Hc Hown Hg]
  · iframe Hinit Hc Hlog Hstor Hown Hinst Hc0 Hbinv Htlb
    isplitl [Hg]
    · unfold rnInit; iexact Hg
    · unfold certLink; iright; iexact Hok'
  iintro !> %nd ⟨%γn, %n, %Hf, #Hnode, Hdrv, Hcfg⟩
  obtain ⟨Hγr, Hγb, Hγs, Hmd, Hsn, Hnd'⟩ := Hf
  have Hnok : NodeOk γ γn := ⟨Hγr, Hγb, Hsl, by rw [Hmd, Hγm, RNMode.all_self], .inl Hsn⟩
  iapply HΦ
  iexists n
  isplitr
  · ipureintro; exact Hnd'
  isplitr
  · unfold isNode
    iexists γn
    iframe Hnode Hci
    ipureintro; exact Hnok
  unfold nodeDriver NodeDriverState.init
  iexists γn, cv.ID', []
  isplitr
  · ipureintro; exact ⟨Hnok, Hγs, rfl⟩
  iframe Hci
  isplitr
  · iapply isCommittedLogLb_nil_impl
  isplitl [Hcfg]
  · iright; iframe Hlink; iexists 0, cfgState (GMap.listToSet csm.Voters') ∅; iexact Hcfg
  isplitr
  · ileft; ipureintro; rw [Hmd]; rfl
  ileft
  isplitr
  · ipureintro; rfl
  iexact Hdrv

/-- `RestartNode.unifiedSpec` from the raw triple (2026-10-28, stage U4a): the node in the cluster's
dynamic mode (the rule's), taking `MsgSnap`s (`snapIn`), its ghost state the dynamic one at the
initial state (`ownRaftGhostR_rinit`), its table entry inserted (`nodeTabOk`), its view at the
voters' membership. -/
private theorem wp_RestartNode_unified_impl
    (hS : EtcdGrove.RestartNode.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.RestartNode.unifiedSpec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.RestartNode.unifiedSpec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.nodeDriver
    EtcdGrove.nodeFounder EtcdGrove.storageCertLink EtcdGrove.nodeConfig
  intro γ N vs c cv lok si σ hs csm H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss Hpe Hhs Hv Hvo Hl Hln
    Hal Hid Hfl
  iintro %Φ ⟨#Hinit, Hc, #Hlog, #Hstor, Hown, #Hinst, Hboot, #Hlink⟩ HΦ
  iunfold nodeFounderU at Hboot
  icases Hboot with ⟨#Hcl, %Hpf, Hg, #Hc0, #Hbinv, #Htlb, ⟨%g, %Hg0, Ha⟩⟩
  obtain ⟨Hcfg, ⟨r, Hmr⟩, Hne, Hnd, Hnz, Hlen⟩ := Hpf
  ihave #Hcl' := Hcl
  iunfold isClusterU at Hcl'
  icases Hcl' with ⟨%Hu, #Hci⟩
  obtain ⟨-, Hsl, Hcert⟩ := Hu
  have Hdyn := Hmr.1.2.2.1
  have Hns := Hmr.1.2.2.2.1
  obtain ⟨h0, h1, Hmd⟩ := Hmr.mode
  subst Hv
  ihave #Hok' := storCertOk_of_link γ N _ Hcert Hns $$ Hci Hlink
  iapply wp_fupd
  iapply (hS γ.raft (γ.mode inferInstance) γ.bud c cv lok si σ hs csm true
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss Hpe Hhs Hne Hnd Hnz (by omega) Hvo Hl Hln Hal Hcfg Hid
    Hfl (fun _ => Hns)) $$ [Hc Hown Hg]
  · iframe Hinit Hc Hlog Hstor Hown Hinst Hc0 Hbinv Htlb
    isplitl [Hg]
    · rw [Hmd]
      unfold rnInit
      isplitr
      · ipureintro; exact ⟨Hdyn, stOf_simple _⟩
      iapply ownRaftGhostR_rinit $$ Hg
    · unfold certLink; iright; iexact Hok'
  iintro !> %nd ⟨%γn, %n, %Hf, #Hnode, Hdrv, Hcf⟩
  obtain ⟨Hγr, Hγb, Hγs, Hmd', Hsn, Hnd'⟩ := Hf
  have Hnok : NodeOk γ γn := ⟨Hγr, Hγb, Hsl, Hmd', .inl Hsn⟩
  have Hdy : γn.mode.isDyn = true := by rw [Hmd', Hmd]; rfl
  imod ghost_map_insert_persist cv.ID' (cfgNamesOf γn) (GMap.lookup_empty _) $$ Ha with ⟨-, #He⟩
  ihave #Htb : nodeTabOk (GF := GF) γ cv.ID' γn $$ []
  · unfold nodeTabOk; iexists g; iframe He; ipureintro; exact Hg0
  imodintro
  iapply HΦ
  iexists n
  isplitr
  · ipureintro; exact Hnd'
  isplitr
  · unfold isNode
    iexists γn
    iframe Hnode Hci
    ipureintro; exact Hnok
  isplitl [Hdrv]
  · unfold nodeDriver NodeDriverState.init
    iexists γn, cv.ID', []
    isplitr
    · ipureintro; exact ⟨Hnok, Hγs, rfl⟩
    iframe Hci
    isplitr
    · iapply isCommittedLogLb_nil_impl
    isplitr
    · ileft; ipureintro; exact Hdy
    isplitr
    · iright; iframe Htb
      isplitr
      · unfold hsCommitted; ileft; ipureintro; rfl
      iright; iexact Hlink
    ileft
    isplitr
    · ipureintro; rfl
    iexact Hdrv
  unfold nodeConfig
  iexists γn, cv.ID'
  iframe Hnode Htb
  isplitr
  · ipureintro
    refine ⟨Hnok, Hdy, ?_⟩
    show CCGood (stOf (Membership.simple (GMap.listToSet csm.Voters')))
    rw [stOf_simple]; exact ccGood_cfgState _
  rw [stOf_simple]; iexact Hcf

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

theorem RestartNode.wp_proof_unified
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG))
    (wp_newNode : newNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    RestartNode.unifiedSpec (GF := GF) (hG := hG) :=
  ApiImpl.wp_RestartNode_unified_impl (RestartNode.wp_raw wp_NewRawNode wp_newNode wp_node_run)

end proof

end EtcdGrove
end Perennial
