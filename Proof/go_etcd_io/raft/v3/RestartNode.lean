/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.newNode
public import Spec.go_etcd_io.raft.v3.node__run
public import Proof.go_etcd_io.raft.v3.InvNodeRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
theorem RestartNode.wp_proof
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG))
    (wp_newNode : newNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    RestartNode.spec (GF := GF) (hG := hG) := by
  intro γ md bud c cv lok si σ hs csm P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14
    P15 P16 P17 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27
  wp_start as ⟨Hc, #Hlg, #Hsto, Hown, #Hinit, Hghost, #Hcommitted, #Hbud, #Hlb0⟩
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
  wp_auto
  wp_apply wp_NewRawNode c cv lok si σ hs csm P1 P2 P3 P4 P5 P6 P7 P8 P9
    P10 P11 P12 P13 P14 P15 P16 P17 P19 P20 P21 P22 P23 P24 P25
    $$ [$Hc $Hlg $Hsto $Hown $Hinit] as %rn %err ⟨%s, Hfresh, %Herr⟩
  subst Herr
  -- the node closed with the ghost state, in the mode `md` (2026-10-16, stage R8b: `NewRawNode`
  -- leaves it open, `rawNodeFresh`)
  iunfold rawNodeFresh at Hfresh
  icases Hfresh with ⟨%rnv, %sv, %hprev, Hfresh⟩
  iNamed Hfresh
  obtain ⟨Hp, Hse, Hue, Hsd, Hcm, Hap, Hapg, Hun, Hsn, Hsg⟩ := Hlog
  obtain ⟨Ht0, Hv0, Hr, -, -, -⟩ := Hterm0
  have Hdlen0 : ([] : List EntryM).length = (uint.Z s.logst.applying).toNat := by
    rw [Hapg]; rfl
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  ihave Hrn : ownRawNode γ rn cv.ID'
      { delivered := [], unpersisted := [], steps := [], term := W64 0,
        storage := interface.ok si, mode := md,
        cfg := cfgState (GMap.listToSet csm.Voters') ∅ } $$ [Hrn Hphys Hghost Hsteps Hsteps_cap]
  · cases md with
    | static =>
      iunfold rnInit at Hghost
      ihave Hphys := ownRaftPhysC_toS $$ Hphys
      ihave Hphys : ownRaftPhys γ.reCfg rnv.raft' cv.ID' s $$ [Hphys]
      · rw [P26]; iexact Hphys
      iapply ownRawNode_intro_static γ rn cv.ID'
          { delivered := [], unpersisted := [], steps := [], term := W64 0,
            storage := interface.ok si, mode := .static,
            cfg := cfgState (GMap.listToSet csm.Voters') ∅ }
          s initPState rnv sv hprev [] rfl Hrel
          (by rw [P26]; exact (GMap.elem_of_list_to_set _ _).2 P27) Hasync
          Hdlen0 (by rw [Hun]) Hsn trivial
          (by rw [Ht0]) (by rw [Hsg]) Hpvoff (by rw [Hgh]) (by rw [Hgh])
          (uint_Z_nonneg _)
          $$ Hrn Hphys Hghost Hsoft Hhard Hsteps Hsteps_cap [] Hcommitted []
      · iapply pendList_nil
      · rw [Hsd]; iapply storedRecs_nil
    | dyn dec c0 h0 h1 =>
      iunfold rnInit at Hghost
      icases Hghost with ⟨%HD, Hgr⟩
      obtain ⟨HD, rfl⟩ := HD
      have Hro : rOf s ⟨0, cfgState (GMap.listToSet csm.Voters') ∅, []⟩ =
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
            ⟨0, cfgState (GMap.listToSet csm.Voters') ∅, []⟩)
          (CfgM.simple (GMap.listToSet csm.Voters') (domSet s.progress \ GMap.listToSet csm.Voters'))
          cv.ID' s $$ [Hgr]
      · simp only [RNMode.toG]
        iapply (ownStepGhost_dyn γ dec _ h0 _ _ cv.ID' s).2
        rw [Hro]
        iframe Hgr
        ipureintro
        refine ⟨HD, ?_⟩
        rw [Hdiff]; rfl
      iapply ownRawNode_intro γ rn cv.ID'
          { delivered := [], unpersisted := [], steps := [], term := W64 0,
            storage := interface.ok si, mode := .dyn dec (cfgState (GMap.listToSet csm.Voters') ∅) h0 h1,
            cfg := cfgState (GMap.listToSet csm.Voters') ∅ }
          s _ [] rnv sv hprev [] Hrel.2 (fun h => by cases h) rfl Hasync
          Hdlen0 (by rw [Hun]) Hsn trivial
          (by rw [Ht0]) (by rw [Hsg]) Hpvoff (by rw [Hgh]) (by rw [Hgh])
          (uint_Z_nonneg _)
          $$ Hrn Hphys Hghost Hsoft Hhard Hsteps Hsteps_cap [] Hcommitted []
      · iapply pendList_nil
      · rw [Hsd]; iapply storedRecs_nil
  wp_auto
  wp_apply wp_newNode rn as %nv ⟨%Hnvrn, Hchans⟩
  ipersist n
  -- the node's ghost state
  imod dghostVar_alloc ([] : List EntryM) with ⟨%γdlv, Hdlv⟩
  icases dghostVar_halves _ _ $$ Hdlv with ⟨Hdlv1, Hdlv2⟩
  imod dghostVar_alloc (([], [], []) : List EntryM × List EntryM ×
    List EntryM) with ⟨%γrof, Hrof⟩
  icases dghostVar_halves _ _ $$ Hrof with ⟨Hrof1, Hrof2⟩
  -- (2026-10-15, stage N) the configuration shared with the driver
  imod mono_list_own_alloc ([] : List EntryM) with ⟨%γdlm, Hdlm, #Hdlb⟩
  imod dghostVar_alloc ((0 : Nat), cfgState (GMap.listToSet csm.Voters') ∅) with ⟨%γcap, Hcap⟩
  icases dghostVar_halves _ _ $$ Hcap with ⟨Hcap1, Hcap2⟩
  imod dghostVar_alloc ((0 : Nat), cfgState (GMap.listToSet csm.Voters') ∅) with ⟨%γccq, Hccq⟩
  icases dghostVar_halves _ _ $$ Hccq with ⟨Hccq1, Hccq2⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γcam, Hcam, #Hcamlb⟩
  unfold newNodeChans
  icases Hchans with ⟨%γp, %γr, %γc, %γcs, %γrd, %γa, %γt, %γd, %γs, %γst, #Hcp, Hop, #Hcr, Hor,
    #Hcc, Hoc, #Hccs, Hocs, #Hcrd, Hord, #Hca, Hoa, #Hct, Hot, #Hcd, Hod, #Hcs, Hos, #Hcst, Host⟩
  let γn : NodeNames := { raft := γ, bud := bud, stor := interface.ok si, propc := γp,
                          recvc := γr, confc := γc, confstatec := γcs, readyc := γrd, advancec := γa, tick := γt,
                          done := γd, stop := γs, status := γst, dlv := γdlv, rof := γrof,
                          mode := md, dlm := γdlm, cap := γcap, ccq := γccq, cam := γcam }
  imod start_handshake nv.propc' (propP γn) iprop(True) γp $$ Hcp Hop with #Hhp
  imod start_handshake nv.recvc' (netP γn cv.ID') iprop(True) γr $$ Hcr Hor with #Hhr
  imod start_handshake nv.confc' (confcP γn) iprop(True) γc $$ Hcc Hoc with #Hhc
  imod start_handshake nv.confstatec' (confstateP γn) iprop(True) γcs $$ Hccs Hocs with #Hhcs
  imod start_handshake nv.readyc' (readyP γn) iprop(True) γrd $$ Hcrd Hord with #Hhrd
  imod start_handshake nv.advancec' (advanceP γn) iprop(True) γa $$ Hca Hoa with #Hha
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
  ihave #Hnode : isNode γn cv.ID' n_ptr $$ []
  · unfold isNode
    iexists nv, r, lok'
    simp only [named]
    rw [Hnvrn]
    iframe #
  -- `go n.run()`
  wp_apply wp_fork $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam]
  · wp_apply wp_node_run γn cv.ID' n_ptr $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam]
    · iframe Hnode
      unfold runPre
      iexists nv, _, (([], [], []) : List EntryM × List EntryM × List EntryM)
      rw [Hnvrn]
      iframe n Hrn Hrof1 Hrof2
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iframe Hdlv1 Hlb0
      unfold runCfg
      iframe Hdlm
      isplitr
      · ipureintro; exact ⟨rfl, Nat.le_refl _⟩
      iexists 0
      iframe Hcap1 Hcam
      ipureintro; exact ⟨Nat.le_refl _, NoConfIn_empty _ _⟩
    itrivial
  iapply HΦ
  iexists γn, n_ptr
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  iframe Hnode
  isplitl [Hdlv2]
  · unfold nodeDriver dlvLb
    iframe Hnode Hdlv2 Hdlb
  unfold nodeCfg
  iframe Hcap2 Hcamlb
  iexists _
  iframe Hccq1 Hccq2

end proof

end EtcdGrove
end Perennial
