/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.StartNode
public import Spec.go_etcd_io.raft.v3.setupNode
public import Spec.go_etcd_io.raft.v3.node__run
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvAdvance

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

/-- `setupNode`, then as `RestartNode.wp_proof` from `newNode` on: the node's ghost state (the
channels' hand-shakes, the tick channel's invariant, `dlv` and `rof`, the configuration shared
with the driver at the peers), `go n.run()` with `runPre` at the delivered log `[]` (D12: the
boot entries reach the application through the first `Ready`). -/
theorem StartNode.wp_proof
    (wp_setupNode : setupNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    StartNode.spec (GF := GF) (hG := hG) := by
  intro γ bud c cv lok si σ hs csm R peers dq pv ps ctxs bootLog P1 P2 P3 P4 P5 P6 P7 P8 P9 P11
    P12 P13 P14 P15 P16 Q1 Q2 Q3 Q4 Q5 R1 R2 R3 R4 R5 R6 R7 R8 R9 Hfl0
  wp_start as ⟨Hc, #Hlg, #Hsto, Hown, Hinit, Hpeers, #Hctx, #Hmarshal, Hghost, #Hcommitted,
    #Hbud, #Hlb1, #Hnscap⟩
  ihave #Hcinv : raftCommitInv γ $$ [Hghost]
  · iapply ownRaftGhost_inv γ cv.ID' (bootPState bootLog) $$ Hghost
  wp_auto
  wp_apply wp_setupNode γ c cv lok si σ hs csm R peers dq pv ps ctxs bootLog P1 P2 P3 P4 P5 P6 P7
    P8 P9 P11 P12 P13 P14 P15 P16 Q1 Q2 Q3 Q4 Q5 R1 R2 R3 R4 R5 R6 R7 R8 R9 Hfl0
    $$ [$Hc $Hlg $Hsto $Hown $Hinit $Hpeers $Hctx $Hmarshal $Hghost $Hcommitted $Hnscap]
    as %np ⟨HR, %nv, %rn, Hn, %Hnvrn, Hchans, Hrn, Hpeers⟩
  ipersist Hn
  try wp_auto
  -- the node's ghost state
  imod dghostVar_alloc ([] : List EntryM) with ⟨%γdlv, Hdlv⟩
  icases dghostVar_halves _ _ $$ Hdlv with ⟨Hdlv1, Hdlv2⟩
  imod dghostVar_alloc (([], [], []) : List EntryM × List EntryM ×
    List EntryM) with ⟨%γrof, Hrof⟩
  icases dghostVar_halves _ _ $$ Hrof with ⟨Hrof1, Hrof2⟩
  -- the configuration shared with the driver: the peers'
  imod mono_list_own_alloc ([] : List EntryM) with ⟨%γdlm, Hdlm, #Hdlb⟩
  imod dghostVar_alloc ((0 : Nat), cfgState (GMap.listToSet ps) ∅) with ⟨%γcap, Hcap⟩
  icases dghostVar_halves _ _ $$ Hcap with ⟨Hcap1, Hcap2⟩
  imod dghostVar_alloc ((0 : Nat), cfgState (GMap.listToSet ps) ∅) with ⟨%γccq, Hccq⟩
  icases dghostVar_halves _ _ $$ Hccq with ⟨Hccq1, Hccq2⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γcam, Hcam, #Hcamlb⟩
  -- (D19i part 1) the driver's request on `advancec`
  imod dghostVar_alloc (0 : Nat) with ⟨%γreq, Hreq⟩
  icases dghostVar_halves _ _ $$ Hreq with ⟨Hreq1, Hreq2⟩
  unfold newNodeChans
  icases Hchans with ⟨%γp, %γr, %γc, %γcs, %γrd, %γa, %γt, %γd, %γs, %γst, #Hcp, Hop, #Hcr, Hor,
    #Hcc, Hoc, #Hccs, Hocs, #Hcrd, Hord, #Hca, Hoa, #Hct, Hot, #Hcd, Hod, #Hcs, Hos, #Hcst, Host⟩
  let γn : NodeNames := { raft := γ, bud := bud, stor := interface.ok si, propc := γp,
                          recvc := γr, confc := γc, confstatec := γcs, readyc := γrd, advancec := γa, tick := γt,
                          done := γd, stop := γs, status := γst, dlv := γdlv, rof := γrof,
                          mode := RNMode.static, dlm := γdlm, cap := γcap, ccq := γccq, cam := γcam, req := γreq }
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
  ihave #Hnode : isNode γn cv.ID' np $$ []
  · unfold isNode
    iexists nv, r, lok'
    simp only [named]
    rw [Hnvrn]
    iframe #
  -- `go n.run()`
  wp_apply wp_fork $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam]
  · wp_apply wp_node_run γn cv.ID' np $$ [Hrn Hdlv1 Hrof1 Hrof2 Hdlm Hcap1 Hcam]
    · iframe Hnode
      unfold runPre
      iexists nv, _, (([], [], []) : List EntryM × List EntryM × List EntryM)
      rw [Hnvrn]
      iframe Hn Hrn Hrof1 Hrof2
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iframe Hdlv1 Hlb1
      unfold runCfg
      iframe Hdlm
      isplitr
      · ipureintro; exact ⟨rfl, Nat.le_refl _, rfl⟩
      iexists 0
      iframe Hcap1 Hcam
      ipureintro; exact ⟨Nat.le_refl _, NoConfIn_empty _ _⟩
    itrivial
  iapply HΦ
  iframe HR
  iexists γn, np
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  iframe Hnode Hpeers
  isplitl [Hdlv2 Hreq1 Hreq2]
  · unfold nodeDriver dlvLb
    iframe Hnode Hdlv2 Hdlb
    iexists _
    iframe Hreq1 Hreq2
  unfold nodeCfg
  iframe Hcap2 Hcamlb
  iexists _
  iframe Hccq1 Hccq2

end proof

end EtcdGrove
end Perennial
