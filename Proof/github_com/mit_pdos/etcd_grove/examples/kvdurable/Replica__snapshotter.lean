/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__snapshotter.lean`.
Lean-first (no Rocq counterpart; kvreconf's `Replica.snapshotter` proof, with the stored snapshot's
known index as an argument and the snapshotter's half of `nodeRunning`, sent back on `snapDone`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__snapshotter
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__snapshot
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Replica.snapshotter.wp_proof (wp_snapshot : Replica.snapshot.spec (GF := GF) (hG := hG)) :
    Replica.snapshotter.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ρ known
  wp_start as ⟨#HR, Hprod, #Hkn, #Hkni, Hrun⟩
  ihave #HR' := HR
  iunfold isReplicaR at HR'
  iNamed HR'
  try wp_auto
  ihave Hinv : iprop(∃ k : w64, "known" ∷ known_ptr ↦ k ∗ "#Hk" ∷ memSnapLb ρ.γs (uint.nat k) ∗
      "#Hki" ∷ monoNatLbOwn ρ.ph.is (uint.nat k) ∗
      "Hprod" ∷ handoffProducer ρ.sd false ∗
      "Hrun" ∷ nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half) $$ [known Hprod Hrun]
  · iexists known
    iframe known Hprod Hrun Hkn Hkni
  wp_for_core
  iNamed Hinv
  try wp_auto
  cleanup_bool_decide
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a request
    simp only [chan.blockingClausePre]
    iexists KSnapReq, inferInstance, inferInstance, inferInstance, inferInstance, ρ.snc, ρ.sn
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ HsnB
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] HsnB
    inext
    iintro %q Hq
    wp_auto
    wp_apply wp_snapshot γ vs dir id r n st sts sq ρ q k (1 : Qp).half $$ [$HR $Hq $Hk $Hki $Hrun]
      as %k' ⟨#Hk', #Hki', Hrun⟩
    try wp_auto
    wp_for_post
    iframe
    iexists k'
    iframe
    iframe Hk' Hki'
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `stopc` closed: the snapshotter's half of `nodeRunning` sent on `snapDone`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ρ.stopc, ρ.sc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ HstopB
    iapply broadcast_chan_receive _ _ _ _ _ $$ HstopB
    iintro ⟨-, -⟩
    try wp_auto
    wp_apply wp_handoff_send ρ.sd ρ.sdc (fun _ => nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half)
      iprop(True) iprop(False) () $$ [$HsdH $Hprod Hrun] as -
    · isplitl [Hrun]
      · iexact Hrun
      · itrivial
    try wp_auto
    wp_for_post
    try wp_auto
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end kvdurable
end EtcdGrove
end Perennial
