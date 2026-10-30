/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__snapshotter.lean`.
Lean-first (no Rocq counterpart; kvreconf-snapshot-thread, 2026-10-30).

`ticker`'s shape: a loop over a blocking `select` of a receive from `snapc` (a bag: the request
with what it carries, `snapReqOk`, handed to `snapshot`) and of `stopc`'s close (then the send on
`snapDone`). The loop's invariant: `known` a lower bound of the stored snapshot's index
(`memSnapLb`, at `0` from `isReplicaR`) and `snapDone`'s producer token.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__snapshotter
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__snapshot
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Replica.snapshotter.wp_proof (wp_snapshot : Replica.snapshot.spec (GF := GF) (hG := hG)) :
    Replica.snapshotter.spec (GF := GF) (hG := hG) := by
  intro γr vs id r n st sts ρ
  wp_start as ⟨#HR, Hprod⟩
  ihave #HR' := HR
  iunfold isReplicaR at HR'
  iNamed HR'
  try wp_auto
  ihave Hinv : iprop(∃ k : w64, "known" ∷ known_ptr ↦ k ∗ "#Hk" ∷ memSnapLb ρ.γs (uint.nat k) ∗
      "Hprod" ∷ handoffProducer ρ.sd false) $$ [known Hprod]
  · iexists zero_val w64
    iframe known Hprod
    rw [show uint.nat (zero_val w64 : w64) = 0 from rfl]
    iexact HsnLb
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
    iexists RSnapReq, inferInstance, inferInstance, inferInstance, inferInstance, ρ.snc, ρ.sn
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ HsnB
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] HsnB
    inext
    iintro %q Hq
    wp_auto
    wp_apply wp_snapshot γr vs id r n st sts ρ q k $$ [$HR $Hq $Hk] as %k' #Hk'
    try wp_auto
    wp_for_post
    iframe
    iexists k'
    iframe
    iexact Hk'
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `stopc` closed
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ρ.stopc, ρ.sc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ HstopB
    iapply broadcast_chan_receive _ _ _ _ _ $$ HstopB
    iintro ⟨-, -⟩
    try wp_auto
    wp_apply wp_handoff_send ρ.sd ρ.sdc (fun _ => iprop(True)) iprop(True) iprop(False) ()
      $$ [$HsdH $Hprod] as -
    · isplitl <;> itrivial
    try wp_auto
    wp_for_post
    try wp_auto
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
