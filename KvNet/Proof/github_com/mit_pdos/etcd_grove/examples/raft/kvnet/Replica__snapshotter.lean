/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Replica__snapshotter.lean`.
Lean-first (no Rocq counterpart; kvreconf's `Replica.snapshotter` proof, with the stored snapshot's
known index as an argument and the snapshotter's half of `nodeRunning`, sent back on `snapDone`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica__snapshotter
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica__snapshot
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem Replica.snapshotter.wp_proof (wp_snapshot : Replica.snapshot.spec (GF := GF) (hG := hG)) :
    Replica.snapshotter.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ρ known
  wp_start as ⟨#HR, #Hkn, #Hkni, Hrun⟩
  ihave #HR' := HR
  iunfold isReplicaR at HR'
  iNamed HR'
  try wp_auto
  ihave Hinv : iprop(∃ (k : w64) (qv : KSnapReq), "known" ∷ known_ptr ↦ k ∗ "req" ∷ req_ptr ↦ qv ∗
      "#Hk" ∷ memSnapLb ρ.γs (uint.nat k) ∗
      "#Hki" ∷ monoNatLbOwn ρ.ph.is (uint.nat k) ∗
      "Hrun" ∷ nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half) $$ [known req Hrun]
  · iexists known, _
    iframe known req Hrun Hkn Hkni
  wp_for Hinv
  wp_apply wp_bag_receive (t := github_com.mit_pdos.etcd_grove.examples.raft.kvnet.snapReq.ty) ρ.sn ρ.snc (snapReqOk γ ρ.key ρ.γs ρ.ph) $$ HsnB
    as %q Hq
  try wp_auto
  wp_apply wp_snapshot γ vs dir id r n st sts sq ρ q k (1 : Qp).half $$ [$HR $Hq $Hk $Hki $Hrun]
    as %k' ⟨#Hk', #Hki', Hrun⟩
  try wp_auto
  wp_for_post
  iframe
  iexists k', q
  iframe
  iframe Hk' Hki'

end proof

end raft_kvnet
end EtcdGrove
end Perennial
