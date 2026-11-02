/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__stop.lean`.
Lean-first (no Rocq counterpart; kvreconf's `Replica.stop` proof, with `run`'s and the snapshotter's
halves of `nodeRunning` received on `runDone` and `snapDone`, and `node.Stop`'s `nodeVacant`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__stop
public import Spec.go_etcd_io.raft.v3.node__Stop
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

theorem Replica.stop.wp_proof (wp_Stop : node.Stop.spec (GF := GF) (hG := hG)) :
    Replica.stop.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r
  wp_start as Hs
  iunfold repStopper at Hs
  icases Hs with ⟨%n, %st, %sts, %sq, %ρ, #HR, Hpend, Hrd, Htd, Hsd⟩
  ihave #HR' := HR
  iunfold isReplicaR at HR'
  iNamed HR'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Htt : □ (True : IProp GF) $$ []
  · imodintro; itrivial
  try wp_auto
  wp_apply wp_broadcast_chan_close ρ.stopc ρ.sc iprop(True) $$ [$Hpend $Htt] as -
  try wp_auto
  wp_apply wp_handoff_receive ρ.rd ρ.rdc (fun _ => iprop(nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
      ∃ v : Option GName × RaftState, ghostVar ρ.ph.ph (1 : Qp).half v))
    iprop(True) iprop(False) false $$ [$HrdH $Hrd] as %u %ok ⟨-, Hgot⟩
  unfold handoffGot
  ihave ⟨Hrun1, Hclaim⟩ : iprop(nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
      ∃ v : Option GName × RaftState, ghostVar ρ.ph.ph (1 : Qp).half v) $$ [Hgot]
  · cases ok with
    | true => simp only [Bool.false_eq_true, ↓reduceIte]; icases Hgot with ⟨$, -⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hgot with ⟨-, Hf⟩
      iexfalso; iexact Hf
  try wp_auto
  wp_apply wp_handoff_receive ρ.td ρ.tdc (fun _ => iprop(True)) iprop(True) iprop(False) false
    $$ [$HtdH $Htd] as %u' %ok' -
  try wp_auto
  wp_apply wp_handoff_receive ρ.sd ρ.sdc (fun _ => nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half)
    iprop(True) iprop(False) false $$ [$HsdH $Hsd] as %u'' %ok'' ⟨-, Hgot2⟩
  unfold handoffGot
  ihave Hrun2 : nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half $$ [Hgot2]
  · cases ok'' with
    | true => simp only [Bool.false_eq_true, ↓reduceIte]; icases Hgot2 with ⟨$, -⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hgot2 with ⟨-, Hf⟩
      iexfalso; iexact Hf
  ihave Hrun : nodeRunning n γ.r.cluster kdRaftN ((1 : Qp).half + (1 : Qp).half) $$ [Hrun1 Hrun2]
  · iapply (nodeRunning_fractional n γ.r.cluster kdRaftN).fractional _ _ |>.2
    iframe Hrun1 Hrun2
  rw [Qp.half_add_half]
  try wp_auto
  wp_apply wp_Stop n γ.r.cluster kdRaftN id $$ [$Hraft $HisNode $Hrun] as ⟨-, Hvac⟩
  iapply HΦ
  iframe Hvac
  iexists n, st, sts, sq, ρ
  iframe HR Hclaim

end proof

end kvdurable
end EtcdGrove
end Perennial
