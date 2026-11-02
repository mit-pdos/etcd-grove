/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__stop.lean`. Lean-first
(no Rocq counterpart).

`close(stopc)` with the stopper's `Pending` token; `<-runDone` hands over the loop's
`nodeRunning 1` (a close that follows no send carries `False`); `<-tickDone`; then `node.Stop`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__stop
public import Spec.go_etcd_io.raft.v3.node__Stop

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

theorem Replica.stop.wp_proof (wp_Stop : node.Stop.spec (GF := GF) (hG := hG)) :
    Replica.stop.spec (GF := GF) (hG := hG) := by
  intro γr vs r
  wp_start as Hs
  iunfold repStop at Hs
  icases Hs with ⟨%id, %n, %st, %sts, %ρ, #HR, Hpend, Hrd, Htd, Hsd⟩
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
  wp_apply wp_handoff_receive ρ.rd ρ.rdc (fun _ => nodeRunning n γr.cluster kvrRaftN 1)
    iprop(True) iprop(False) false $$ [$HrdH $Hrd] as %u %ok ⟨-, Hgot⟩
  unfold handoffGot
  ihave Hrun : nodeRunning n γr.cluster kvrRaftN 1 $$ [Hgot]
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
  wp_apply wp_handoff_receive ρ.sd ρ.sdc (fun _ => iprop(True)) iprop(True) iprop(False) false
    $$ [$HsdH $Hsd] as %u'' %ok'' -
  try wp_auto
  wp_apply wp_Stop n γr.cluster kvrRaftN id $$ [$Hraft $HisNode $Hrun] as -
  iapply HΦ
  itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
