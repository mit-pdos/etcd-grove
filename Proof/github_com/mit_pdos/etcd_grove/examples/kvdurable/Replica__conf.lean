/-
kvreconf's proof (the same Go text), ported. Proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__conf.lean`. Lean-first (no Rocq
counterpart): the lock's half of the replicated state holds the conf state (read-only).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__conf
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

theorem Replica.conf.wp_proof : Replica.conf.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r
  wp_start as #HisRep
  iunfold isRep at HisRep
  icases HisRep with ⟨%n, %st, %sts, %sq, %ρ, #HR⟩
  iunfold isReplicaR at HR
  iNamed HR
  ihave #Hrep' := Hrep
  iclear Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iNamed HL
  iNamed Hrep
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmW HW Hwaiters HmR HRd Hreads HmA HA Hcs Hidx]
  · inext
    unfold lockInv
    iexists mW, W, mR, Rd
    iframe
    unfold repShared
    iexists mA, A, csp, c, idx, ap
    iframe
    iframe HcsO Hap
    ipureintro; exact HA
  try wp_auto
  iapply HΦ
  iexists c
  iexact HcsO

end proof

end kvdurable
end EtcdGrove
end Perennial
