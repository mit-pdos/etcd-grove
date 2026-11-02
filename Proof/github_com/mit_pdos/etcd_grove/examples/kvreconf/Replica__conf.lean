/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__conf.lean`. Lean-first (no
Rocq counterpart): the configuration and the applied index read under the lock (`repShared`'s
halves), the configuration read-only.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__conf

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

theorem Replica.conf.wp_proof : Replica.conf.spec (GF := GF) (hG := hG) := by
  intro γr vs id r
  wp_start as #HisRep
  iunfold isRep at HisRep
  icases HisRep with ⟨%n, %st, %sts, %ρ, #HR⟩
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
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmW HW Hwaiters Hns Hseq HmR HRd Hreads HmA HA Hcs Hidx]
  · inext
    unfold lockInv
    iexists ns, mW, W, mR, Rd
    iframe
    isplitl
    · unfold repShared
      iexists mA, A, csp, c, idx, ap
      iframe
      iframe HcsO Hap
      ipureintro; exact HA
    · ipureintro; exact HRdom
  try wp_auto
  iapply HΦ
  iexists c
  iexact HcsO

end proof

end kvreconf
end EtcdGrove
end Perennial
