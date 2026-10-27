/-
Lean-first (no Rocq counterpart).

The proof of `kubernetes.New`: `clientv3.New`'s result, an allocation of the wrapper, its
`Kubernetes` field set to itself, then read-only.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kubernetes.New

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem New.wp_proof (wp_New : clientv3.New.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro cfg eps V
  wp_start as ⟨#Hcfg, %Htb⟩
  ihave #Pc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_New cfg eps V) $$ [] as %cl %err Hr
  · iframe #
    ipureintro; exact Htb
  icases Hr with (⟨%He, #Hnc⟩ | ⟨%He, %Hcl⟩)
  · subst He
    iapply wp_fupd
    wp_auto
    ipersist «$r0»
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists cl
    iframe «$r0» Hnc
  · cases err with
    | nil => exact absurd rfl He
    | ok ei =>
      wp_auto
      iapply HΦ
      iright
      ipureintro; exact He
end proof

end kubernetes
end EtcdGrove
end Perennial
