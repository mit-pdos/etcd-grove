/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__credentialsForEndpoint.lean` (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__credentialsForEndpoint
public import Spec.go_etcd_io.etcd.client.v3.internal.endpoint.RequiresCredentials

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.credentialsForEndpoint.wp_proof
    (wp_RequiresCredentials : endpoint.RequiresCredentials.spec (GF := GF) (hG := hG)) :
    Client.credentialsForEndpoint.spec (GF := GF) (hG := hG) := by
  intro c ep cr
  wp_start as ⟨#Hcr, %Hplain⟩
  ihave #Hep : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.endpoint $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_RequiresCredentials ep $$ [$Hep] as %r ⟨%Hr, %Hpl⟩
  rw [Hpl Hplain]
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
