/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewKVAny.lean` (pr-verify etcd#21714). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewKVAny
public import Spec.go_etcd_io.etcd.client.v3.RetryKVClient

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem NewKVAny.wp_proof (wp_RetryKVClient : RetryKVClient.spec (GF := GF) (hG := hG)) :
    NewKVAny.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as #Hc
  iunfold clientConnAt at Hc
  icases Hc with ⟨%cl, #Hfix, #Hconn⟩
  iunfold clientFixed at Hfix
  icases Hfix with ⟨%Hne, -, -, -, -, -, -, -, -, -, -, -, #Hco, -⟩
  wp_auto
  wp_apply wp_RetryKVClient c cl.conn' $$ [] as %v ⟨%rkv, %Hv, -⟩
  · iexact Hconn
  subst Hv
  iStructNamed «$r0»
  simp only [decide_eq_false Hne]
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
