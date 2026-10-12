/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/NewWithResponse.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.NewWithResponse

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

theorem wait.NewWithResponse.wp_proof : wait.NewWithResponse.spec (GF := GF) (hG := hG) := by
  intro ch
  wp_start
  wp_alloc chp as Hchp
  wp_auto
  wp_alloc p as Hp
  ipersist Hp
  iStructNamed Hp
  wp_auto
  iapply HΦ
  iexists p
  iframe ch
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
