/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/waitWithResponse__Register.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.waitWithResponse__Register

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

theorem wait.waitWithResponse.Register.wp_proof :
    wait.waitWithResponse.Register.spec (GF := GF) (hG := hG) := by
  intro p ch id
  wp_start as #Hch
  wp_auto
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
