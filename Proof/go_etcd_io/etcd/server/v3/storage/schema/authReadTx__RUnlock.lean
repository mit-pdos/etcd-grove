/-
Proof of `Spec/.../schema/authReadTx__RUnlock.lean`: the transaction's `RUnlock` (its contract). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__RUnlock

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.authReadTx.RUnlock.wp_proof :
    schema.authReadTx.RUnlock.spec (GF := GF) (hG := hG) := by
  intro atx rt R Held D
  wp_start as ⟨#Htx, #Hrtx, HD⟩
  iunfold schema.authRTx at Hrtx
  icases Hrtx with ⟨-, #HRU⟩
  wp_auto
  wp_bind (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #()))
  iapply HRU $$ %D HD
  inext
  iintro HR
  (try wp_auto)
  iapply HΦ
  iexact HR

end proof

end EtcdGrove
end Perennial
