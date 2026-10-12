/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/UnsafeCreateMetaBucket.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateMetaBucket

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

theorem schema.UnsafeCreateMetaBucket.wp_proof :
    schema.UnsafeCreateMetaBucket.spec (GF := GF) (hG := hG) := by
  intro tx P
  wp_start as ⟨HP, #HC⟩
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨⟨%mb, #Hmb⟩, -, -, -⟩
  wp_auto
  wp_bind (App (Val #(methods tx.ty _ tx.v)) (Val #mb))
  iapply HC $$ %mb [HP]
  · iexact HP
  inext
  iintro HP
  wp_auto
  iapply HΦ $$ HP

end proof

end EtcdGrove
end Perennial
