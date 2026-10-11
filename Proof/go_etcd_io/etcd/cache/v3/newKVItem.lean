/-
Proof of `Spec/newKVItem.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.newKVItem

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem newKVItem.wp_proof : newKVItem.spec (GF := GF) (hG := hG) := by
  intro e
  obtain ⟨k, l⟩ := e
  simp only [kvItemIs, kvAt]
  wp_start as ⟨%keySl, #Hl, #Hkey⟩
  wp_auto
  wp_apply wp_bytes_to_string _ k DFrac.discard $$ Hkey as _
  wp_alloc p as Hp
  ipersist Hp
  wp_end

end proof

end EtcdGrove
end Perennial
