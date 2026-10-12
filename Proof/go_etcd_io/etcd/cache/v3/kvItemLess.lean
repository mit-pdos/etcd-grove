/-
Proof of `Spec/kvItemLess.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.kvItemLess

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

-- Loads from the read-only (`↦□`) `kvItem`s: the field-store `AccessStrict` instances
-- (which need `DFrac.own 1`) are found first and the search does not backtrack.
attribute [-instance] kvItem.kvItem_access_store_key kvItem.kvItem_access_store_kv

theorem kvItemLess.wp_proof : kvItemLess.spec (GF := GF) (hG := hG) := by
  intro a b ea eb
  rw [show decide (kvLess ea eb) = decide (go.GoStringLt ea.1 eb.1) from rfl]
  wp_start as ⟨Ha, Hb⟩
  unfold kvItemIs
  wp_auto
  wp_end

end proof

end EtcdGrove
end Perennial
