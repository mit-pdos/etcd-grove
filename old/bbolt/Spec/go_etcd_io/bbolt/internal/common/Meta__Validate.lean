module
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Sum64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]
-- `hash.Hash64`'s type (its underlying interface): `internal/common` reaches `hash` only
-- through `hash/fnv`, so its `Assumptions` do not include `hash`'s
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- A meta is valid: bbolt's magic number, version 2, and its checksum is the hash of the
rest. -/
def metaValid (v : Meta) : Prop :=
  v.magic' = W32 3977042669 ∧ v.version' = W32 2 ∧ v.checksum' = fnv64a ((metaBytes v).take 56)

/-- `m.Validate()`: `nil` if the meta is valid, otherwise one of bbolt's errors
(`ErrInvalid`, `ErrVersionMismatch`, `ErrChecksum`). -/
abbrev Meta.Validate.spec : Prop :=
  ∀ (l : Loc) (v : Meta) (dq : DFrac),
  l.locCar ≠ 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"Validate")) (Val #()))
  {{ (e : GoInterface), RET #e; l ↦{dq} v ∗
      ⌜(e = interface.nil ↔ metaValid v) ∧ (e = interface.nil ∨ IsNewErr e)⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
