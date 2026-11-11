/-
`(*Meta).Validate`'s spec (`internal/common/meta.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit
public import Proof.go_etcd_io.bbolt.Model.Meta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace common

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `m.Validate()`: `nil` exactly when the meta is valid (`metaValid`: bbolt's magic, version 2, and
its checksum is `Sum64`'s); otherwise `ErrInvalid` (bad magic), `ErrVersionMismatch` (bad version)
or `ErrChecksum` (bad checksum), which are not `nil`. -/
abbrev Meta.Validate.spec : Prop :=
  ∀ (l : Loc) (v : Meta) (dq : DFrac),
  0 < l.addr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"Validate")) (Val #()))
  {{ (e : GoInterface), RET #e; l ↦{dq} v ∗ ⌜e = GoInterface.nil ↔ metaValid v⌝ }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
