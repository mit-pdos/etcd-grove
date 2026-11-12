/-
`(*Meta).Sum64`'s spec (`internal/common/meta.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit
public import Proof.go_etcd_io.bbolt.Model.Meta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace common

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `m.Sum64()`: FNV-64a over the meta's bytes before its checksum, its first 56 (`metaSum`; read
through a `*[56]byte` view of `*m`, hashed by `hash/fnv`). -/
abbrev Meta.Sum64.spec : Prop :=
  ∀ (l : Loc) (v : Meta) (dq : DFrac),
  0 < l.addr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"Sum64")) (Val #()))
  {{ RET #(metaSum v); l ↦{dq} v }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
