/-
`(*Page).FastCheck`'s spec (`internal/common/page.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit

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

/-- `p.FastCheck(id)` returns when the page's header has the id `id` and a valid type (flags
branch, leaf, meta or freelist). It panics otherwise (through `fmt.Sprintf`): the premises exclude
it. -/
abbrev Page.FastCheck.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac) (id : w64),
  v.id' = id → (v.flags' = W16 1 ∨ v.flags' = W16 2 ∨ v.flags' = W16 4 ∨ v.flags' = W16 16) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"FastCheck")) (Val #id))
  {{ RET #(); l ↦{dq} v }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
