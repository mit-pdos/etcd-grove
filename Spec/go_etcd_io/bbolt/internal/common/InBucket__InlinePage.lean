/-
`(*InBucket).InlinePage`'s spec (`internal/common/bucket.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `b.InlinePage(v)`: the page inline in a bucket's value, after the 16-byte bucket header
(`&v[BucketHeaderSize]`). Pure in the address; `b` is not read. It panics unless `v` is longer than
the header: a premise. -/
abbrev InBucket.InlinePage.spec : Prop :=
  ∀ (l : Loc) (buf : GoSlice),
  16 < sint.Z buf.len → 0 < buf.ptr.addr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (Val (l @!! go.GoType.PointerType InBucket.ty @!! go!"InlinePage")) (Val #buf))
  {{ RET #(buf.ptr +ₗ 16); True }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
