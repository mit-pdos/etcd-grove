/-
`(*Page).FreelistPageIds`'s spec (`internal/common/page.go`; U0b of `notes/bbolt-proof-plan.md`).
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

/-- `p.FreelistPageIds()`: the ids of a freelist page, as a `[]Pgid` over the page (8 bytes each,
from index `idx` after the header: see `Page.FreelistPageCount`); `nil` if there are none. It
reads only the header and, for an overflowing count, the `Pgid` after it. It panics on a page
that is not a freelist page and on a negative overflow count: the premises exclude both. -/
abbrev Page.FreelistPageIds.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac) (c : w64),
  v.flags' = W16 16 → (v.count' = W16 65535 → 0 ≤ sint.Z c) →
  0 < l.addr →
  l.addr + 16 + 8 * (uint.Z (if v.count' = W16 65535 then W64 1 else W64 0) + sint.Z (if v.count' = W16 65535 then c else W64 (uint.Z v.count'))) ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v ∗
      (if v.count' = W16 65535 then (l +ₗ 16) ↦{dq} c else True) }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"FreelistPageIds")) (Val #()))
  {{ RET #(if (if v.count' = W16 65535 then c else W64 (uint.Z v.count')) = W64 0 then slice.nil
           else slice.mk (l +ₗ (16 + 8 * uint.Z (if v.count' = W16 65535 then W64 1 else W64 0)))
             (if v.count' = W16 65535 then c else W64 (uint.Z v.count')) (if v.count' = W16 65535 then c else W64 (uint.Z v.count')));
      l ↦{dq} v ∗ (if v.count' = W16 65535 then (l +ₗ 16) ↦{dq} c else True) }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
