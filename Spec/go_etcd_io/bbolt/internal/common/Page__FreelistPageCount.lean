/-
`(*Page).FreelistPageCount`'s spec (`internal/common/page.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit

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

/-- `p.FreelistPageCount()`: the index of a freelist page's first id and its number of ids. The
count is the header's, unless that is `0xFFFF` (the overflow marker): then it is the `Pgid` `c`
just after the header, and the ids start one element later (index 1). It panics on a page that
is not a freelist page, and on an overflow count that is negative as an `int`: the premises
exclude both. -/
abbrev Page.FreelistPageCount.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac) (c : w64),
  v.flags' = W16 16 → (v.count' = W16 65535 → 0 ≤ sint.Z c) →
  0 < l.addr → l.addr + 16 ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v ∗
      (if v.count' = W16 65535 then (l +ₗ 16) ↦{dq} c else True) }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"FreelistPageCount")) (Val #()))
  {{ RET (PairV #(if v.count' = W16 65535 then W64 1 else W64 0)
        #(if v.count' = W16 65535 then c else W64 (uint.Z v.count')));
      l ↦{dq} v ∗ (if v.count' = W16 65535 then (l +ₗ 16) ↦{dq} c else True) }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
