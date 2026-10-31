/-
`(*lessor).Lookup` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.Lookup(id)` (read-locked), by the lease owner (`leaseOwn γl L I`; the lease-keys plan,
item 3, 2026-10-31: until then by any share of the live set): the lease map's lease of `id`,
nil exactly when `id` is not live; a lease is the owner's lease of `id`, so the owner's resource
comes back opened at it (`leaseOwnOpen`: its item set, which `Keys()` reads), else as it was. -/
abbrev lease.lessor.Lookup.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id : w64) (L : List w64) (I : GMap LeaseItem w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorRd lp γl ∗ leaseOwn γl L I }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Lookup")) (Val #id))
  {{ (l : Loc), RET #l; lessorRd lp γl ∗ ⌜l = null ↔ id ∉ L⌝ ∗
      ((⌜l = null⌝ ∗ leaseOwn γl L I) ∨ leaseOwnOpen γl L I id l) }}
end spec

end EtcdGrove
end Perennial
