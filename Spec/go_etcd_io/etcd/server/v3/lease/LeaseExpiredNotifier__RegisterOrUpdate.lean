/-
`(*LeaseExpiredNotifier).RegisterOrUpdate` (`server/lease/lease_queue.go`). Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `mq.RegisterOrUpdate(item)`, `item` a fresh item of id `id` the caller owns: the notifier
stays a notifier (an item already registered under `id` takes `item`'s time and moves in the
heap; otherwise `item` is pushed and registered). -/
abbrev lease.LeaseExpiredNotifier.RegisterOrUpdate.spec : Prop :=
  ∀ (np item : Loc) (id k : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ notifierAt np 1 ∗
      lwtAt item id k 1 }}
    (App (Val (np @!! go.GoType.PointerType LeaseExpiredNotifier.ty @!! go!"RegisterOrUpdate"))
      (Val #item))
  {{ RET #(); notifierAt np 1 }}

end spec

end EtcdGrove
end Perennial
