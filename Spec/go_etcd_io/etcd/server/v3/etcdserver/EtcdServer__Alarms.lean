/-
`(*EtcdServer).Alarms()` (`server.go`: `return s.alarmStore.Get(pb.AlarmType_NONE)`). Lean-first (no
Rocq counterpart); verified for `etcd-io/etcd#22654` (`8fd98af04`: `applySnapshot` recovers
`s.alarmStore` in place via `AlarmStore.Recover` under `a.mu` instead of overwriting `s.alarmStore`
via `s.restoreAlarms()`, so `s.alarmStore` is read-only for good once `NewServer` finishes and
`s.Alarms()` is safe with only the persistent `srvAlarmStoreAddr s ↦□ a` and `isAlarmStore a`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.Alarms()` (`s.alarmStore.Get(pb.AlarmType_NONE)`) returns an owned slice of the server's
active alarms, reading `s.alarmStore` via its persistent read-only points-to (`srvAlarmStoreAddr s
↦□ a`) and acquiring `a.mu` (`isAlarmStore a`) without any lock on `s`. -/
abbrev EtcdServer.Alarms.spec : Prop :=
  ∀ (s a : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAlarmStoreAddr s ↦□ a ∗ isAlarmStore a }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Alarms")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ l : List Loc, sl ↦* l ∗ ownSliceCap Loc sl (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
