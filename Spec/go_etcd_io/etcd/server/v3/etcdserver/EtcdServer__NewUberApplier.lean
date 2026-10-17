/-
`(*EtcdServer).NewUberApplier()` (`server.go`: `apply.NewUberApplier` over the server's fields).
Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- `s.NewUberApplier()`: `apply.NewUberApplier`'s result over the options it builds of the
server's fields (read-only; the server itself as the raft status and the snapshot server), with
the auth store's reader resource `RD`; its contract (`uberIs`, `uberOwn`) in every environment
`E` whose reader resource is `RD` and for which `apply.NewUberApplier.spec`'s premise holds
(`backendOptsOk E opts`), given after the call (unit N4, 2026-10-17: the environment's post-lock
hook is installed after the call, `server.go:412`; until then `backendOptsOk` was a premise, at
any `TxnModeWriteWithSharedBuffer` and with `RaftStatus`/`SnapshotServer` unconstrained, which no
caller could discharge). The alarm store is the real one (`isAlarmStore a`: its `Get`). -/
abbrev EtcdServer.NewUberApplier.spec : Prop :=
  ∀ (s lg a cl : Loc) (kv au le ci be fg : GoInterface) (quota : w64)
    (wad : time.Duration) (RD : IProp GF) (dq : DFrac) (T : IProp GF) (z : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ srvKVAddr s ↦□ kv ∗ srvAlarmStoreAddr s ↦□ a ∗
      srvAuthStoreAddr s ↦□ au ∗ srvLessorAddr s ↦□ le ∗ srvClusterAddr s ↦□ cl ∗
      srvCIAddr s ↦□ ci ∗ srvBeAddr s ↦{dq} be ∗
      srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗ isFeatureGate fg ∗
      srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ quota ∗
      srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ wad ∗
      isAlarmStore a ∗ RD ∗ apply.alarmGetIs a T z ∗ T }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"NewUberApplier")) (Val #()))
  {{ (ua : GoInterface), RET #ua; srvBeAddr s ↦{dq} be ∗ T ∗ ∃ (p : Loc)
        (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions),
      ⌜ua = interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty) #p⌝ ∗
      ⌜opts.Logger' = lg ∧ opts.KV' = kv ∧ opts.AlarmStore' = a ∧ opts.AuthStore' = au ∧
        opts.Lessor' = le ∧ opts.Cluster' = cl ∧ opts.ConsistentIndex' = ci ∧
        opts.Backend' = be ∧ opts.QuotaBackendBytesCfg' = quota ∧
        opts.WarningApplyDuration' = wad ∧
        opts.RaftStatus' = interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s ∧
        opts.SnapshotServer' = interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s⌝ ∗
      ∀ E : apply.AEnv GF, ⌜E.RD = RD⌝ -∗ apply.backendOptsOk E opts -∗
        apply.uberIs E p opts ∗ ∃ ns cr : Bool, ⌜z = true → ns = false ∧ cr = false⌝ ∗
          apply.uberOwn E p (apply.alarmChain E.authOn ns cr) }}

end spec

end EtcdGrove
end Perennial
