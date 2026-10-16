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

/-- `s.NewUberApplier()`: `apply.NewUberApplier`'s result in the environment `E`, over the options
it builds of the server's fields (read-only), for which `apply.NewUberApplier.spec`'s premise
holds (`backendOptsOk`, at whatever `TxnModeWriteWithSharedBuffer` the feature gate answers and
with the server itself as the raft status and the snapshot server), with the auth store's reader
resource. (`backendOptsOk` asks `isApplyKV` of `s.kv`: false for `NewServer`'s watchable store
until unit N4.) -/
abbrev EtcdServer.NewUberApplier.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (lg a cl : Loc) (kv au le ci be fg : GoInterface) (quota : w64)
    (wad : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ srvKVAddr s ↦□ kv ∗ srvAlarmStoreAddr s ↦□ a ∗
      srvAuthStoreAddr s ↦□ au ∗ srvLessorAddr s ↦□ le ∗ srvClusterAddr s ↦□ cl ∗
      srvCIAddr s ↦□ ci ∗ srvBeAddr s ↦□ be ∗
      srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗ isFeatureGate fg ∗
      srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ quota ∗
      srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ wad ∗
      □ (∀ opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions,
        ⌜opts.Logger' = lg ∧ opts.KV' = kv ∧ opts.AlarmStore' = a ∧ opts.AuthStore' = au ∧
          opts.Lessor' = le ∧ opts.Cluster' = cl ∧ opts.ConsistentIndex' = ci ∧
          opts.Backend' = be ∧ opts.QuotaBackendBytesCfg' = quota ∧
          opts.WarningApplyDuration' = wad⌝ -∗ apply.backendOptsOk E opts) ∗
      E.RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"NewUberApplier")) (Val #()))
  {{ (ua : GoInterface), RET #ua; ∃ (p : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions),
      ⌜ua = interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty) #p⌝ ∗ apply.uberIs E p opts ∗
      ∃ ns cr : Bool, apply.uberOwn E p (apply.alarmChain E.authOn ns cr) }}

end spec

end EtcdGrove
end Perennial
