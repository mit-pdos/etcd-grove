/-
`bootstrapBackend(cfg, haveWAL)` (`bootstrap.go:259-309` at the etcd pin `edc800c6f`; names-only, a
callee of `bootstrap`'s proof, `?` in the server's link until stage 4 proves it over the
`OpenBackend` axiom). Lean-first; claim #34, stage 3 (2026-11-23), `notes/bootstrap-proof-plan.md`
§7.3. Its vocabulary: `Proof/.../etcdserver/BootParts.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`bootstrapBackend(cfg, false)` at a first start**: for the configurations `bootstrap`'s contract
covers (`bootCfgOk`, a budget `N + 7 + bootWB ≤ wbInit`, bbolt opening the file, `dbOpensOk`), with a
zap logger, a feature gate `nil` or answering `NonBlockingDefrag`, `ETCD_VERIFY` off, and the backend
file's name free (`bootstrapSnapshot`'s post): no error, and the record `bk` with `bootOk`'s backend
rows (`bootBackendRows`: `Hci … Hbfile` but `Hnew`), the constructor's post `Hnew` over the data `D`
it leaves (`bootBackendNew`), `D`'s facts (`bootBackendData`: `Hm0`, `HD`, the rest buckets empty,
`HmEmpty`), no snapshot, and one write-back token (`Finalize`'s session's). `γA`, `cil`, `d`, `D` are
existential. Not `HDr`'s membership buckets: `Finalize`'s `SetBackend` creates them
(`bootstrappedCluster.Finalize.spec`).

Why it is true of Go: `fileutil.Exist(cfg.BackendPath())` is `false` on the free name (`:260`), so
`beExist` is false and the `Validate` branch (`:287-300`) is not taken; `NewConsistentIndex(nil)`,
`NewBackendHooks(cfg.Logger, ci)` (`:261-262`); `OpenBackend(cfg, beHooks)` (`:263`) opens a fresh
file (the empty data) with the hooks (`HhkAt`), at the configuration's batch limit (`Hbe`), the file
the configuration's backend path (`Hpath`, `Hbfile`); the apply protocol's names are a ghost allocation
(`consInv_alloc`) made before it, as `openPre`'s batch-lock resource needs; `ci.SetBackend(be)`
(`Hown`) and `CreateMetaBucket(be.BatchTx())` (`:269-270`: one session, `Meta` created empty, one
write-back token of the budget); no defragmentation (`BootstrapDefragThresholdMegabytes = 0`,
`bootCfgOk`); `haveWAL` false: no `recoverSnapshot`, `snapshot` nil (`:280-286`); `err` is never set,
so the deferred `Close` does not run. Of the budget, the session spent one, `Finalize` takes one and
`bootLeft N` keeps `N + 7` (`bootWB` is four). -/
abbrev bootstrapBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (N : Nat),
  bootCfgOk cfg → N + 7 + bootWB ≤ backend.wbInit → storage.dbOpensOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      zapLoggerOk cfg.Logger' ∗
      (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
      envVerifyOff ∗ backend.fileFree (config.backendPathOf cfg.DataDir') }}
    (App (App (Val (@! bootstrapBackend)) (Val #cfg)) (Val #false))
  {{ (bkl : Loc) (err : GoInterface), RET (PairV #bkl #err);
      ⌜err = GoInterface.nil⌝ ∗
      ∃ (bk : bootstrappedBackend) (γA : ApplyNames) (cil : Loc) (d : mvcc.KBReal) (D : backend.Data),
        bkl ↦ bk ∗ ⌜bk.snapshot' = null ∧ bootBackendData γA d D⌝ ∗
        bootBackendRows cfg bk γA cil d ∗ bootBackendNew N γA d D ∗ backend.wbTok d.γB }}

end spec

end EtcdGrove
end Perennial
