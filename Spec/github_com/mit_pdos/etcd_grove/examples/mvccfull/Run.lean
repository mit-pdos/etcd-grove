/- Lean-first (no Rocq counterpart).

`Run(cfg)` (`examples/mvccfull/mvccfull.go`): the tester. **Every check passes** in every execution:
it returns the report. For every configuration within the run's resource bounds and F1's scope
(`runCfgOk`, below), from the package initialized, the configuration's weight slices (`mixOwn`, the
read weights `wr`), every file a run may create absent (`fileHolds p ∅` for each of `filePathsM cfg`,
`FilePaths.lean`), the store's key-count assumption (`keySized`, `etcdStorage_open.law`'s), the main
thread's token and `ETCD_VERIFY` unset (`backend.New`'s), and the environment premises mvccrand's
`Run.spec` takes: the lessor's checkpoint premise (`ckptEffectsOk`), bbolt's `Open` and `Close`
succeeding (`dbOpenOk`, `dbCloseOk`).

**`runCfgOk`** (on the normalized configuration where `normalize` changes a field): F1's scope
(`readMixOk` of `Mix.Read`: no hash read; `Readers.lean`); `0 ≤ Ops < 2 ^ 38` (the receipts' and
write-back tokens' budgets, `FilePaths`' loop); the threads, `2·Readers + 2·(2·Streams) + 3 ≤ 2 ^ 28`
(each reader and each stream goroutine a thread and a reader token of each store it reads); the
backend's batch limit at most `2 ^ 57` (`backend.New`'s `P.Wf`); the store's compaction batch limit
in mvcc's range (`batchLimitOk`, `New`'s); the keys within mvcc's state bound (`stateOk`: at most
`2 ^ 62`, `3 ^ Depth`-ish keys).

After `stopReaders`, `Run` calls the corruption checker (`x.hashes()`) only if `hashing(Mix.Read)`,
which `readMixOk` makes false (`hashingM_of_readMixOk`): F1's scope excludes the hashes, the readers'
and `Run`'s (`HashByRev` and `Hashes` have no spec until F2).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.FilePaths
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.normalize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The configuration's weight slices** (any fraction), the read weights at `wr`. -/
def mixOwn (mx : Mix) (wr : List w64) : IProp GF :=
  iprop(∃ (dq : DFrac) (ws wo wc wrr wa wst : List w64), mx.Step' ↦*{dq} ws ∗ mx.Op' ↦*{dq} wo ∗
    mx.CompactAt' ↦*{dq} wc ∗ mx.RangeRev' ↦*{dq} wrr ∗ mx.Read' ↦*{dq} wr ∗ mx.Act' ↦*{dq} wa ∗
    mx.Start' ↦*{dq} wst)

/-- **The run's bounds and F1's scope** (see the file header). -/
def runCfgOk (cfg : Config) (wr : List w64) : Prop :=
  readMixOk (wr.map sint.Z) ∧ 0 ≤ sint.Z cfg.Ops' ∧ sint.Z cfg.Ops' < 2 ^ 38 ∧
  2 * max 0 (sint.Z cfg.Readers') + 4 * max 0 (sint.Z cfg.Streams') + 3 ≤ 2 ^ 28 ∧
  sint.Z (limOf cfg) ≤ 2 ^ 57 ∧ batchLimitOk (cblOf cfg) ∧
  (keysOf (sint.nat (normalizeM cfg).Depth')).length ≤ 2 ^ 62

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ (cfg : Config) (wr : List w64) [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 38)],
  runCfgOk cfg wr → ckptEffectsOk → backend.dbOpenOk → backend.dbCloseOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      mixOwn cfg.Mix' wr ∗ ([∗list] p ∈ filePathsM cfg, backend.fileHolds p ∅) ∗
      □ (∀ (γB : backend.BNames) (P : backend.BParams) (b : Loc), keySized γB P b) ∗
      threadTok ∗ envVerifyOff }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.Run)) (Val #cfg))
  {{ (rep : Report), RET #rep; True }}

end spec

end mvccfull
end EtcdGrove
end Perennial
