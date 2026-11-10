/- Lean-first (no Rocq counterpart).

`runChecks(cfg)` (`examples/mvccrand/mvccrand.go`): the tester's run up to the store's close. It
opens a backend in the file `cfg.Path` (fresh: `fileHolds cfg.Path ∅`), makes the lessor and the
store over it as etcd's server does, installs the post-lock hook, checks the new store's revision,
and runs the writer (`cfg.Ops` operations), `cfg.Readers` readers and the watch stream's two
goroutines concurrently, every result checked against the model; then it closes the stream and the
store. **Every check passes**: the result is the report with the lessor and the backend, with the
right to stop the lessor (`lessorStopTok`) and what the backend's `Close` takes (its contract and
stop channels at the store's write invariant, and its whole open token `bOpen 1`: every reader of
the backend done, `stop_census_open`). (2026-11-08, for the closed theorem, the user's decision:
under `dbOpenOk`, bbolt's `Open` succeeding, so `backend.New` does not panic; until then the post
admitted `New`'s panic, the user's decision of 2026-11-06.)

The premises: the configuration's bounds (`make(chan int64, Watchers)` takes a capacity below
`2 ^ 32`; `wg.Add(2 + Readers)`, each of the `Readers + 2` users of the history, the writer,
the receiver and the readers, holds one of its lock's `actualMaxReaders = 2 ^ 30 - 1` reader slots,
`History.lean`, and each of the store's `Readers + 2` readers, the writer, the registrar and the
readers, one of its reader tokens (`mvccReaders`, of which `New` gives `mvccReaderN`, at least
`2 ^ 28`): `Readers + 2 ≤ 2 ^ 28`; the writer's lease grants spend one of the backend's `2 ^ 40 - 1` write-back tokens
each, the store's receipt-paid supply as many as there are receipts: `Ops < 2 ^ 38` and
`receiptBound ≤ 2 ^ 38`), the thread bound of the backend's reader pool (`2 ^ 28`), the lessor's
checkpoint premise (`ckptEffectsOk`, `lease.NewLessor.spec`'s), and `dbOpenOk` (`Open_kv`'s
environment premise). (Premise fixes 5, 2026-11-10) The store's key-count premise `keySized`
(`etcdStorage_open.law`'s) is proved (`mvcc.keySized_all`), no longer a premise here.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev runChecks.spec : Prop :=
  ∀ (cfg : Config) [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 38)],
  0 ≤ sint.Z cfg.Ops' → sint.Z cfg.Ops' < 2 ^ 38 →
  0 ≤ sint.Z cfg.Readers' → sint.Z cfg.Readers' + 2 ≤ 2 ^ 28 →
  0 ≤ sint.Z cfg.Watchers' → sint.Z cfg.Watchers' < 2 ^ 32 →
  ckptEffectsOk → backend.dbOpenOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      backend.fileHolds cfg.Path' ∅ ∗
      -- (R8, 2026-11-08, the second `lean` merge) the main thread's token, for `backend.New`'s
      -- first read transaction (begin-tok, `notes/begin-tok-plan.md`)
      threadTok ∗
      -- (2026-11-08, `lean`'s sweep repairs: the `ETCD_VERIFY` finding) the environment leaves
      -- `ETCD_VERIFY` unset, which `backend.New` takes (as etcdstart's start resources do)
      envVerifyOff }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.runChecks)) (Val #cfg))
  {{ (rep : Report) (lp b : Loc) (γB : backend.BNames) (P : backend.BParams) (W : IProp GF),
      RET (PairV (PairV #rep #(lease.lessorIface lp))
        #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b));
      lease.lessorStopTok lp ∗ backend.isBackend γB P W iprop(True) b ∗
      backend.isStopChans γB P W iprop(True) b ∗ backend.bOpen γB 1 }}

end spec

end mvccrand
end EtcdGrove
end Perennial
