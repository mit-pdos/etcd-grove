/- Lean-first (no Rocq counterpart).

`Main(clients, ops)` (`examples/etcd/txnlin/etcd_txnlin.go`; linkv-txn stage G): one etcd member started
in process (as `examples/linkv`'s `Main`, on `linkvtxn`'s ports), a client with etcd's
default configuration (its default retries; D29), and `Check(cli, clients, ops, 0)`, with a panic if porcupine reports the
history `Illegal`.

**The triple:** from the package's `isPkgInit`, the right to listen on the client address
`127.0.0.1:23796`, the main thread's token and `Main`'s named premises (`etcd_txnlin.premises`,
putget's at `linkvtxn`'s configuration, `Proof/.../linkvtxn/MainDefs.lean`), `Main(clients, ops)` does
not panic and returns `Ok` (the check ran: the history is linearizable) or `Unknown` (a step
before the check failed). The pure premises are putget's (`etcd_putget.Main.spec`: the member id and
bootstrap log, the thread and time-receipt bounds, the server's workload and effect premises,
gRPC's method sets, `errors.As`'s target, the method-set classes of `*errorString`) and `Run`'s bounds on
`clients` and `ops`. Stated under the cache package's assumptions, as putget's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.MainDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Base
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (clients ops : w64),
  etcd_putget.BootFacts id ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  -- (per-type stage B3) the levels of a thread token the server's gRPC runs use
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → grpcRepliesFit →
  storage.diskOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
      -- (2026-11-05, hub step 7) the member's start bundle: its WAL directory fresh and the right
      -- to listen on its client address (`netAddrFree`, which program start gives once: D19d)
      etcdstart.memberStartRes (GF := GF) go!"linkvtxn" ⟨none, some go!"127.0.0.1:23796"⟩ ∗
      threadTok ∗ premises N id ctxs boot }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Main)) (Val #clients))
      (Val #ops))
  {{ (r : GoString), RET #r; ⌜r = go!"Ok" ∨ r = go!"Unknown"⌝ }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
