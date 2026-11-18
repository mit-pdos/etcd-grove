/-
The etcd model, continued: transactions and leases (Lean-first, no Rocq counterpart). See
`decisions.md`, "the transaction model: sequential ops at one revision, per prefix; leases
without liveness; the create-revision persistence law".

**Transactions, purely.** A transaction (`TxnModel`) is a list of comparisons (`CmpModel`,
`InvCmp.lean`) and two lists of operations (`TxnOp`: a get, a put or a delete). etcd evaluates
the comparisons on its state `s` (`cmpHolds`, etcd's `applyCompare`: a comparison on a range
holds if it holds of every key in it; on no key, it reads the zero key-value — create and mod
revision, version and lease `0` — **except a value comparison, which then fails**), and runs the
chosen branch's operations **in order, each on the state the previous one left** (`runOps`,
`applyTxnOp`), all at one revision `r`: a put of a new key creates it with create and mod
revision `r` and version `1`; a put of an existing key keeps its create revision, sets its mod
revision to `r`, increments its version, and sets its value and lease (or keeps the lease: a
put with `WithIgnoreLease`, `putKeep`); a delete removes the keys
its range selects; a get reads the state at that point (`rangeSel`: the keys in its range,
filtered by its revision filters; the response sorts and limits them, `rangeKvsOk`). The
revision advances only if the transaction wrote (`txnWrote`: a put, or a delete of at least one
key); a read-only transaction is answered at the current revision, whose state it leaves as it
was.

**The client's `Txn`** (`isEtcdTxnKV kv pfx`, a definition like `isEtcdKV`): `kv.Txn(ctx)`
returns a builder `t` (a `clientv3.Txn` interface value) with an abstract state `B` (its
`TxnBuild`: the model so far and which of `If`/`Then`/`Else` were called); `If(cs...)`,
`Then(ops...)`, `Else(ops...)` append to the model (each once, in that order: otherwise the
client panics) and return `t`; `Commit()`, for a transaction whose keys are all under `pfx`
and with what the caller knows etcd has reached (`etcdReached lo`), returns an error, or a
response (`txnCommitResult`) at a revision `r ≥ lo` that etcd has reached, with a state `s`
(sorted, under `pfx`) such that: `resp.Succeeded` is `(runTxn r s t).1`; the responses are the
chosen operations' results; if the transaction wrote, `s` was etcd's state at `r - 1` and
`(runTxn r s t).2.1` is its state at `r`; otherwise `s` is its state at `r`. The builder's
methods are the trust boundary (the client's `txn` calls protobuf's `proto.Clone` and gRPC):
see `decisions.md`.

**History laws** (fields of `EtcdModel`, axioms until the vertical slice's unit V1; about
`etcdState`): every key-value of etcd's state at `r` has
`0 < createRev ≤ modRev ≤ r` and `0 < version` (`etcdState_revs`); a key present at `r`
with create revision `c` is present, with the same create revision, at every revision in
`[c, r]` (`etcdState_create_persist`: a key is created once and lives until it is deleted); and
two states holding a key with the same mod revision hold the same key-value
(`etcdState_modrev_det`: a revision writes a key at most once).

**A written revision is one commit's** (`etcdRevToken r`, a field of `EtcdModel` with its
exclusivity law
`etcdRevToken_excl`): every committed write is its own revision, so the client's contract hands
the caller of a writing commit an exclusive token for the revision it made (`txnCommitResultTok`,
`putResult`); a read-only transaction makes no revision (etcd answers it at the current one) and
gets no token.

**Linearizability** holds for a transaction with an operation that is not a serializable get
(`TxnModel.linearizable`); etcd answers one of serializable gets alone, or of no operation, from
the member's state, which may lag (`EtcdServer.Txn`, `IsTxnSerializable`).

**Read transactions** (`isEtcdReadTxnKV`): a transaction of gets alone, each at the current
revision or at an earlier one (`WithRev`): `Commit()` returns each get's range response on
etcd's state at its revision (`readTxnResult`); the STM's reads.

**Leases** (`isEtcdLease l`, a definition): `Grant` returns an error or a lease ID other than
`NoLease` with a header revision etcd has reached; `KeepAlive` returns an error, or a channel
(nil or not) on which a receive yields any response or the close (`isChanAny`: no promise that
the stream lasts; the close is the sender's, whose token the caller does not hold); `Revoke` returns an error or a response whose header revision etcd has
reached. What a lease does to keys (a put with `WithLease(id)` records `id` in the key-value;
the lease's expiry or revocation deletes them, a step of etcd's history like any other) is not
stated beyond the put's `lease`: nothing about liveness.

**`client/v3/experimental/recipes`' additions**: puts (`putTxn`, `putResult`, `isEtcdPutKV`: a put
as the one-operation transaction `Then(OpPut(...))`, as a delete is `deleteTxn`), the contracts at
`context.TODO()` (`isEtcdKVTodo`, `isEtcdTxnKVTodo`, `isEtcdDeleteKVTodo`, `isEtcdPutKVTodo`:
`TODO()`'s context is not an `isContext`; the get's response also has its `More` flag,
`getRespMore`). Their range watches are `isEtcdRangeWatcher`'s, whose channel may close (unit
W-Q, 2026-10-16: the recipes are verified against the closed-watch fix, so no premise that the
channel stays open).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvWatcher
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.SavedProp
public import Perennial.Proof.sync.RWMutexGuard
public import Proof.go_etcd_io.etcd.cache.v3.EtcdModel
public import Lean
public import Perennial.Proof.context
public import Proof.go_opentelemetry_io.otel.trace.Defs
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import Code.google_golang_org.grpc.metadata
public import Perennial.GeneratedProof.context
public import Code.net
public import Code.google_golang_org.grpc.credentials
public import Code.google_golang_org.grpc.peer
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Perennial.Ghost.MonoList
public import Perennial.Proof.errors

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## Key ranges and comparisons -/

/-- A missing key, as etcd compares it: revisions, version and lease `0`, empty value. -/
def zeroKv (k : GoString) : EtcdKv :=
  { key := k, createRev := W64 0, modRev := W64 0, version := W64 0, value := [], lease := W64 0 }

/-! ## Transactions -/

/-! ### The size of a transaction's request (2026-10-30, `opWireLen`) -/

/-! ### Bounding a transaction's size by its shape (L-s4)

A transaction whose every key, range end, operand and value is at most `N` bytes (`bytesLe N`), with
at most `M` comparisons and operations at every depth (`nodes`), has a request of at most
`M * (3 * N + 256)` bytes (`txnSizeOk_of_bounds`). -/

/-- A put of `key` at revision `r` (see the module docstring). -/
def putKv (r : w64) (key value : GoString) (lease : w64) (s : List EtcdKv) : List EtcdKv :=
  let nv : EtcdKv := match s.find? (fun v => decide (v.key = key)) with
    | some v => { v with modRev := r, version := v.version + W64 1, value := value, lease := lease }
    | none => { key := key, createRev := r, modRev := r, version := W64 1, value := value,
                lease := lease }
  btInsert etcdKvLess nv s

/-! ## History laws: the fields of `EtcdModel` (`EtcdModel.lean`) -/

section client
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]

/-! ## The client's transactions -/

/-! ## Read transactions: gets at the current or an earlier revision -/

/-! ## The client's deletes -/

/-! ## The client's puts (`client/v3/experimental/recipes`' addition) -/

/-! ## The client at `context.TODO()` (`client/v3/experimental/recipes`' addition) -/

/-! ## The client's range watch (a key, or a prefix) -/

/-! ## Leases -/

end client

/-! ## Small shared lemmas (outside `client`: only the variables each needs) -/

section pointwise
variable {GF : BundledGFunctors}

end pointwise

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

end heap

end EtcdGrove
end Perennial
