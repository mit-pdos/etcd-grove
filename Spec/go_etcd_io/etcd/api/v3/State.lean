/-
# etcd's abstract state as a resource (batch W0, the anchor)

The resource every client-facing atomic update of etcd acts on, shared by the client (`client/v3`)
and the server batches that must produce it (the cluster contract, `notes/specs-only/top.md`).

## Vocabulary

* `Cluster`: opaque ghost names of one etcd cluster (one replicated state).
* `etcdState γ σ` (exclusive, timeless): **the cluster `γ`'s state is `σ`** (`Model.lean`'s
  `State`). Whoever starts the cluster gets it in full (the cluster contract) and keeps it, usually
  in an invariant of its own; the cluster changes it only through the atomic updates the clients
  hand to their calls (`client/v3/Api.lean`) and through the environment's permission
  (`envUpd`). Intended realization: a ghost variable's half (`ghostVar γ.st ½ σ`) whose other half
  the cluster's invariant (2c/2d: the KV model of the committed raft log) keeps, with the
  authoritative side of `γ.hist`, the append-only list of the states the committed log has passed
  through (the `etcdLb`s below).
* `etcdLb γ σ` (persistent, timeless): **the cluster's state has been `σ`** (`σ` is in its
  history). Built from what every member shares (the committed log's states), never from one
  member's store (PRINCIPLES, "A client's certificate is the cluster's"). Laws: snapshot from
  the state (`etcdState_lb`), the current state is reachable from it (`etcdLb_reach`), two of them
  are ordered (`etcdLb_ord`). This is the one persistent fact clients carry between calls (a
  revision reached, a history prefix, a lease granted, a user added: all pure consequences of
  `Reach σ₀ σ`, which clients prove themselves from the model).
* `etcdN`: the namespace the cluster's invariants live in; a client's atomic updates are fired
  under `⊤ \ ↑etcdN`.
* `envUpd γ cfg` (transparent; persistent): **the environment's permission**: a persistent atomic
  update that performs any `EnvStep cfg` on `etcdState γ` (`cfg`: whether the members
  auto-compact). The state's owner gives it to the cluster when it
  starts one (or a member: every start spec of the server batches takes it, `top.md`), so that
  lease expiry, auto-compaction, alarms and members' publications happen without a client call. The
  owner keeps whatever invariant it likes over `etcdState`, as long as it is stable under
  `EnvStep` (a client that never names leases and never compacts below what it reads sees only the
  compaction and the publications). Decision (W0): a permission handed over once, rather than a
  client invariant the specs would have to name, because it keeps every client spec's atomic
  update about the client's own request only.
* `errVal e`: the Go value of rpctypes' error `e` (`rpctypes.ErrCompacted`, ...): a non-nil
  `rpctypes.EtcdError` interface value; distinct errors have distinct values. That rpctypes' package
  variables hold these values is a law of rpctypes (batch 2a, `req/go_etcd_io_etcd_api_v3_v3rpc_rpctypes.md`).

## Laws (obligations of the cluster's implementation)

`etcdState_timeless`, `etcdState_excl`, `etcdLb_persistent`, `etcdLb_timeless`, `etcdState_lb`,
`etcdLb_reach`, `etcdLb_ord`, `etcdState_revFits`, `etcdState_sizeFits`, `errVal_inj`, `errVal_ty`.

`etcdState_revFits`, `etcdState_sizeFits`: the current revision and the number of events fit an
`int64` (a reply's header, `Count`, `Version`, `Deleted` carry them). etcd itself never refuses at
`2 ^ 63` (mvcc wraps), so the cluster's invariant keeps the bounds from a **step budget** fixed by
the adequacy theorem: a counted resource (as Perennial's thread tokens) of which every committed
entry spends one and each entry writes a bounded number of events (`--max-txn-ops` per level,
nesting bounded by the request size), held by the cluster's invariant (bounds plan: the bound at
its owner); no client spec carries a bound.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.Model
public import GeneratedProof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdModel

open Iris Iris.BI

/-- Ghost names of one etcd cluster: opaque. -/
opaque Cluster : Type := Unit

/-- The namespace of the cluster's invariants. -/
def etcdN : Namespace := nroot .@ "etcd"

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The cluster `γ`'s state is `σ`** (exclusive). -/
opaque etcdState (γ : Cluster) (σ : State) : IProp GF := iprop(True)

/-- **The cluster `γ`'s state has been `σ`** (persistent). -/
opaque etcdLb (γ : Cluster) (σ : State) : IProp GF := iprop(True)

def etcdState_timeless.spec : Prop := ∀ (γ : Cluster) (σ : State), Timeless (etcdState (GF := GF) γ σ)

def etcdState_excl.spec : Prop := ∀ (γ : Cluster) (σ σ' : State),
  etcdState (GF := GF) γ σ ∗ etcdState γ σ' ⊢ iprop(False)

def etcdLb_persistent.spec : Prop := ∀ (γ : Cluster) (σ : State), Persistent (etcdLb (GF := GF) γ σ)

def etcdLb_timeless.spec : Prop := ∀ (γ : Cluster) (σ : State), Timeless (etcdLb (GF := GF) γ σ)

/-- A snapshot of the current state. -/
def etcdState_lb.spec : Prop := ∀ (γ : Cluster) (σ : State),
  etcdState (GF := GF) γ σ ⊢ etcdState γ σ ∗ etcdLb γ σ

/-- The current state is reachable from every state the cluster has been in. -/
def etcdLb_reach.spec : Prop := ∀ (γ : Cluster) (σ₀ σ : State),
  etcdLb (GF := GF) γ σ₀ ∗ etcdState γ σ ⊢ ⌜Reach σ₀ σ⌝

/-- The states the cluster has been in are ordered: its history is one sequence. -/
def etcdLb_ord.spec : Prop := ∀ (γ : Cluster) (σ₁ σ₂ : State),
  etcdLb (GF := GF) γ σ₁ ∗ etcdLb γ σ₂ ⊢ ⌜Reach σ₁ σ₂ ∨ Reach σ₂ σ₁⌝

/-- The current revision fits a reply's `int64`. -/
def etcdState_revFits.spec : Prop := ∀ (γ : Cluster) (σ : State),
  etcdState (GF := GF) γ σ ⊢ ⌜σ.kv.rev < 2 ^ 63⌝

/-- The number of events in the history fits an `int64` (so does every count of keys, every
version, every `Deleted`: each needs an event). -/
def etcdState_sizeFits.spec : Prop := ∀ (γ : Cluster) (σ : State),
  etcdState (GF := GF) γ σ ⊢ ⌜(σ.kv.revs.map List.length).sum < 2 ^ 63⌝

/-- **A member of the cluster `γ` serves etcd's v3 API at the endpoint `ep`** (persistent; the
cluster contract, `notes/specs-only/top.md`): gRPC handlers registered at that address answer
every request by `Step`, firing the callers' updates as the client's contract says
(`client/v3/Api.lean`). Produced by the server batches when a member starts serving (2a's handlers,
2e's `Serve`), consumed by the client's dialer (1c: `connOk`). -/
opaque servesAt (γ : Cluster) (ep : GoString) : IProp GF := iprop(True)

def servesAt_persistent.spec : Prop := ∀ γ ep, Persistent (servesAt (GF := GF) γ ep)

/-- **The environment's permission** (see the header): any environment step of a cluster
configured as `cfg`, at any time. -/
def envUpd (γ : Cluster) (cfg : EnvCfg) : IProp GF :=
  iprop(□ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
    <{ ∀∀ (σ' : State), ⌜EnvStep cfg σ σ'⌝ ∗ etcdState γ σ', COMM True }>)

end res

section errs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **The Go value of rpctypes' error `e`** (`rpctypes.ErrCompacted` for `.compacted`, ...). -/
opaque errVal (e : EtcdErr) : GoInterface := GoInterface.nil

/-- Distinct errors are distinct values. -/
def errVal_inj.spec : Prop := ∀ (e e' : EtcdErr), errVal e = errVal e' → e = e'

/-- An `rpctypes.EtcdError` value (so not `nil`, not a context's error, not a gRPC status). -/
def errVal_ty.spec : Prop := ∀ (e : EtcdErr), ∃ v : val,
  errVal e = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty v

/-- **An error that settles nothing** (after which the request may still take effect): not `nil`,
and if one of etcd's errors then an indefinite one (`EtcdErr.indefinite`); a context's error, a
gRPC status, a transport error are such errors. -/
def indefErr (err : GoInterface) : Prop :=
  err ≠ GoInterface.nil ∧ ∀ e : EtcdErr, err = errVal e → e.indefinite = true

end errs

end EtcdModel
end EtcdGrove
end Perennial
