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
`etcdLb_reach`, `etcdLb_ord`, `etcdLb_init`, `etcdState_revFits` (with one to spare),
`etcdState_sizeFits`, `errVal_inj`, `errVal_ty`. Shared shapes: `etcdPerm γ T`, `etcdPeek γ`.

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

/-- The current revision fits a reply's `int64`, with one to spare (a client computes
`Header.Revision + 1`: the recipes' watch starts). -/
def etcdState_revFits.spec : Prop := ∀ (γ : Cluster) (σ : State),
  etcdState (GF := GF) γ σ ⊢ ⌜σ.kv.rev + 1 < 2 ^ 63⌝

/-- Every state the cluster has been in has a revision that fits, with one to spare (for clients
that hold only an `etcdLb`, not the state). -/
def etcdLb_revFits.spec : Prop := ∀ (γ : Cluster) (σ : State),
  etcdLb (GF := GF) γ σ ⊢ ⌜σ.kv.rev + 1 < 2 ^ 63⌝

/-- **etcd never stores the empty key** (a put, alone or in a transaction, of the empty key is
refused by the gRPC layer's validation: `PutReq.invalid`, `TxnReq.valid`): no event of any state
an `etcdLb` names puts or deletes it, and no store of its history holds it. -/
def etcdLb_keyNonEmpty.spec : Prop := ∀ (γ : Cluster) (σ : State),
  etcdLb (GF := GF) γ σ ⊢
    ⌜(∀ evs ∈ σ.kv.revs, ∀ e ∈ evs, (match e with | .put k _ => k | .delete k => k) ≠ []) ∧
      ∀ (r : Nat) (k : Key) (kr : KeyRec), σ.kv.storeAt r k = some kr → k ≠ []⌝

/-- **Every state the cluster has been in comes from an initial one** (its provenance: a present
key's create revision is at least 2, its mod revision the revision of the event that wrote it, its
version at least 1; pure consequences of `Reach`). -/
def etcdLb_init.spec : Prop := ∀ (γ : Cluster) (σ : State),
  etcdLb (GF := GF) γ σ ⊢ ⌜∃ ms : List Member, Reach (State.init ms) σ⌝

/-- **Leases of a reached state** (3a's request, round 1 item 6; pure consequences of `Reach`, as
`etcdLb_init` gives, stated once): no lease table has lease `0` (a grant never chooses nor accepts
`0`: `leaseStep .leaseGrant`), and every present key's non-zero lease is live (a put checks its
lease, `PutReq.check`; a revocation, the client's or the environment's, deletes the keys attached). -/
def etcdLb_leases.spec : Prop := ∀ (γ : Cluster) (σ : State),
  etcdLb (GF := GF) γ σ ⊢
    ⌜(∀ t ∈ σ.leaseTables, t 0 = none) ∧
      ∀ (k : Key) (kr : KeyRec), σ.kv.store k = some kr → kr.lease ≠ 0 → σ.leases kr.lease ≠ none⌝

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

/-- **The auth state had index `lo` or more before now** (persistent; `lo = 0` always): what a read
spec takes to bound the auth states its permission check may see (`Step`'s `lo`,
`State.authOffSince`). A caller gets it from an `etcdLb` it holds (taken at the call's start inside
its own invariant, or any earlier one). -/
def authLb (γ : Cluster) (lo : Nat) : IProp GF :=
  iprop(⌜lo = 0⌝ ∨ ∃ σ0 : State, etcdLb γ σ0 ∗ ⌜lo < σ0.authTables.length⌝)

/-- **A permission to change the cluster's state by `T`** (transparent, persistent): a persistent
atomic update performing any transition `T σ σ'`, whose commit gives `etcdLb` of both states.
The one shape the client libraries take from their callers (1d's sessions, mutexes, STMs; 1f's
recipes; 1g's cache): a library builds each request's update from it. -/
def etcdPerm (γ : Cluster) (T : State → State → Prop) : IProp GF :=
  iprop(□ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
    <{ ∀∀ (σ' : State), ⌜T σ σ'⌝ ∗ etcdState γ σ', COMM etcdLb γ σ ∗ etcdLb γ σ' }>)

/-- **A permission to look** (persistent): `etcdPerm` of the transitions that change nothing (the
reads of 1f's recipes and 1g's cache). -/
def etcdPeek (γ : Cluster) : IProp GF := etcdPerm γ (fun σ σ' => σ' = σ)

/-- **A member's lessor has reached lease table `i`** (persistent; `State.leaseTables`): the member
serving `ep` reflects table `i` or a later one, and answers its lease reads (`Leases`; `TimeToLive`
on the leader) from a table at least `i`. Produced by 1c's lease specs from the server (a grant
answered through `ep` gives the table after it; a read answered through `ep` at table `j` gives
`j`), consumed by them (a read through `ep` holding `leaseViewLb γ ep i` is answered at a table
`≥ i`): what `examples/etcd/{leasegrant,leaseexpiry,leasecatchup}` carry. Realized by 2c/2d from
the member's applied index. -/
opaque leaseViewLb (γ : Cluster) (ep : GoString) (i : Nat) : IProp GF := iprop(True)

def leaseViewLb_persistent.spec : Prop := ∀ γ ep i, Persistent (leaseViewLb (GF := GF) γ ep i)

/-- A member's lessor is at a table the cluster has had. -/
def leaseViewLb_le.spec : Prop := ∀ (γ : Cluster) (ep : GoString) (i : Nat) (σ : State),
  leaseViewLb (GF := GF) γ ep i ∗ etcdState γ σ ⊢ ⌜i < σ.leaseTables.length⌝

/-- **`tok` is a token the cluster issued to user `u`** (persistent; `Authenticate`'s answer, 1c and
3d; also the tokens a member issues itself: `WithRoot`'s root tokens, the JWTs its keys sign): a
request carrying it is `u`'s, or refused once it is invalid or stale. -/
opaque tokenUser (γ : Cluster) (tok : GoString) (u : GoString) : IProp GF := iprop(True)

def tokenUser_persistent.spec : Prop := ∀ γ tok u, Persistent (tokenUser (GF := GF) γ tok u)

/-- A token names one user. -/
def tokenUser_agree.spec : Prop := ∀ γ tok u u',
  tokenUser (GF := GF) γ tok u ∗ tokenUser γ tok u' ⊢ ⌜u = u'⌝

/-- No user has the empty name in any state the cluster has had (`UserAdd` refuses it). -/
def etcdLb_noEmptyUser.spec : Prop := ∀ (γ : Cluster) (σ : State),
  etcdLb (GF := GF) γ σ ⊢ ⌜∀ a ∈ σ.authTables, a.users [] = none⌝

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

/-- **A hash matches its own password** (bcrypt's documented contract; trusted, 3d's boundary). -/
def pwHash_match.spec : Prop := ∀ pw cred : Bytes, pwHash pw cred → pwMatch cred pw

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
