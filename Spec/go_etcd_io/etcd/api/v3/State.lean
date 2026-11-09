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
`etcdState_sizeFits`, `errVal_inj`, `errVal_ty`; across a crash (verify round, crash pass)
`etcdState_gen`, `etcdLb_gen`, `urlsRight_gen`, `urlsReserve_gen`, `soleMember_gen`, `peerLeaseServed_gen`,
`envUpd_gen`; the lease views' `leaseViewLb_persistent`, `leaseViewLb_zero`, `leaseViewLb_le`,
`soleMember_persistent`, `peerLeaseServed_persistent`. Shared shapes: `etcdPerm γ T`, `etcdPeek γ`.

`etcdState_revFits`, `etcdState_sizeFits`: the current revision and the number of events fit an
`int64` (a reply's header, `Count`, `Version`, `Deleted` carry them). etcd itself never refuses at
`2 ^ 63` (mvcc wraps), so the cluster's invariant keeps the bounds from a **step budget** fixed by
the adequacy theorem: a counted resource (as Perennial's thread tokens) of which every committed
entry spends one and each entry writes a bounded number of events (`--max-txn-ops` per level,
nesting bounded by the request size), held by the cluster's invariant (bounds plan: the bound at
its owner); no client spec carries a bound. Since these laws are plain entailments (they cannot
open the cluster's invariant), the bounds are part of the **half the program holds**: the intended
realization of `etcdState γ σ` is `ghostVar γ.st ½ σ ∗ ⌜σ.kv.rev + 1 < 2 ^ 63 ∧ (σ.kv.revs.map
List.length).sum < 2 ^ 63⌝`, the cluster's invariant establishing the pure part at every commit
(it updates both halves, and spends the step budget there), and `etcdLb γ σ` carries the same pure
part for each state of the history (verify round, A1-provability F9).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.Model
public import GeneratedProof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.Api

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
opaque etcdState [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (σ : State) : IProp GF := iprop(True)

/-- **The cluster `γ`'s state has been `σ`** (persistent). -/
opaque etcdLb [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (σ : State) : IProp GF := iprop(True)

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
opaque servesAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (ep : GoString) : IProp GF := iprop(True)

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
the member's applied index: `i = 0` (nothing known: every table index is `≥ 0`, and the cluster
always has table `0`, `State.leaseTables` being nonempty), or `∃ id, srvEp γ ep id ∗` member
`id`'s lessor view of `i`. -/
opaque leaseViewLb [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (ep : GoString) (i : Nat) : IProp GF := iprop(True)

def leaseViewLb_persistent.spec : Prop := ∀ γ ep i, Persistent (leaseViewLb (GF := GF) γ ep i)

/-- **The trivial view** (verify-round F2, `verify/F-client-api.md`): any member's lessor is at a
table `≥ 0`, so a lease read through `ep` may always bound itself by table `0` (and gets the view
of the table it was answered at). No premise: the realization's `i = 0` case (above); every
consumer's claim at `i = 0` (an answer at a table `≥ 0`; `leaseViewLb_le`'s `0 < length`) holds of
every state. Replaces the `⌜i = 0⌝ ∨` alternative of 1c's `viaPre`, which 2a's `etcdUnary` had no
source for. -/
def leaseViewLb_zero.spec : Prop := ∀ γ ep, ⊢ leaseViewLb (GF := GF) γ ep 0

/-- **The cluster `γ` never has a member but its one initial member** (persistent; open question
A4's single-member alternative, recheck RR-1): so whichever member serves an endpoint is the
cluster's only voter, its leader whenever it has one, and a `TimeToLive` answered through it is its
own lessor's (`ClientV3.viaFact`, 2a's `leaseFact`: the leader answers from its lessor
(`v3_server.go:636-669`); before an election the member forwards to the leader's peer URLs, its
own, whose `leasehttp` handler looks the lease up in the same lessor (`:671-676`,
`leasehttp/http.go:109-160`)). Introduced by 2e's `soleMember_intro` (`etcdserver/ApiBoot.lean`)
from the boot token of a one-member cluster and the whole `urlsReserve γ 1`: every member addition
(`MemberAdd`, `MemberAddAsLearner`, hence every promotion) takes a `urlsRight`, which only
`urls_reserve` mints, from a share of `urlsReserve`; so no URL set was reserved before and none can
be after, and no reconfiguration adds a member while it is held (a removal of the only member
leaves no voter, and so no answer: raft refuses or panics, `nonissues/raft-remove-last-voter-panic.md`).
Intended realization: an invariant holding `urlsReserve γ 1`, with the cluster's initial member
list (2d's cluster invariant: every member is an initial one or added under a reserved URL set). -/
opaque soleMember [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) : IProp GF := iprop(True)

def soleMember_persistent.spec : Prop := ∀ γ, Persistent (soleMember (GF := GF) γ)

/-- **Every member of `γ` serves its own lessor's lease endpoint on its peer URLs** (persistent;
verify-round F1, `verify/F-client-api.md`): a deployment fact, for each member `m` of a state the
cluster reached and each `u ∈ m.peerURLs`, `u ++ "/leases/internal"` is answered by
`leasehttp.NewHandler(s.lessor, s.ApplyWait)` of a server object of `m` (embed's peer handler,
`etcdhttp.newPeerHandler`, mounts `s.LeaseHandler()` there; `examples/lib/etcdstart` serves only
`s.RaftHandler()`, whose mux answers `404`, so it is false there). What a `TimeToLive` forwarded by
a member to its leader (`v3_server.go:671-686`) needs for its answer to be the leader's lessor's,
not the mux's `404`. Introduced by 2e's `peerLeaseServed_intro` (`etcdserver/ApiBoot.lean`) for a
one-member cluster whose member's peer URLs are lease endpoints (4b's deployment premise
`Leasehttp.leasePeerURL`); eliminated by 2e's `peerLeaseServed_url` into 4b's
`Leasehttp.leaseURLOf`. Intended realization: `□ ∀ σ m u ep, etcdLb γ σ -∗ ⌜m ∈ σ.members ∧ u ∈
m.peerURLs⌝ -∗ srvEp γ ep m.id -∗ leaseURLOf γ ep (u ++ "/leases/internal")` (2e's and 4b's
vocabulary). -/
opaque peerLeaseServed [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) : IProp GF := iprop(True)

def peerLeaseServed_persistent.spec : Prop := ∀ γ, Persistent (peerLeaseServed (GF := GF) γ)

/-- **A share `q` of the right to reserve new peer-URL sets for `γ`** (fractional; recheck RR-1):
`cluster_alloc` gives it whole and `urls_reserve` spends a share (2e, `etcdserver/ApiBoot.lean`;
repair3-boot): a program that has reserved no URL set keeps it whole and may give it
up for `soleMember γ`. -/
opaque urlsReserve [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (q : Qp) : IProp GF := iprop(True)

def urlsReserve_fractional.spec : Prop := ∀ (γ : Cluster) (q₁ q₂ : Qp),
  urlsReserve (GF := GF) γ (q₁ + q₂) ⊣⊢ urlsReserve γ q₁ ∗ urlsReserve γ q₂

/-- A member's lessor is at a table the cluster has had. -/
def leaseViewLb_le.spec : Prop := ∀ (γ : Cluster) (ep : GoString) (i : Nat) (σ : State),
  leaseViewLb (GF := GF) γ ep i ∗ etcdState γ σ ⊢ ⌜i < σ.leaseTables.length⌝

/-- **The right to give a member of `γ` the peer URLs `urls`, once** (exclusive; moved here from
2e's `EtcdServer.urlsRight`, `etcdserver/ApiBoot.lean`, at integration I1, so that a client can hold
it): taken by a client's `MemberAdd`/`MemberAddAsLearner`/`MemberUpdate` (1c's
`Cluster.MemberAddTriple`, `Cluster.MemberUpdateTriple`, `reqRight`) and by the server's
`AddMember`/`UpdateMember` (2e); minted, with the joiner's `memberJoin`, by 2e's `urls_reserve`
(the URLs' hosts reserved for the cluster's network). The initial members' URL sets have none. -/
opaque urlsRight [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (urls : List GoString) : IProp GF := iprop(True)

/-- One right per URL set (up to order). -/
def urlsRight_excl.spec : Prop := ∀ (γ : Cluster) (urls urls' : List GoString), urls.Perm urls' →
  urlsRight (GF := GF) γ urls ∗ urlsRight γ urls' ⊢ iprop(False)

/-- **The right at the URLs' parsed forms** (verify round, A8-completeness F2, server-boot's
request): a client holds `urlsRight` at the raw strings it sends; the member compares and stores
the parsed URLs' `String()` forms (`Types.urlsNorm`, `types.NewURLs`), so the right converts to them
for a list `NewURLs` accepts. Intended realization: the right is keyed by `urlsNorm` of its strings
(a ghost token per normalized multiset), so the law is `Types.urlsNorm_idem`; `urlsRight_excl` by
`Types.urlsNorm_perm`. Still spent when the request is refused (`ApiClient.lean`'s `reqRight`:
margin). -/
def urlsRight_norm.spec : Prop := ∀ (γ : Cluster) (urls : List GoString), Types.urlsValid urls →
  urlsRight (GF := GF) γ urls ⊢ urlsRight γ (Types.urlsNorm urls)

/-- **`tok` is a token the cluster issued to user `u`** (persistent; `Authenticate`'s answer, 1c and
3d; also the tokens a member issues itself: `WithRoot`'s root tokens, the JWTs its keys sign): a
request carrying it is `u`'s, or refused once it is invalid or stale. -/
opaque tokenUser [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : Cluster) (tok : GoString) (u : GoString) : IProp GF := iprop(True)

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

/-! ### Across a crash (verify round, crash pass: R-A8 N1)

Perennial's crash rule hands the next generation `L'` (a new local ghost state: heap, threads,
crash token) only invariants and the crash frame; every opaque predicate takes the heap `hG`. The
cluster's state is the committed log's, durable on a quorum (K6), and its resources are of the
global ghost state: **the same at the next generation's heap `⟨hG.goose_globalGS, L'⟩`**, so the
program's invariant over `etcdState`, a client's `etcdLb`s and the permissions it handed out serve
every generation. Realization: `etcdState`'s ghost variable half, `etcdLb`'s history fragment and
`urlsRight`'s token are `own`s of `GF`'s ghost names (and pure facts), the cluster's invariants are
at `etcdN` (`GooseGlobalGS`'s invariants); nothing is of a heap, a thread or a crash token. -/

/-- **`etcdState` does not depend on the local generation.** -/
def etcdState_gen.spec : Prop := ∀ (L' : GooseLocalGS GF) (γ : Cluster) (σ : State),
  etcdState (GF := GF) γ σ ⊣⊢ etcdState (hG := ⟨hG.goose_globalGS, L'⟩) γ σ

/-- **`etcdLb` does not depend on the local generation.** -/
def etcdLb_gen.spec : Prop := ∀ (L' : GooseLocalGS GF) (γ : Cluster) (σ : State),
  etcdLb (GF := GF) γ σ ⊣⊢ etcdLb (hG := ⟨hG.goose_globalGS, L'⟩) γ σ

/-- **`urlsRight` does not depend on the local generation** (a joiner's right reserved before a
crash is spent after it). -/
def urlsRight_gen.spec : Prop := ∀ (L' : GooseLocalGS GF) (γ : Cluster) (urls : List GoString),
  urlsRight (GF := GF) γ urls ⊣⊢ urlsRight (hG := ⟨hG.goose_globalGS, L'⟩) γ urls

/-- **`urlsReserve` and `soleMember` do not depend on the local generation** (recheck RR-1's
resources: a program that reserved no URL set before a crash still holds the whole right after). -/
def urlsReserve_gen.spec : Prop := ∀ (L' : GooseLocalGS GF) (γ : Cluster) (q : Qp),
  urlsReserve (GF := GF) γ q ⊣⊢ urlsReserve (hG := ⟨hG.goose_globalGS, L'⟩) γ q

def soleMember_gen.spec : Prop := ∀ (L' : GooseLocalGS GF) (γ : Cluster),
  soleMember (GF := GF) γ ⊣⊢ soleMember (hG := ⟨hG.goose_globalGS, L'⟩) γ

/-- `peerLeaseServed` does not depend on the local generation (a restarted member's new server
object serves the same peer URLs; its realization is over `srvEp`, `srvEp_gen`). -/
def peerLeaseServed_gen.spec : Prop := ∀ (L' : GooseLocalGS GF) (γ : Cluster),
  peerLeaseServed (GF := GF) γ ⊣⊢ peerLeaseServed (hG := ⟨hG.goose_globalGS, L'⟩) γ

/-- **The environment's permission serves the next generation** (`NewServer`'s premise after a
restart; transparent over `etcdState`, so a consequence of `etcdState_gen`, stated so that no
client unfolds the atomic update: the update's masks are the global invariants'). -/
def envUpd_gen.spec : Prop := ∀ (L' : GooseLocalGS GF) (γ : Cluster) (cfg : EnvCfg),
  envUpd (GF := GF) γ cfg ⊢ envUpd (hG := ⟨hG.goose_globalGS, L'⟩) γ cfg

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
