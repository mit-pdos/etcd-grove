/-
# `etcdserver/read`: the linearizable read loop (batch 2c), vocabulary

`read.go`: a `Read` batches the member's linearizable reads into rounds. A reader
(`LinearizableReadNotify`) takes the current round's notifier and wakes the loop; the loop
(`LinearizableReadLoop`) swaps in the next round's notifier, asks raft for a read index under a
fresh context (`requestCurrentIndex`: `ReadIndex`, retried with a new context every 500ms or on a
first commit in the term; `ErrLeaderChanged` on a leader change, `ErrTimeout` after the request
timeout), waits until the member has applied that index (`ApplyWait`), and closes the round's
notifier with `nil` (or the error). So a reader that returns `nil` knows: **the member has applied
an index the cluster had committed after the reader started**.

## Vocabulary

* `readEnv srv rf rγ γi A` (persistent): the contract of the two interfaces `NewRead` gets, the
  server `srv` (`*EtcdServer`) and raft `rf` (`&s.r`, the `*raftNode`), for raft cluster `rγ`
  (R1's `Raft.Cluster`), id space `γi` and applied-index predicate `A`:
  - `A i` (persistent, downward closed): the member has applied the committed log up to index `i`
    (so the committed log is at least `i` long: `A i ⊢ committedLb rγ l` with `i ≤ l.length`);
  - `AppliedIndex()` returns an `i` with `A i`; `ApplyWait(d)` a channel whose receive gives `A d`;
  - `NextRequestID()` a fresh id (`IdUtil.idFresh γi`);
  - `Done()`, `Stopping()`, `LeaderChanged()`, `FirstCommitInTermNotify()` channels (`recvAny`);
    `Logger()` a logger; `RequestTimeout()` a duration;
  - `rf.ReadIndex(ctx, rctx)` sends a read request for a registered context (R1's
    `node.ReadIndex.spec`); `rf.ReadState()` a channel of read states, each with R1's `readState`;
  - **the registration of a read context** (`□`, a fancy update): a fresh id's 8-byte big-endian
    context `be64 id` registered with raft (`Raft.readCtx_register`) under the read update that
    certifies a lower bound `l` of the committed log (`readLbQ l`: its result `⌜opsOf l <+: ops⌝`
    at the committed operations `ops` of the firing). The server holds raft's client-owned
    `readCtxs` and `committedOps` in its cluster invariant, so it is the one that can register and
    fire such updates; the loop only asks.
* `readNew r srv rf` (exclusive): `NewRead`'s result, before its environment is known (the server's
  `start` calls `NewRead` before it sets the fields `srv`'s methods read); `readNew_init` turns it,
  with `readEnv`, into the two below.
* `readAt r rγ A` (persistent): `r` serves linearizable reads for raft cluster `rγ`, applied-index
  predicate `A` (`LinearizableReadNotify.spec`).
* `readLoopTok r` (exclusive): the right to run the loop (once).
* `readErr err` (pure): `err` is one of the read path's errors: `ErrStopped`, `ErrLeaderChanged`,
  `ErrTimeout` (`etcdserver/errors`), raft's `ErrStopped`, a context's `Canceled` or
  `DeadlineExceeded`; all indefinite for the client (the server's law
  `EtcdServer.readErr_indef`).

## Intended realization

`readAt`: an invariant over the current notifier `nc` (its channel open, a ghost set of the lower
bounds its readers deposited, `committedLb`s, frozen at the swap) and the rounds swapped out but
not yet notified; the notifier's close with `nil` carries, for its frozen set, `committedLb rγ l' ∗
A l'.length` with every deposited bound's operations a prefix of `opsOf l'`. The loop: after the
swap it registers its fresh contexts with the longest deposited bound `l_need` (comparable, R1's
`committedLb_agree`); a matching read state `(be64 id, i)` (`readState_registered`, the 8-byte
decode injective), then `ApplyWait(i)`'s `A i`, which gives `committedLb rγ l` with `i ≤ l.length`,
let `readState_fire` give `l'` of length `i` with `opsOf l_need <+: opsOf l'`. `waitC` (buffer 1)
carries nothing.

## Requirement snippets

`examples/specreq/etcdserverreq/read.go` (`ReqReadAfterWrite`, `ReqReadErrIndef`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.read
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.read
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Api
public import Spec.go_uber_org.zap.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Read

open Iris Iris.BI

/-- The 8-byte big-endian encoding of `id` (`uint64ToBigEndianBytes`). -/
def be64 (id : w64) : List w8 :=
  (List.range 8).map (fun k => W8 ((uint.nat id / 2 ^ (8 * (7 - k)) % 256 : Nat) : Int))

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- A channel any goroutine may receive on (only ever closed, never sent a value anyone relies on). -/
def recvAny (ch : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, isChan ch γc Unit ∗
    □ ∀ Φ : Unit → Bool → IProp GF, (∀ v ok, Φ v ok) -∗ recvAu γc Unit Φ)

/-- The read update certifying the lower bound `l` of the committed log. -/
def readLbQ (l : List Raft.LogEntry) : List Raft.LogEntry → IProp GF :=
  fun ops => iprop(⌜Raft.opsOf l <+: ops⌝)

/-- `r` is `NewRead`'s result over `srv` and `rf`, its environment not yet given. Exclusive. -/
opaque readNew (r : Loc) (srv rf : GoInterface) : IProp GF := iprop(True)

/-- **`r` serves linearizable reads** for raft cluster `rγ`, applied-index predicate `A`.
Persistent. -/
opaque readAt (r : Loc) (rγ : Raft.Cluster) (A : Nat → IProp GF) : IProp GF := iprop(True)

/-- The right to run `r`'s loop. Exclusive. -/
opaque readLoopTok (r : Loc) : IProp GF := iprop(True)

def readAt_persistent.spec : Prop := ∀ r rγ A, Persistent (readAt (GF := GF) r rγ A)

end vocab

section errs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **`err` is one of the read path's errors** (see the header). -/
opaque readErr (err : GoInterface) : Prop

end errs

section env
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- A `ReadState` value read from `rf.ReadState()`: its context's bytes (read-only) and the read
state's fact. -/
def readStateVal (rγ : Raft.Cluster) (v : go_etcd_io.raft.v3.ReadState) : IProp GF :=
  iprop(∃ c : List w8, v.RequestCtx' ↦*□ c ∗ Raft.readState rγ c v.Index')

/-- The method call `v.m()` on an interface value of the read package's interface type `t`. -/
def call0 (v : GoInterface) (t : go.GoType) (m : GoString) : Expr :=
  App (Val (v @!! t @!! m)) (Val #())

/-- **The environment's contract** (see the header): the server's and raft's interface methods,
and the registration of read contexts. Persistent. -/
def readEnv (srv rf : GoInterface) (rγ : Raft.Cluster) (γi : IdUtil.IdSpace) (A : Nat → IProp GF) :
    IProp GF :=
  let st := go_etcd_io.etcd.server.v3.etcdserver.read.server.ty
  let rt := go_etcd_io.etcd.server.v3.etcdserver.read.raftInterface.ty
  iprop(
    ⌜(∀ a b : Nat, b ≤ a → A a ⊢ A b) ∧ (∀ a, Persistent (A a)) ∧
     (∀ i : Nat, A i ⊢ ∃ l, Raft.committedLb rγ l ∗ ⌜i ≤ l.length⌝) ∧
     ({{ True }} call0 srv st go!"Done" {{ (ch : Loc), RET #ch; recvAny ch }}) ∧
     ({{ True }} call0 srv st go!"Stopping" {{ (ch : Loc), RET #ch; recvAny ch }}) ∧
     ({{ True }} call0 srv st go!"LeaderChanged" {{ (ch : Loc), RET #ch; recvAny ch }}) ∧
     ({{ True }} call0 srv st go!"FirstCommitInTermNotify" {{ (ch : Loc), RET #ch; recvAny ch }}) ∧
     ({{ True }} call0 srv st go!"Logger" {{ (lg : Loc), RET #lg; Zap.isLogger lg }}) ∧
     ({{ True }} call0 srv st go!"RequestTimeout" {{ (d : w64), RET #d; True }}) ∧
     ({{ True }} call0 srv st go!"AppliedIndex" {{ (i : w64), RET #i; A (uint.nat i) }}) ∧
     ({{ True }} call0 srv st go!"NextRequestID" {{ (id : w64), RET #id; IdUtil.idFresh γi id }}) ∧
     (∀ d : w64, {{ True }} App (Val (srv @!! st @!! go!"ApplyWait")) (Val #d)
        {{ (ch : Loc), RET #ch; ∃ γc : ChanNames, isChan ch γc Unit ∗
            □ ∀ Φ : Unit → Bool → IProp GF, (∀ v ok, A (uint.nat d) -∗ Φ v ok) -∗
              recvAu γc Unit Φ }}) ∧
     ({{ True }} call0 rf rt go!"ReadState"
        {{ (ch : Loc), RET #ch; ∃ γc : ChanNames, isChan ch γc go_etcd_io.raft.v3.ReadState ∗
            □ ∀ Φ : go_etcd_io.raft.v3.ReadState → Bool → IProp GF,
              (∀ v ok, (⌜ok = true⌝ -∗ readStateVal rγ v) -∗ Φ v ok) -∗
              recvAu γc go_etcd_io.raft.v3.ReadState Φ }}) ∧
     (∀ (ctx : GoInterface) (rctx : GoSlice) (c : List w8) (Q : List Raft.LogEntry → IProp GF),
        {{ Context.ctxOk ctx ∗ rctx ↦*□ c ∗ Raft.readCtx rγ c Q }}
          App (App (Val (rf @!! rt @!! go!"ReadIndex")) (Val #ctx)) (Val #rctx)
        {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil ∨ readErr err⌝ }})⌝ ∗
    □ ∀ (id : w64) (l : List Raft.LogEntry), IdUtil.idFresh γi id -∗ Raft.committedLb rγ l -∗
      |={⊤}=> Raft.readCtx rγ (be64 id) (readLbQ l))

/-- **Starting the read path**: `NewRead`'s result, with its environment, serves reads, and its
loop may run. -/
def readNew_init.spec : Prop := ∀ (r : Loc) (srv rf : GoInterface) (rγ : Raft.Cluster)
    (γi : IdUtil.IdSpace) (A : Nat → IProp GF),
  readNew r srv rf ∗ readEnv srv rf rγ γi A ⊢ |={⊤}=> readAt r rγ A ∗ readLoopTok r

end env

end Read
end EtcdGrove
end Perennial
