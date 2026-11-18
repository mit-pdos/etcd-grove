/-
**mvcc's API, its pure part** (frozen 2026-11-03, `notes/mvcc-api-candidate.md`; the statements
`Api.lean` states over it): the store's abstract state and its steps, a transaction's view, a watch
response, a watcher in the stream's state, the stream's state, the watch guarantee (`wsRecvOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer
public import Perennial.Std.ListBasics
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model2
public import Spec.go_uber_org.zap.Defs
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.SavedProp
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.bytes
public import Perennial.GeneratedProof.encoding.binary
public import Perennial.Golang.Theory
public import Code.google_golang_org.protobuf.reflect.protoreflect
public import GeneratedProof.google_golang_org.protobuf.internal.impl
public import Code.google_golang_org.protobuf.runtime.protoimpl
public import Code.go_etcd_io.etcd.api.v3.authpb
public import Perennial.GeneratedProof.context
public import Code.go_etcd_io.etcd.api.v3.membershippb
public import GeneratedProof.go_etcd_io.etcd.api.v3.mvccpb
public import Code.google_golang_org.grpc.metadata
public import Code.google_golang_org.grpc
public import GeneratedProof.google_golang_org.grpc.chunk1
public import GeneratedProof.google_golang_org.grpc.chunk3
public import Code.go_etcd_io.etcd.api.v3.etcdserverpb
public import Perennial.GeneratedProof.fmt
public import Code.go_etcd_io.etcd.client.pkg.v3.verify
public import Perennial.GeneratedProof.errors
public import Code.google_golang_org.grpc.codes
public import Code.google_golang_org.grpc.internal.status
public import Code.google_golang_org.grpc.status
public import Code.go_etcd_io.etcd.api.v3.v3rpc.rpctypes
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.adt
public import GeneratedProof.go_uber_org.zap
public import Code.golang_org.x.crypto.bcrypt
public import Perennial.GeneratedProof.sort
public import Perennial.GeneratedProof.strconv
public import Perennial.GeneratedProof.strings
public import Perennial.GeneratedProof.sync
public import Perennial.GeneratedProof.sync.atomic
public import Perennial.GeneratedProof.time
public import Code.go_etcd_io.etcd.server.v3.auth
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.backend
public import GeneratedProof.google_golang_org.protobuf.internal.pragma
public import Code.google_golang_org.protobuf.proto
public import Code.go_etcd_io.etcd.server.v3.storage.schema

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The abstract state (pure) -/

/-- **The store's abstract state**: the changes of every committed revision (the first two,
revisions `0` and `1`, `NewStore`'s, empty), the compaction revision (`-1`: never compacted), and
the revision being committed (notified to the watchers, not yet visible to reads). -/
structure MvccState where
  log : Log
  crev : Int
  pending : Option (List Change)

/-- The current (committed) revision. -/
def MvccState.rev (σ : MvccState) : Nat := σ.log.length - 1

/-- The history the watchers were sent: the log with the pending revision. -/
def MvccState.notifiedLog (σ : MvccState) : Log :=
  match σ.pending with
  | none => σ.log
  | some p => σ.log ++ [p]

/-- **A commit's first step**: the changes `pend` sent to the watchers (none: nothing pending). -/
def MvccState.notify (σ : MvccState) (pend : List Change) : MvccState :=
  { σ with pending := if pend = [] then none else some pend }

/-- **A commit's second step**: the pending revision committed (visible to reads). -/
def MvccState.commitPending (σ : MvccState) : MvccState :=
  { σ with log := commitLog σ.log (σ.pending.getD []), pending := none }

/-- A compaction at `r`. -/
def MvccState.compactTo (σ : MvccState) (r : Int) : MvccState := { σ with crev := r }

/-- A new store's state: revisions `0` and `1`, both empty, never compacted, nothing pending. -/
def mvccStart : MvccState := ⟨[[], []], -1, none⟩

/-- **The states a store goes through**: from `mvccStart`, a commit's two steps (of well-formed
changes, each delete of a key present: `LogWf`), compactions to a revision above the last and at
most the current one. -/
inductive MvccReachable : MvccState → Prop
  | start : MvccReachable mvccStart
  | notify (σ : MvccState) (pend : List Change) :
      MvccReachable σ → σ.pending = none → LogWf (σ.log ++ [pend]) → MvccReachable (σ.notify pend)
  | commit (σ : MvccState) : MvccReachable σ → MvccReachable σ.commitPending
  | compact (σ : MvccState) (r : Int) :
      MvccReachable σ → σ.pending = none → 1 ≤ r → σ.crev < r → r ≤ (σ.rev : Int) →
      MvccReachable (σ.compactTo r)

/-- **A transaction's view**: a read transaction at the state `σ`, or a write transaction begun at
`σ` with the pending changes `pend`. -/
inductive MTxn where
  | read (σ : MvccState)
  | write (σ : MvccState) (pend : List Change)

/-- **A watch response**, as the client sees it: its watcher's id (`-1`: the whole stream's
progress), its events, its revision and its compaction revision (`0`: none). -/
structure WResp where
  id : w64
  evs : List EvM
  rev : w64
  compactRev : w64

/-- The events the responses `rs` carried for the watcher `id`, in order. -/
def recvEvs (rs : List WResp) (id : w64) : List EvM :=
  ((rs.filter fun r => decide (r.id = id)).map WResp.evs).flatten

/-- **A watcher, in the stream's state**: its range, its filters' predicates (an event a predicate
holds of is not sent), its first revision, the number of responses the stream had sent when it
registered, and whether it is live (not cancelled). -/
structure WInfo where
  rg : WatchRange
  fs : List (EvM → Bool)
  lo : Nat
  k : Nat
  live : Bool

/-- **The watch stream's state**: its watchers by id, and whether it is closed. -/
structure StreamState where
  ws : GMap w64 WInfo
  closed : Bool

def StreamState.register (S : StreamState) (id : w64) (w : WInfo) : StreamState :=
  { S with ws := S.ws.insert id w }
def StreamState.close (S : StreamState) : StreamState := { S with closed := true }
def wsStart : StreamState := ⟨∅, false⟩
/-- A cancel of `id`: the watcher, if any, not live. -/
def StreamState.cancel (S : StreamState) (id : w64) : StreamState :=
  match S.ws !! id with
  | some w => { S with ws := S.ws.insert id { w with live := false } }
  | none => S

/-- **The revisions `[lo, c]` of `L` change each key at most once** (vacuous when `c < lo`). -/
def onceUpTo (L : Log) (lo : Nat) (c : Int) : Prop :=
  ∀ r : Nat, lo ≤ r → (r : Int) ≤ c → ((L.getD r []).map Change.key).Nodup

/-- The namespace an implementation reserves (a stated departure from "no internal namespaces in
masks": a library with invariants must reserve one). -/
def mvccN : Namespace := nroot .@ "mvcc"

/-! ## Lemmas of the vocabulary (stage 1; the clients' rewrites) -/

end api
end mvcc
end EtcdGrove
end Perennial
