/-
**A watcher before the server's facts** (D19f, 2026-10-18, branch `raft-retarget`):
`isClientWatcherCore V w`, what `NewWatchFromWatchClient`/`NewWatcher` establish without the watch
server's facts. Constructing a watcher only allocates it (its streams map and its lock; no
goroutine, no call on the connection: `watch.go`'s `NewWatchFromWatchClient`), and the lock's
invariant (`watcherMu`, an empty map at construction) needs no fact about the server, so the facts
are needed only by `Watch`. `isClientWatcher V w` is the core with the facts of the connection
(`isClientWatcher_of_core`), supplied when the client first watches. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3
open go_etcd_io.etcd.cache.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The watcher `w` without the server's facts** (persistent): `isClientWatcher V w` with the
stub on the connection (`watchStubAt`) in place of `watchSrvFacts V`. The environment `V` is
fixed at construction (the lock's invariant is stated over it) but nothing is assumed of it. -/
def isClientWatcherCore (V : WEnv GF) (w : Loc) : IProp GF :=
  iprop(∃ (callSl : GoSlice) (vs : List GoInterface),
    ⌜w ≠ null⌝ ∗
    watcherF w go!"remote" ↦□ wcIface V.wc ∗ watcherF w go!"callOpts" ↦□ callSl ∗
    callSl ↦*□ vs ∗ callOptsOk vs ∗ watcherF w go!"lg" ↦□ V.lg ∗
    sync.isMutex (watcherF w go!"mu") (watcherMu V w callSl) ∗
    v3rpc.watchStubAt V.wc V.conn ∗ ⌜V.lg ≠ null ∧ threadBound GF ≤ 2 ^ 31⌝)

instance isClientWatcherCore_persistent (V : WEnv GF) (w : Loc) :
    Persistent (isClientWatcherCore V w) := by
  unfold isClientWatcherCore; infer_instance

/-- **The watcher `w`'s stub is over the connection `conn`** (persistent; G2's F-W3, 2026-10-30):
its `remote` field holds a watch client whose connection is `conn` (`v3rpc.watchStubAt`), as
`isClientWatcherCore` says of its environment's: what ties a client's `Watcher` to the connection
its other fields use (`clientTokAt`). -/
def watcherConnAt (w conn : Loc) : IProp GF :=
  iprop(∃ wc : Loc, watcherF w go!"remote" ↦□ wcIface wc ∗ v3rpc.watchStubAt wc conn)

instance watcherConnAt_persistent (w conn : Loc) : Persistent (watcherConnAt (GF := GF) w conn) := by
  unfold watcherConnAt; infer_instance

theorem watcherConnAt_of_core (V : WEnv GF) (w : Loc) :
    isClientWatcherCore V w ⊢ watcherConnAt w V.conn := by
  unfold isClientWatcherCore watcherConnAt
  iintro ⟨%callSl, %vs, -, #Hr, -, -, -, -, -, #Hs, -⟩
  iexists V.wc
  iframe Hr Hs

theorem watcherConnAt_of_watcher (V : WEnv GF) (w : Loc) :
    isClientWatcher V w ⊢ watcherConnAt w V.conn := by
  unfold isClientWatcher watchSrvFacts watcherConnAt
  iintro ⟨%callSl, %vs, -, #Hr, -, -, -, -, -, ⟨#Hs, -⟩, -⟩
  iexists V.wc
  iframe Hr Hs

/-- **The watcher with the facts of its connection's server** is `isClientWatcher`. -/
theorem isClientWatcher_of_core (V : WEnv GF) (w : Loc) :
    isClientWatcherCore V w ∗ watchConnFacts V ⊢ isClientWatcher V w := by
  unfold isClientWatcherCore isClientWatcher watchSrvFacts
  iintro ⟨⟨%callSl, %vs, %Hw, #H1, #H2, #H3, #H4, #H5, #H6, #Hst, %Hp⟩, #Hf⟩
  iexists callSl, vs
  iframe #
  isplitr
  · ipureintro; exact Hw
  ipureintro; exact Hp

end defs

end client
end EtcdGrove
end Perennial
