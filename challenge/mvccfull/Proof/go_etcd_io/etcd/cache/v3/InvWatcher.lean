/-
etcd's cache `watcher` (`cache/watcher.go`): the shared vocabulary of `Spec/newWatcher.lean`
and `Spec/watcher__*.lean`, and the two operations of the watcher's consumer that are not Go
functions (`wp_watcher_receive`, `wp_watcher_cancelResp`). Lean-first (no Rocq counterpart).

A watcher is a buffered channel `respCh` of `WatchResponse`s with one producer (the demux,
which calls `enqueueResponse` under its lock, and `Stop`/`Compact`) and one consumer (the
goroutine of `Cache.Watch`, which does `resp, ok := <-w.respCh` and, on `!ok`, reads
`w.cancelResp`); a key filter `keyPred`; and a `sync.Once` guarding the `close`.

**The four predicates** (ghost names `γ`, `WatcherNames`):
- `isWatcher w γ pred` (persistent): the channel, the `keyPred` closure (nil iff
  `pred = none`, else its triple `keyPredSpec`), the `Once`, and the invariant `watcherInv`.
- `watcherOpen γ sent` (exclusive, the producer's): the channel is open and `sent` is the
  log of every response sent so far.
- `watcherClosed γ sent c` (persistent): the channel was closed after `sent`, with
  `cancelResp` nil (`c = none`, `Stop`) or the compaction response of revision `rev`
  (`c = some rev`, `Compact`).
- `watcherConsumer γ received` (exclusive, the consumer's): the consumer has received
  `received`, a prefix of `sent`.
The producer's and the consumer's views are separate (two halves of two ghost variables, the
other halves in the invariant) because they run concurrently: the producer cannot know how
much has been received, the consumer how much has been sent. The invariant ties them to the
channel: `recv <+: sent`, and the values in flight (in the buffer, or the one an unbuffered
send has committed) are the responses `sent.drop recv.length`, each `respSent` (`respAt` of
its model, with a non-nil `Header`).

**Closing.** `Stop` and `Compact` close the channel through `stopOnce.Do`. The `Once`'s
one-shot resource is `cancelResp ↦ nil`, its persistent result "closed after some log"; the
caller lends its `watcherOpen` to the closure (`Once.wp_Do_frame`, `OnceFrame.lean`), which
closes the channel, records `watcherClosed γ sent c` and leaves `cancelResp` read-only for
good. A caller that already holds `watcherClosed` gets it back unchanged.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvBtree
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoNat
public import Perennial.Golang.Defn.String
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI
public import Perennial.Proof.sync
public import Perennial.Golang.Theory.Chan
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.Token
public import Perennial.Std.ListBasics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## Pure models -/

/-- The values a channel in state `s` holds in flight: its buffer (also when closed), or the
value an unbuffered send has committed to; `none` for the states of a blocking send, which
the watcher's producer never does. -/
def chanInflight {V : Type} : ChanState V → Option (List V)
  | .Buffered b => some b
  | .Closed b => some b
  | .Idle => some []
  | .RcvPending => some []
  | .SndCommit v => some [v]
  | .SndPending _ => none
  | .RcvCommit => none

/-- The channel state `s` is closed. -/
def chanIsClosed {V : Type} : ChanState V → Bool
  | .Closed _ => true
  | _ => false

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

end defs

/-! ## Lemmas -/

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-! ## Freshness of a new watcher -/

end lemmas

end EtcdGrove
end Perennial
