/-
The client's watch stream (`watcher.go`): the contract of the `watchable` interface it calls (the
watchable store, unit 3) and the stream's lock invariant. Lean-first; `notes/decisions.md`,
"The watcher group and the stream (unit 2)".

**The contract is the store's choice** (`WatchParams`): `IW w` says `w` is a watcher of the
store (persistent: `RequestProgress` uses a watcher after releasing the stream's lock, while
`Cancel` may run), `WC w` that `w` is cancelled (persistent), `C ch` what the store needs of
the stream's channel and `F f` of a filter (persistent), and `CR ch L` (owned) the right to
close `ch`, the store's record of the watchers `L` registered on it: `watch` adds the new
watcher to it, and the stream closes `ch` with it once every watcher of `L` is cancelled
(`Close` cancels all, then closes, under its lock: the store must not send on a closed channel).

**The stream** (`isWatchStream ws wa P γ`, persistent): its `watchable` and `ch` fields
(written once by `NewWatchStream`), and the `sync.Mutex` `ws.mu` guarding `watchStreamInv`:
`nextID`, `closed` and the maps `cancels` and `watchers`, with the same domain, each watcher
registered and each cancel closure's spec (it cancels its id's watcher, any number of times:
`cancelWatcher` is idempotent); while open, the close right with every watcher it lists either
in `watchers` or cancelled (`Cancel` deletes a watcher only after cancelling it); once closed,
the token `watchStreamOpen γ`, which `Close` consumes (a second `Close` would close `ch` twice,
a panic: `NewWatchStream` hands out one token). The specs are history-free: the invariant is
the only state, since two `Cancel(id)` may both proceed.

**What a registration says** (unit W-M, for the watch client): `watch` returns, besides `IW`,
`IWF w r fcs lo` (persistent, the store's choice): `w`'s fixed range `r` (key, end, start
revision, id), filters and first revision `lo`; and a bound on the watchers registered on the
channel (`(w :: L).length + 3 ≤ 2 ^ 63`: the store's watcher budget), which keeps the stream's
`nextID` from overflowing. **Auto-assigned ids** (`id = 0`, `AutoWatchID`): the stream's ghost
map `γ.ids` (`WsStreamNames`) records every id it assigned with its watcher (`idAssigned γ id w`,
persistent), so an id assigned on a stream names one watcher for good (`idAssigned_agree`); the
invariant keeps every assigned id in `[0, nextID)` and `nextID` plus the live ids at or above it
at most the watchers registered (`aboveCnt`), so `nextID` never wraps. Explicitly chosen ids are
not recorded: they can be reused after a cancel (`issues/etcd-watch-id-reuse-stale-events.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchGroup
public import Perennial.Ghost.Token
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.SavedProp
public import Perennial.Golang.Theory.Chan
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamLog
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The ids a stream assigns (pure) -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The ghost names of a stream's channel: the channel's, the consumer's received responses
(`ghostVar (List RespM)`), the registered watchers (`ghostVar (List Loc)`, half the close
right's) and their set (a ghost map with persistent elements: `chanReg`); and (unit W-M2) the
ids the stream assigned to the watchers registered on it (`ids`, a ghost map from an id to its
watcher, persistent elements: `chanIdAssigned`; the stream's `idsInv` holds its authority) and
the channel's progress fact (`prog`, a saved proposition fixed at the stream's creation: what a
response of id `-1` says, `progFact`). Moved from `InvWatchStore.lean` (unit W-M2): the stream's
contract names it. And (unit W-K) the responses sent on the channel, a monotone list
(`sentl`, its authority the channel invariant's), so that a response sent has a position in the
channel's order and a snapshot of the list is a point in it (`chanSentLb`); and (K1b) the
registration index of each watcher registered on it (`regi`, a ghost map from a watcher to the
sent list's length at its registration, persistent elements: `chanRegAt`). -/
structure WatchChanNames where
  ch : ChanNames
  recv : GName
  regl : GName
  reg : GName
  ids : GName
  prog : GName
  sentl : GName
  regi : GName
  /-- the reason a watcher of the channel's stream was cancelled (unit W-K, K1b): a saved
  predicate on its id, the stream's creator's (`rsnFor`) -/
  rsn : GName
  /-- (stage 2 of the mvcc API, the watch chain, 2026-11-05) the stream's API names
  (`api.WsAbs`, `wsAbsOf`): its history (a monotone list of `api.sent.SEv`, the authority the
  channel invariant's, `chanApi`), the count of its client's events, the consumer's view and its
  count -/
  aev : GName
  ans : GName
  arcv : GName
  arx : GName
  /-- (2026-11-05, the registration) the history at the stream's client's last event, half the
  client's (`api.wsStateI`), half the stream's mutex invariant's (`watchStreamInv`) -/
  acl : GName

/-- **The progress fact of the saved proposition `g`** (persistent; unit W-M2): some `Q` saved at
`g`, and `Q`. A stream's creator fixes `Q` (`NewWatchStream`); a response of id `-1` on the
channel (`progressAll`'s) carries it. -/
def progFact (g : GName) : IProp GF :=
  iprop(∃ Q : IProp GF, savedPropOwn g DFrac.discard Q ∗ □ Q)

/-- **The channel's stream assigned `id` to the watcher `w`** (persistent; unit W-M2): an element
of the channel's id map. The stream's `idAssigned` is the same element (`γ.ids = γc.ids`,
`isWatchStream`). -/
def chanIdAssigned (γc : WatchChanNames) (id : w64) (w : Loc) : IProp GF :=
  ghostMapElem γc.ids id DFrac.discard w

/-- **The watcher of id `id` was cancelled, in the stream's history** (persistent; 2026-11-05, in
place of the saved reason `rsnFor`): a lower bound of the history (`γc.aev`) ending in the cancel
of `id`, after its registration; `api.cancelTok` at the stream's names. A progress response of id
`-1` covers every watcher registered on the channel before it, or that watcher has this token. -/
def chanCancelTok (γc : WatchChanNames) (id : w64) : IProp GF :=
  iprop(∃ (l : List api.sent.SEv) (rg : WatchRange) (fg : GName) (lo : Nat),
    monoListLbOwn γc.aev (l ++ [.cancel id]) ∗ ⌜api.sent.SEv.reg id rg fg lo ∈ l⌝)

/-- **The watcher of id `id` was registered in the stream's history with this info** (persistent;
2026-11-05, the sends' premises): a lower bound of the history (`γc.aev`) holding its
registration; `api.regTok` at the stream's names. Every watcher registered on the channel has it
(`chanRegW`, minted at the registration), so a sender knows its registry info is the stream's
(`factAgree`). -/
def chanRegTok (γc : WatchChanNames) (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat) :
    IProp GF :=
  iprop(∃ l : List api.sent.SEv, monoListLbOwn γc.aev l ∗ ⌜api.sent.SEv.reg id rg fg lo ∈ l⌝)

/- The structure's reserved congruence lemma, realized once here: `simp` in the stream's proof files
(`watchStream__Cancel`, `Close`, ...) would otherwise realize it in each, which the layout check
reports as exposed by a proof file. (A statement mentioning it realizes it in the public part;
`#check` does not keep it.) -/

end defs

end mvcc
end EtcdGrove
end Perennial
