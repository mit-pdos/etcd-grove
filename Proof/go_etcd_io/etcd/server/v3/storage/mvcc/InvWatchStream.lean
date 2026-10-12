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
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- What the watchable store chooses for the stream's contract (see the module doc). -/
structure WatchParams (GF : BundledGFunctors) where
  /-- `w` is a watcher of the store (persistent). -/
  IW : Loc → IProp GF
  /-- The watcher `w` is cancelled (persistent). -/
  WC : Loc → IProp GF
  /-- What the store needs of the stream's channel (persistent). -/
  C : GoChan → IProp GF
  /-- What the store needs of a filter function (persistent). -/
  F : GoFunc → IProp GF
  /-- The right to close the channel, with the watchers registered on it. -/
  CR : GoChan → List Loc → IProp GF
  /-- What the caller owns to call the store (lent to each call: the store's reader slots). -/
  R : IProp GF
  IW_pers : ∀ w, Persistent (IW w)
  WC_pers : ∀ w, Persistent (WC w)
  C_pers : ∀ ch, Persistent (C ch)
  F_pers : ∀ f, Persistent (F f)


instance WatchParams.IW_persistent (P : WatchParams GF) (w : Loc) : Persistent (P.IW w) :=
  P.IW_pers w
instance WatchParams.WC_persistent (P : WatchParams GF) (w : Loc) : Persistent (P.WC w) :=
  P.WC_pers w
instance WatchParams.C_persistent (P : WatchParams GF) (ch : GoChan) : Persistent (P.C ch) :=
  P.C_pers ch
instance WatchParams.F_persistent (P : WatchParams GF) (f : GoFunc) : Persistent (P.F f) :=
  P.F_pers f

/-- `c` cancels the watcher `w` (persistent: callable any number of times). -/
def cancelSpec (P : WatchParams GF) (c : GoFunc) (w : Loc) : IProp GF :=
  iprop(□ {{ True }} (App (Val #c) (Val #())) {{ RET #(); P.WC w }})

instance cancelSpec_persistent (P : WatchParams GF) (c : GoFunc) (w : Loc) :
    Persistent (cancelSpec P c w) := by
  unfold cancelSpec; infer_instance

/-- **The `watchable` the stream uses** (persistent), the interface value `wa`:
`watch(key, end, startRev, id, ch, fcs)` registers a watcher on `ch` (the stream's channel,
converted to send-only) with the range `key`/`end` and the filters `fcs`, all read-only for
good (the watcher keeps them), and returns it with its cancel closure, adding it to the close
right's watchers (a start revision at least `0`: `0` is "now", the documented domain);
`progress(w)` takes a watcher's persistent fact only; `progressAll(m)` reads the map of the
stream's watchers; `rev()` returns a revision. Every call is lent the caller's `P.R` (the store's
reader slots: `rev` opens a read transaction, the others take the store's locks). -/
def isWatchable (wa : GoInterface) (P : WatchParams GF) : IProp GF :=
  iprop(∃ wi : GoInterfaceOk, ⌜wa = GoInterface.ok wi⌝ ∗
    □ (∀ (key endk fcs : GoSlice) (k e : List w8) (fs : List GoFunc) (startRev id : w64)
        (ch : GoChan) (L : List Loc),
      {{ key ↦*□ k ∗ endk ↦*□ e ∗ fcs ↦*□ fs ∗ ([∗list] f ∈ fs, P.F f) ∗ P.C ch ∗ P.CR ch L ∗
          P.R ∗ ⌜0 ≤ sint.Z startRev⌝ }}
        (App (App (App (App (App (App (Val #(methods wi.ty go!"watch" wi.v)) (Val #key))
          (Val #endk)) (Val #startRev)) (Val #id)) (Val #ch)) (Val #fcs))
      {{ (w : Loc) (c : GoFunc), RET (PairV #w #c);
          ⌜w ≠ null⌝ ∗ P.IW w ∗ cancelSpec P c w ∗ P.CR ch (w :: L) ∗ P.R }}) ∗
    □ (∀ w : Loc,
      {{ P.IW w ∗ P.R }} (App (Val #(methods wi.ty go!"progress" wi.v)) (Val #w))
      {{ RET #(); P.R }}) ∗
    □ (∀ (m : Loc) (dq : DFrac) (M : GMap w64 Loc),
      {{ m ↦${dq} M ∗ □ (∀ (id : w64) (w : Loc), ⌜M !! id = some w⌝ -∗ P.IW w) ∗ P.R }}
        (App (Val #(methods wi.ty go!"progressAll" wi.v)) (Val #m))
      {{ (b : Bool), RET #b; m ↦${dq} M ∗ P.R }}) ∗
    □ ({{ P.R }} (App (Val #(methods wi.ty go!"rev" wi.v)) (Val #()))
      {{ (r : w64), RET #r; P.R }}))

instance isWatchable_persistent (wa : GoInterface) (P : WatchParams GF) :
    Persistent (isWatchable wa P) := by
  unfold isWatchable; infer_instance

/-- The token of an open stream: `NewWatchStream` returns it, `Close` consumes it. -/
def watchStreamOpen (γ : GName) : IProp GF := token γ

/-- The state `ws.mu` guards (see the module doc). -/
def watchStreamInv (ws : Loc) (P : WatchParams GF) (ch : GoChan) (γ : GName) : IProp GF :=
  iprop(∃ (nextID : w64) (closed : Bool) (cm wm : Loc) (CM : GMap w64 GoFunc)
      (WM : GMap w64 Loc),
    "HnextID" ∷ ws.[watchStream, go!"nextID"] ↦ nextID ∗
    "Hclosed" ∷ ws.[watchStream, go!"closed"] ↦ closed ∗
    "Hcf" ∷ ws.[watchStream, go!"cancels"] ↦ cm ∗
    "Hwf" ∷ ws.[watchStream, go!"watchers"] ↦ wm ∗
    "Hcm" ∷ cm ↦$ CM ∗
    "Hwm" ∷ wm ↦$ WM ∗
    "%Hdom" ∷ ⌜∀ id, (CM !! id).isSome = (WM !! id).isSome⌝ ∗
    "%Hnn" ∷ ⌜∀ id w, WM !! id = some w → w ≠ null⌝ ∗
    "#Hws" ∷ □ (∀ (id : w64) (w : Loc), ⌜WM !! id = some w⌝ -∗ P.IW w) ∗
    "#Hcs" ∷ □ (∀ (id : w64) (c : GoFunc) (w : Loc), ⌜CM !! id = some c⌝ -∗
      ⌜WM !! id = some w⌝ -∗ cancelSpec P c w) ∗
    "Hcl" ∷ (if closed then watchStreamOpen γ else
      ∃ L : List Loc, P.CR ch L ∗
        □ (∀ w : Loc, ⌜w ∈ L⌝ -∗ ((∃ id : w64, ⌜WM !! id = some w⌝) ∨ P.WC w))))

/-- **The stream** `ws` over the watchable `wa` (persistent; see the module doc). -/
def isWatchStream (ws : Loc) (wa : GoInterface) (P : WatchParams GF) (γ : GName) : IProp GF :=
  iprop(∃ ch : GoChan,
    "#Hwa" ∷ ws.[watchStream, go!"watchable"] ↦□ wa ∗
    "#Hch" ∷ ws.[watchStream, go!"ch"] ↦□ ch ∗
    "#HC" ∷ P.C ch ∗
    "#Hwable" ∷ isWatchable wa P ∗
    "#Hclose" ∷ □ (∀ L : List Loc,
      {{ P.CR ch L ∗ □ (∀ w : Loc, ⌜w ∈ L⌝ -∗ P.WC w) }}
        (App (Val #(functions go.close
          [go.GoType.ChannelType go.ChanDir.sendrecv WatchResponse.ty])) (Val #ch))
      {{ RET #(); True }}) ∗
    "#Hmu" ∷ sync.isMutex (ws.[watchStream, go!"mu"]) (watchStreamInv ws P ch γ))

instance isWatchStream_persistent (ws : Loc) (wa : GoInterface) (P : WatchParams GF)
    (γ : GName) : Persistent (isWatchStream ws wa P γ) := by
  unfold isWatchStream; simp only [named]; infer_instance

end defs

end mvcc
end EtcdGrove
end Perennial
