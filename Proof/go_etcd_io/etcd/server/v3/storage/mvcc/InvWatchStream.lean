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

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The ids a stream assigns (pure) -/

/-- The number of ids at or above `n` (as signed integers) in the map `WM`. -/
noncomputable def aboveCnt (n : w64) (WM : GMap w64 Loc) : Nat :=
  GMap.size (GMap.filter (fun i _ => decide (sint.Z n ≤ sint.Z i)) WM)

theorem aboveCnt_delete (n id : w64) (WM : GMap w64 Loc) :
    aboveCnt n (GMap.delete id WM) ≤ aboveCnt n WM := by
  unfold aboveCnt
  apply GMap.map_subseteq_size
  intro k v h
  have h' : (GMap.filter (fun i _ => decide (sint.Z n ≤ sint.Z i)) (GMap.delete id WM)) !! k =
      some v := h
  show (GMap.filter (fun i _ => decide (sint.Z n ≤ sint.Z i)) WM) !! k = some v
  rw [GMap.mapLookup_filter_Some] at h' ⊢
  refine ⟨?_, h'.2⟩
  have := h'.1
  rw [GMap.lookup_delete_iff] at this
  split at this
  · cases this
  · exact this

theorem aboveCnt_insert (n id : w64) (w : Loc) (WM : GMap w64 Loc) :
    aboveCnt n (<[id := w]> WM) ≤ aboveCnt n WM + 1 := by
  unfold aboveCnt
  have h1 : GMap.filter (fun i _ => decide (sint.Z n ≤ sint.Z i)) (<[id := w]> WM) ⊆
      <[id := w]> (GMap.filter (fun i _ => decide (sint.Z n ≤ sint.Z i)) WM) := by
    intro k v h
    have h' : (GMap.filter (fun i _ => decide (sint.Z n ≤ sint.Z i)) (<[id := w]> WM)) !! k =
        some v := h
    show (<[id := w]> (GMap.filter (fun i _ => decide (sint.Z n ≤ sint.Z i)) WM)) !! k = some v
    rw [GMap.mapLookup_filter_Some] at h'
    obtain ⟨h1, h2⟩ := h'
    rw [GMap.lookup_insert_eq_iff] at h1 ⊢
    by_cases hik : id = k
    · simp only [hik, ↓reduceIte] at h1 ⊢; exact h1
    · simp only [hik, ↓reduceIte] at h1 ⊢
      rw [GMap.mapLookup_filter_Some]; exact ⟨h1, h2⟩
  have := GMap.map_subseteq_size h1
  rw [GMap.map_size_insert] at this
  split at this <;> omega

/-- Skipping a live id `n`: one fewer live id at or above the next. -/
theorem aboveCnt_skip (n : w64) (w : Loc) (WM : GMap w64 Loc) (hn : WM !! n = some w)
    (hb : sint.Z n < 2 ^ 63 - 1) :
    aboveCnt n WM = aboveCnt (n + W64 1) WM + 1 := by
  unfold aboveCnt
  have hs : sint.Z (n + W64 1) = sint.Z n + 1 := by word
  have he : GMap.filter (fun i _ => decide (sint.Z n ≤ sint.Z i)) WM =
      <[n := w]> (GMap.filter (fun i _ => decide (sint.Z (n + W64 1) ≤ sint.Z i)) WM) := by
    apply GMap.ext
    intro k
    rw [GMap.lookup_insert_eq_iff, GMap.lookup_filter]
    split
    · rename_i h; subst h; simp [hn]
    · rw [GMap.lookup_filter]
      rename_i hk
      have hk' : sint.Z k ≠ sint.Z n := fun h => hk (by
        have := congrArg (fun z : Int => (BitVec.ofInt 64 z)) h
        simpa using this.symm)
      have hiff : (sint.Z n ≤ sint.Z k) ↔ (sint.Z (n + W64 1) ≤ sint.Z k) := by rw [hs]; omega
      cases WM !! k <;> simp [Option.filter, hiff]
  rw [he, GMap.map_size_insert_None _ _ _ (by
    have hlt : ¬ (sint.Z (n + W64 1) ≤ sint.Z n) := by omega
    rw [GMap.lookup_filter, hn]; simp only [Option.filter, decide_eq_false hlt]; rfl)]

/-- Assigning the free id `n` and moving past it: no more live ids at or above the next. -/
theorem aboveCnt_assign (n : w64) (w : Loc) (WM : GMap w64 Loc)
    (hb : sint.Z n < 2 ^ 63 - 1) :
    aboveCnt (n + W64 1) (<[n := w]> WM) ≤ aboveCnt n WM := by
  unfold aboveCnt
  have hs : sint.Z (n + W64 1) = sint.Z n + 1 := by word
  apply GMap.map_subseteq_size
  intro k v h
  have h' : (GMap.filter (fun i _ => decide (sint.Z (n + W64 1) ≤ sint.Z i)) (<[n := w]> WM)) !! k =
      some v := h
  show (GMap.filter (fun i _ => decide (sint.Z n ≤ sint.Z i)) WM) !! k = some v
  rw [GMap.mapLookup_filter_Some] at h' ⊢
  obtain ⟨h1, h2⟩ := h'
  rw [GMap.lookup_insert_eq_iff] at h1
  split at h1
  · exfalso; simp only [decide_eq_true_eq] at h2; rename_i h; subst h; rw [hs] at h2; omega
  · simp only [decide_eq_true_eq] at h2 ⊢
    exact ⟨h1, by omega⟩

/-- The range `watch` registers for `key`/`end` (`end` nil: the single key `k`; otherwise
`[k, e)`, `e` empty for "from `k` on"), the start revision and the id. -/
def watchRangeOf (k e : List w8) (endk : GoSlice) (startRev id : w64) : WatchRange :=
  { key := k, end? := if endk = slice.nil then none else some e, startRev := startRev, id := id }

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
  /-- What a registration costs (consumed by `watch`: the store's watcher budget, a token). -/
  T : IProp GF
  /-- `w` is a watcher with the fixed range `r` (its key, end, start revision and id), the
  filters `fcs` and the first revision `lo` (persistent): what `watch` says of the watcher it
  made. -/
  IWF : Loc → WatchRange → GoSlice → Nat → IProp GF
  IW_pers : ∀ w, Persistent (IW w)
  WC_pers : ∀ w, Persistent (WC w)
  C_pers : ∀ ch, Persistent (C ch)
  F_pers : ∀ f, Persistent (F f)
  IWF_pers : ∀ w r fcs lo, Persistent (IWF w r fcs lo)


instance WatchParams.IW_persistent (P : WatchParams GF) (w : Loc) : Persistent (P.IW w) :=
  P.IW_pers w
instance WatchParams.WC_persistent (P : WatchParams GF) (w : Loc) : Persistent (P.WC w) :=
  P.WC_pers w
instance WatchParams.C_persistent (P : WatchParams GF) (ch : GoChan) : Persistent (P.C ch) :=
  P.C_pers ch
instance WatchParams.F_persistent (P : WatchParams GF) (f : GoFunc) : Persistent (P.F f) :=
  P.F_pers f
instance WatchParams.IWF_persistent (P : WatchParams GF) (w : Loc) (r : WatchRange)
    (fcs : GoSlice) (lo : Nat) : Persistent (P.IWF w r fcs lo) :=
  P.IWF_pers w r fcs lo

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
right's watchers (a start revision at least `0`: `0` is "now", the documented domain), at the
cost of the caller's `P.T` (consumed), with what it says of the watcher (`P.IWF`, the range
`watchRangeOf`) and the bound on the watchers registered on `ch`;
`progress(w)` takes a watcher's persistent fact only; `progressAll(m)` reads the map of the
stream's watchers; `rev()` returns a revision. Every call is lent the caller's `P.R` (the store's
reader slots: `rev` opens a read transaction, the others take the store's locks). -/
def isWatchable (wa : GoInterface) (P : WatchParams GF) : IProp GF :=
  iprop(∃ wi : GoInterfaceOk, ⌜wa = GoInterface.ok wi⌝ ∗
    □ (∀ (key endk fcs : GoSlice) (k e : List w8) (fs : List GoFunc) (startRev id : w64)
        (ch : GoChan) (L : List Loc),
      {{ key ↦*□ k ∗ endk ↦*□ e ∗ fcs ↦*□ fs ∗ ([∗list] f ∈ fs, P.F f) ∗ P.C ch ∗ P.CR ch L ∗
          P.R ∗ P.T ∗ ⌜0 ≤ sint.Z startRev⌝ }}
        (App (App (App (App (App (App (Val #(methods wi.ty go!"watch" wi.v)) (Val #key))
          (Val #endk)) (Val #startRev)) (Val #id)) (Val #ch)) (Val #fcs))
      {{ (w : Loc) (c : GoFunc), RET (PairV #w #c);
          ⌜w ≠ null⌝ ∗ P.IW w ∗ cancelSpec P c w ∗ P.CR ch (w :: L) ∗ P.R ∗
          (∃ lo : Nat, P.IWF w (watchRangeOf k e endk startRev id) fcs lo) ∗
          ⌜(w :: L).length + 3 ≤ 2 ^ 63⌝ }}) ∗
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

/-- A stream's ghost names: its open token (`tok`), the ids it assigned (`ids`, a ghost map
from an auto-assigned id to its watcher, persistent elements) and the same map with exclusive
elements (`fresh`, the watch slice's unit W-C: one token per assigned id, `idTok`). -/
structure WsStreamNames where
  tok : GName
  ids : GName
  fresh : GName

/-- The token of an open stream: `NewWatchStream` returns it, `Close` consumes it. -/
def watchStreamOpen (γ : WsStreamNames) : IProp GF := token γ.tok

/-- **The stream assigned the id `id` to the watcher `w`** (persistent): `Watch` with
`AutoWatchID` chose `id` for `w`. -/
def idAssigned (γ : WsStreamNames) (id : w64) (w : Loc) : IProp GF :=
  ghostMapElem γ.ids id DFrac.discard w

instance idAssigned_persistent (γ : WsStreamNames) (id : w64) (w : Loc) :
    Persistent (idAssigned (GF := GF) γ id w) := by
  unfold idAssigned; infer_instance

/-- **An id a stream assigned names one watcher**: two watchers assigned the same id on the same
stream are the same. -/
theorem idAssigned_agree (γ : WsStreamNames) (id : w64) (w w' : Loc) :
    idAssigned (GF := GF) γ id w ∗ idAssigned γ id w' ⊢ ⌜w = w'⌝ := by
  unfold idAssigned
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- **The stream assigned the id `id`, once** (exclusive; the watch slice's unit W-C): the token
`Watch` returns with an id it chose (`AutoWatchID`), at most one per id (`idTok_excl`): a
client holding the tokens of the ids it was given knows a new id is not one of them. -/
def idTok (γ : WsStreamNames) (id : w64) : IProp GF :=
  iprop(∃ w : Loc, ghostMapElem γ.fresh id (DFrac.own 1) w)

/-- Two tokens of one id are impossible. -/
theorem idTok_excl (γ : WsStreamNames) (id : w64) :
    idTok (GF := GF) γ id ∗ idTok γ id ⊢ False := by
  unfold idTok
  iintro ⟨⟨%w1, H1⟩, ⟨%w2, H2⟩⟩
  ihave %H := ghostMapElem_valid_2 id γ.fresh (DFrac.own 1) (DFrac.own 1) w1 w2 $$ H1 H2
  exfalso
  exact absurd (DFrac.valid_op_own H.1) (by simp)

/-- The ids assigned so far (`IDS`), each in `[0, nextID)`, `nextID` at least `0`; the map of
the ids' tokens (`fresh`) is the same. -/
def idsInv (γ : WsStreamNames) (nextID : w64) : IProp GF :=
  iprop(∃ IDS : GMap w64 Loc, ghostMapAuth γ.ids 1 IDS ∗ ghostMapAuth γ.fresh 1 IDS ∗
    ⌜0 ≤ sint.Z nextID ∧ ∀ i, (IDS !! i).isSome → 0 ≤ sint.Z i ∧ sint.Z i < sint.Z nextID⌝)

/-- The assigned ids after a registration: an explicit id (`idp ≠ 0`) leaves them as they are;
an assigned one, `id`, free and below the next `nextID`, is recorded with its watcher `w`. -/
theorem idsInv_next (γ : WsStreamNames) (IDS : GMap w64 Loc) (NX idp aid : w64)
    (w : Loc)
    (h : (idp ≠ W64 0 ∧ 0 ≤ sint.Z NX ∧
          ∀ i, (IDS !! i).isSome → 0 ≤ sint.Z i ∧ sint.Z i < sint.Z NX) ∨
         (0 ≤ sint.Z aid ∧ sint.Z aid < sint.Z NX ∧
          ∀ i, (IDS !! i).isSome → 0 ≤ sint.Z i ∧ sint.Z i < sint.Z aid)) :
    ghostMapAuth (GF := GF) γ.ids 1 IDS ∗ ghostMapAuth γ.fresh 1 IDS ⊢
      |==> (idsInv γ NX ∗ (⌜idp ≠ W64 0⌝ ∨ (idAssigned γ aid w ∗ idTok γ aid))) := by
  iintro ⟨Ha, Hf⟩
  rcases h with ⟨hp, h0, hb⟩ | ⟨h0, h1, hb⟩
  · imodintro
    isplitl [Ha Hf]
    · iunfold idsInv
      iexists IDS
      iframe Ha Hf
      ipureintro; exact ⟨h0, hb⟩
    ileft; ipureintro; exact hp
  · have hfresh : IDS.lookup aid = none := by
      cases hc : IDS.lookup aid with
      | none => rfl
      | some _ =>
        have := (hb aid (by show (IDS.lookup aid).isSome; rw [hc]; rfl)).2; omega
    imod ghost_map_insert_persist aid w hfresh $$ Ha with ⟨Ha, #Hel⟩
    imod ghost_map_insert aid w hfresh $$ Hf with ⟨Hf, Hfe⟩
    imodintro
    isplitl [Ha Hf]
    · iunfold idsInv
      iexists _
      iframe Ha Hf
      ipureintro
      refine ⟨by omega, fun i hi => ?_⟩
      by_cases hin : aid = i
      · subst hin; omega
      · have hi' : (IDS !! i).isSome := by
          have := hi
          rw [show (IDS.insert aid w) !! i = (<[aid := w]> IDS) !! i from rfl,
            GMap.lookup_insert_eq_iff] at this
          simpa [hin] using this
        have := hb i hi'; omega
    iright
    iunfold idAssigned
    iframe Hel
    iunfold idTok
    iexists w
    iexact Hfe

/-- The state `ws.mu` guards (see the module doc). -/
def watchStreamInv (ws : Loc) (P : WatchParams GF) (ch : GoChan) (γ : WsStreamNames) : IProp GF :=
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
    "Hids" ∷ idsInv γ nextID ∗
    "Hcl" ∷ (if closed then watchStreamOpen γ else
      ∃ L : List Loc, P.CR ch L ∗
        □ (∀ w : Loc, ⌜w ∈ L⌝ -∗ ((∃ id : w64, ⌜WM !! id = some w⌝) ∨ P.WC w)) ∗
        ⌜sint.Z nextID + aboveCnt nextID WM ≤ L.length ∧ L.length + 3 ≤ 2 ^ 63⌝))

/-- **The stream** `ws` over the watchable `wa` (persistent; see the module doc). -/
def isWatchStream (ws : Loc) (wa : GoInterface) (P : WatchParams GF) (γ : WsStreamNames) :
    IProp GF :=
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
    (γ : WsStreamNames) : Persistent (isWatchStream ws wa P γ) := by
  unfold isWatchStream; simp only [named]; infer_instance

end defs

end mvcc
end EtcdGrove
end Perennial
