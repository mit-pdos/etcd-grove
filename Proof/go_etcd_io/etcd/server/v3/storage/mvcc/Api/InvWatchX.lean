/-
**The watchable store's lock invariant and the watch stream's mutex invariant with a slot** (the
API proof's parallel internals, stage 1, 2026-11-03; `notes/mvcc-api-invariants.md` §1; the store's
side is `Api/InvStoreX.lean`). Lean-first (no Rocq counterpart).

* `watchStoreInvX s γ Z q`: `watchStoreInv` ∗ `Z q σ`, at the lock's state `σ` (its notified log
  `σ.Lmu`); the API's instance `wsAbs`: the lock's quarter of the pending revision `γ.pnd`, which is
  the notified log's last revision while one is pending.
* `isWatchableStoreX`: `isWatchableStore` over `isStoreX` and `watchStoreInvX`; the API's
  `isWatchableStoreA`.
* `watchStreamInvX ws P ch γc γ Z`: `watchStreamInv` ∗ `Z nextID closed WM`; the API's instance
  `streamAbs`: the mutex's quarter of the stream's state `ι.sst` and half of the registry `ι.reg`
  and of the cancelled set `ι.dead` (§1, as superseded in stage 1: the countable part, each watcher
  naming its saved filters, `ApiGhost.lean`). The tie of these to the mutex's maps is the first cut
  (the closed flag); the proofs of `Watch` and `Cancel` add what they need.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchFrac
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.InvStoreX
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiGhost

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section reprs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## The watchable store's lock invariant with a slot -/

/-- **The lock invariant of `s.mu`, with a slot** `Z` at the lock's state (`watchStoreInv`). -/
def watchStoreInvX (s : Loc) (γ : WsNames) (Z : Qp → WsState → IProp GF) (q : Qp) : IProp GF :=
  iprop(∃ σ : WsState, watchStoreBody s γ q σ ∗ monoNatAuthOwn γ.rel q σ.Lmu.length ∗
    wsFields s γ q ∗ ⌜σ.settled ∧ σ.srBelow σ.Lmu.length ∧ σ.unsRst⌝ ∗ Z q σ)

/-- **The lock invariant with a slot is fractional** when the slot is (two parts agree on the state
through `γ.wst`). -/
theorem watchStoreInvX_fractional (hsplit : adt.ownIvt_split.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : WsNames) (Z : Qp → WsState → IProp GF) (hZ : ∀ σ, Fractional (fun q => Z q σ)) :
    Fractional (watchStoreInvX (GF := GF) s γ Z) := by
  unfold watchStoreInvX
  refine fractional_exists_agree _ (fun σ => wFractional_sep (watchStoreBody_fractional hsplit s γ σ)
    (wFractional_sep (monoNatAuthOwn_fractional γ.rel σ.Lmu.length)
      (wFractional_sep (wsFields_fractional s γ)
        (wFractional_sep (wFractional_persistent _) (hZ σ))))) ?_
  intro σ1 σ2 q1 q2
  unfold watchStoreBody
  iintro ⟨⟨⟨H1, -⟩, -⟩, ⟨⟨H2, -⟩, -⟩⟩
  ihave %H := ghostVar_valid_2 γ.wst _ _ _ _ $$ H1 H2
  ipureintro; exact H.2

/-- **The watchable store, with slots** (`isWatchableStore`, over `isStoreX` and `watchStoreInvX`). -/
def isWatchableStoreX (s st : Loc) (γ : WsNames) (X : Qp → Log → Int → IProp GF)
    (Y : Log → IProp GF) (F Fr : IProp GF) (fz : GName) (Z : Qp → WsState → IProp GF) : IProp GF :=
  iprop(∃ (vc stc rv : Loc) (γv : ChanNames),
    "#Hst" ∷ s.[watchableStore, go!"store"] ↦□ st ∗
    "#Hs" ∷ isStoreX st γ.st X Y F Fr fz ∗
    "#Hrv" ∷ st.[store, go!"ReadView"] ↦□
      (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
    "#Hrvkv" ∷ rv.[readView, go!"kv"] ↦□
      (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s : GoInterface) ∗
    "#Hmu" ∷ sync.isRWMutexGuard (wsMuAddr s) (watchStoreInvX s γ Z) ∗
    "#Hvc" ∷ s.[watchableStore, go!"victimc"] ↦□ vc ∗
    "#Hvcb" ∷ isChanBag (V := Unit) γv vc (fun _ => iprop(True)) ∗
    "#Hstopc" ∷ s.[watchableStore, go!"stopc"] ↦□ stc ∗
    "#Hstop" ∷ isStopChan stc ∗
    "#Hfrz" ∷ wsFrozenM γ.st ∗
    "%Hwq" ∷ ⌜γ.st.watchQ = true⌝)

instance isWatchableStoreX_persistent (s st : Loc) (γ : WsNames) (X : Qp → Log → Int → IProp GF)
    (Y : Log → IProp GF) (F Fr : IProp GF) (fz : GName) (Z : Qp → WsState → IProp GF) :
    Persistent (isWatchableStoreX (GF := GF) s st γ X Y F Fr fz Z) := by
  unfold isWatchableStoreX; simp only [named]; infer_instance

/-- The watchable store's inner store. -/
theorem isWatchableStoreX_isStore (s st : Loc) (γ : WsNames) (X : Qp → Log → Int → IProp GF)
    (Y : Log → IProp GF) (F Fr : IProp GF) (fz : GName) (Z : Qp → WsState → IProp GF) :
    isWatchableStoreX (GF := GF) s st γ X Y F Fr fz Z ⊢ isStoreX st γ.st X Y F Fr fz := by
  unfold isWatchableStoreX
  iintro ⟨%vc, %stc, %rv, %γv, H⟩
  iNamed H
  iexact Hs

/-- **A holder of a watchable store's `s.mu` finds the inner store's `s.revMu` not restoring**
(`revMuInv_open_ws`, with a slot). -/
theorem revMuInvX_open_ws (s st : Loc) (γ : WsNames) (X : Qp → Log → Int → IProp GF) (q : Qp) :
    s.[watchableStore, go!"store"] ↦□ st ∗ revMuInvX (GF := GF) st γ.st X q ∗ wsFields s γ 1 ⊢
      (∃ γp : StoreNames, revMuBodyX st γ.st γp X q ∗ revMuTok γ.st γp q) ∗ wsFields s γ 1 := by
  iintro ⟨#Hst, H, Hw⟩
  iunfold wsFields at Hw
  icases Hw with ⟨%st', #Hst', Hf, Hd⟩
  icombine Hst Hst' gives %Heq
  subst Heq
  iunfold fieldShare at Hf
  icases Hf with ⟨%p, %o, Hf⟩
  iunfold fieldShareAt at Hf
  iNamed Hf
  withPhys_simp
  icases revMuInvX_open st γ.st X q _ $$ [H Hfrst] with ⟨⟨%γp, H, Htk⟩, Hfrst⟩
  · iframe H Hfrst
  icases revMuBodyLX_wsd st γ.st γp X q $$ [$H $Hd] with ⟨H, Hd⟩
  isplitl [H Htk]
  · iexists γp; iframe H Htk
  iunfold wsFields
  iexists st
  iframe Hst Hd
  iunfold fieldShare
  iexists p, o
  iunfold fieldShareAt
  simp only [named]
  withPhys_simp
  iframe Hcur Hflds Hfrst Hph

/-! ## The API's instance for the watchable store -/

/-- **The pending revision agrees with the notified log**: a pending revision is the notified log's
last (the watchable `End` notifies, extending `σ.Lmu`, before it bumps). -/
def pndOk (Lmu : Log) (p : Option (List Change)) : Prop :=
  ∀ ps, p = some ps → Lmu.getLast? = some ps

/-- **The watchable store's lock's part of the API's ghost state** at fraction `q` (§1): a quarter
of `q` of the pending revision, agreeing with the lock's notified log. -/
def wsAbs (a : AbsNames) (q : Qp) (σ : WsState) : IProp GF :=
  iprop(∃ p : Option (List Change), pndPart a q.half.half p ∗ ⌜pndOk σ.Lmu p⌝)

theorem wsAbs_fractional (a : AbsNames) (σ : WsState) :
    Fractional (fun q => wsAbs (GF := GF) a q σ) := by
  unfold wsAbs
  refine fractional_exists_agree _ (fun p => wFractional_sep
    (wFractional_half (wFractional_half (pndPart_fractional a p))) (wFractional_pure _)) ?_
  intro p1 p2 q1 q2
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  iapply pndPart_agree a _ _ p1 p2
  iframe H1 H2

/-- **The watchable store, with the API's ghost state** (§1, §2): its inner store `isStoreA`'s
slots (a watchable store's writer holds a quarter of the pending revision, `pndW`), and the lock's
quarter of the pending revision. -/
def isWatchableStoreA (s st : Loc) (γ : WsNames) (a : AbsNames) : IProp GF :=
  isWatchableStoreX s st γ (revMuAbs a) (writerAbs a (pndW γ.st)) (shareTok a 1) (shareTok a 1)
    a.frz (wsAbs a)

instance isWatchableStoreA_persistent (s st : Loc) (γ : WsNames) (a : AbsNames) :
    Persistent (isWatchableStoreA (GF := GF) s st γ a) := by
  unfold isWatchableStoreA; infer_instance

theorem isWatchableStoreA_isStore (s st : Loc) (γ : WsNames) (a : AbsNames) :
    isWatchableStoreA (GF := GF) s st γ a ⊢ isStoreA st γ.st a :=
  isWatchableStoreX_isStore s st γ _ _ _ _ _ _

/-! ## The watch stream's mutex invariant with a slot -/

/-- **The state `ws.mu` guards, with a slot** `Z` at the next id, the closed flag and the watcher
map (`watchStreamInv`). -/
def watchStreamInvX (ws : Loc) (P : WatchParams GF) (ch : GoChan) (γc : WatchChanNames)
    (γ : WsStreamNames) (Z : w64 → Bool → GMap w64 Loc → IProp GF) : IProp GF :=
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
    "#Hws" ∷ □ (∀ (id : w64) (w : Loc), ⌜WM !! id = some w⌝ -∗ P.IW w ∗ P.OC w γc ∗
      ∃ (r : WatchRange) (fcs : GoSlice) (lo : Nat), P.IWF w r fcs lo ∗ ⌜r.id = id⌝) ∗
    "#Hcs" ∷ □ (∀ (id : w64) (c : GoFunc) (w : Loc), ⌜CM !! id = some c⌝ -∗
      ⌜WM !! id = some w⌝ -∗ cancelSpec P c w) ∗
    "Hids" ∷ idsInv γ nextID ∗
    "Hcl" ∷ (if closed then watchStreamOpen γ ∗ □ (∀ (id : w64) (w : Loc), ⌜WM !! id = some w⌝ -∗ P.WC w) else
      ∃ L : List Loc, P.CR ch γc L ∗
        □ (∀ w : Loc, ⌜w ∈ L⌝ -∗ ((∃ id : w64, ⌜WM !! id = some w⌝) ∨ cancelledFor P γc w)) ∗
        ⌜sint.Z nextID + aboveCnt nextID WM ≤ L.length ∧ L.length + 3 ≤ 2 ^ 63⌝) ∗
    "HZ" ∷ Z nextID closed WM)

/-- **The stream, with a slot** (`isWatchStream`, over `watchStreamInvX`). -/
def isWatchStreamX (ws : Loc) (wa : GoInterface) (P : WatchParams GF) (γ : WsStreamNames)
    (Z : w64 → Bool → GMap w64 Loc → IProp GF) : IProp GF :=
  iprop(∃ (ch : GoChan) (γc : WatchChanNames),
    "%Hγc" ∷ ⌜γ.ids = γc.ids ∧ γ.prog = γc.prog ∧ γ.sentl = γc.sentl ∧ γ.rsn = γc.rsn ∧
      γ.regi = γc.regi⌝ ∗
    "#Hwa" ∷ ws.[watchStream, go!"watchable"] ↦□ wa ∗
    "#Hch" ∷ ws.[watchStream, go!"ch"] ↦□ ch ∗
    "#HC" ∷ P.C ch ∗
    "#Hwable" ∷ isWatchable wa P ∗
    "#Hclose" ∷ □ (∀ L : List Loc,
      {{ P.CR ch γc L ∗ □ (∀ w : Loc, ⌜w ∈ L⌝ -∗ P.WC w) }}
        (App (Val #(functions go.close
          [go.GoType.ChannelType go.ChanDir.sendrecv WatchResponse.ty])) (Val #ch))
      {{ RET #(); True }}) ∗
    "#Hmu" ∷ sync.isMutex (ws.[watchStream, go!"mu"]) (watchStreamInvX ws P ch γc γ Z))

instance isWatchStreamX_persistent (ws : Loc) (wa : GoInterface) (P : WatchParams GF)
    (γ : WsStreamNames) (Z : w64 → Bool → GMap w64 Loc → IProp GF) :
    Persistent (isWatchStreamX ws wa P γ Z) := by
  unfold isWatchStreamX; simp only [named]; infer_instance

/-! ## The stream's API ghost state (§1, the countable part) -/

/-- A watch range, as a countable tuple (key, end, start revision, id). -/
abbrev WRangeC := GoString × Option GoString × w64 × w64

def wrC (r : WatchRange) : WRangeC := (r.key, r.end?, r.startRev, r.id)

theorem wrC_inj {r r' : WatchRange} (h : wrC r = wrC r') : r = r' := by
  cases r; cases r'
  simp only [wrC, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- **A watcher of the stream's state, countable**: its range, the ghost name of its saved filters
(`savedFilters`), its first revision `lo`, its stamp `k` and whether it is live (`WInfo` but its
filters, which the name holds). -/
abbrev WInfoC := WRangeC × GName × Nat × Nat × Bool

/-- **A registry entry** (`ι.reg`, persistent once minted): the watcher, its range, its filters'
name, its first revision and its stamp. -/
abbrev RegC := Loc × WRangeC × GName × Nat × Nat

/-- The stream's API ghost names: its state `ι.sst` (the countable part, ¾ the client, ¼ the
mutex), its registry `ι.reg` (authority ½ the client, ½ the mutex) and its cancelled ids `ι.dead`
(as the registry). -/
structure StreamAbsNames where
  sst : GName
  reg : GName
  dead : GName

/-- A share of the stream's state (countable part: watchers by id, and the closed flag). -/
def sstPart (ι : StreamAbsNames) (q : Qp) (S : GMap w64 WInfoC × Bool) : IProp GF :=
  ghostVar ι.sst q S

/-- **A watcher's state's countable part matches its info** (with its filters saved under the
name). -/
def winfoIs (w : WInfo) (c : WInfoC) : IProp GF :=
  iprop(⌜c.1 = wrC w.rg ∧ c.2.2.1 = w.lo ∧ c.2.2.2.1 = w.k ∧ c.2.2.2.2 = w.live⌝ ∗
    savedFilters c.2.1 w.fs)

/-- **The mutex's part of the stream's API ghost state** (first cut): its quarter of the stream's
state, at the mutex's closed flag, and its halves of the registry's and the cancelled set's
authorities. -/
def streamAbs (ι : StreamAbsNames) (_nextID : w64) (closed : Bool) (_WM : GMap w64 Loc) : IProp GF :=
  iprop(∃ (S : GMap w64 WInfoC × Bool) (R : GMap w64 RegC) (D : GMap w64 Unit),
    sstPart ι (1 : Qp).half.half S ∗ ghostMapAuth ι.reg (1 : Qp).half R ∗
    ghostMapAuth ι.dead (1 : Qp).half D ∗ ⌜S.2 = closed⌝)

/-- **The stream, with the API's ghost state.** -/
def isWatchStreamA (ws : Loc) (wa : GoInterface) (P : WatchParams GF) (γ : WsStreamNames)
    (ι : StreamAbsNames) : IProp GF :=
  isWatchStreamX ws wa P γ (streamAbs ι)

instance isWatchStreamA_persistent (ws : Loc) (wa : GoInterface) (P : WatchParams GF)
    (γ : WsStreamNames) (ι : StreamAbsNames) : Persistent (isWatchStreamA ws wa P γ ι) := by
  unfold isWatchStreamA; infer_instance

end reprs

end api
end mvcc
end EtcdGrove
end Perennial
