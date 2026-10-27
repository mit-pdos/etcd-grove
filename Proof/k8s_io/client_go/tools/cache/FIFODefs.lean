/-
client-go's `RealFIFO` (`tools/cache/the_real_fifo.go`) as the informers configure it under the
`AtomicFIFO` gate (`newQueueFIFO`: atomic events, bookmark deltas, no transformer, no known
objects; `UnlockWhileProcessing` either way): its abstract state, its lock's resource and the
predicates its specs are stated with. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`.

* `FD`: a queued delta, abstractly: an object's change (`Added`/`Updated`/`Deleted`, the object
  meeting the client's contract `OK`), a relist (`ReplacedAll`: the list's objects, owned, and its
  resource version), a bookmark (its resource version). `fdAt OK d v`: the Go `Delta` `v` is `d`.
* `FQ`: the queue's state: the deltas, `populated`, `initialPopulationCount`, `syncedClosed`
  (`synced`), `closed`.
* `fifoSt γ q`: the client's half of the state; the other half is the lock's.
* (`fifoRes` holds an exclusive token, `γ.ex`, so that two copies of it are absurd.)
* The FIFO's mutex is an `RWMutex` locked only as a writer (`Lock`; its `Cond` waits on it). Its
  guard needs a fractional resource: the guard's resource is a fractional token (`fifoTok γ q`),
  and the FIFO's resource (`fifoRes`) is in an invariant with the token's whole (`fifoInv`): the
  writer holding the token takes the resource out and puts the token in, and back at `Unlock`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

/-- A queued delta, abstractly. -/
inductive FD [FfiSyntax] where
  | obj (t : GoString) (o : GoInterface)
  | replaced (objs : List GoInterface) (rv : GoString)
  | bookmark (rv : GoString)

/-- `FD` as a sum, for its encoding. -/
def FD.toSum [FfiSyntax] : FD → (GoString × GoInterface) ⊕ ((List GoInterface × GoString) ⊕ GoString)
  | .obj t o => .inl (t, o)
  | .replaced objs rv => .inr (.inl (objs, rv))
  | .bookmark rv => .inr (.inr rv)

instance FD.countable [FfiSyntax] : Pos.Countable FD :=
  .ofInjective (fun d => Pos.Countable.encode d.toSum)
    (by
      intro a b h
      rw [Pos.encode_eq_iff] at h
      cases a <;> cases b <;> simp_all [FD.toSum])

/-- **The queue's state.** -/
structure FQ [FfiSyntax] where
  items : List FD
  populated : Bool
  initCount : Nat
  synced : Bool
  closed : Bool

instance FQ.countable [FfiSyntax] : Pos.Countable FQ :=
  .ofInjective (fun q => Pos.Countable.encode (q.items, q.populated, q.initCount, q.synced, q.closed))
    (by
      rintro ⟨a, b, c, d, e⟩ ⟨a', b', c', d', e'⟩ h
      simp only [Pos.encode_eq_iff, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      rfl)

/-- `Add`/`Update`/`Delete(obj)`: populated, synced if no initial item is left (`checkSynced`),
the delta `{t, obj}` queued. -/
def FQ.addObj [FfiSyntax] (t : GoString) (o : GoInterface) (q : FQ) : FQ :=
  { q with items := q.items ++ [.obj t o], populated := true,
           synced := q.synced || q.initCount == 0 }

/-- `Replace(objs, rv)` (atomic events): the relist's delta queued; the first time (not yet
populated), populated with the queue's length as the initial items (never synced then: the
queue holds at least the relist). -/
def FQ.replace [FfiSyntax] (objs : List GoInterface) (rv : GoString) (q : FQ) : FQ :=
  if q.populated then { q with items := q.items ++ [.replaced objs rv] }
  else { q with items := q.items ++ [.replaced objs rv], populated := true,
                initCount := q.items.length + 1 }

theorem FQ.replace_synced [FfiSyntax] (objs : List GoInterface) (rv : GoString) (q : FQ) :
    (q.replace objs rv).synced = q.synced := by
  unfold FQ.replace; split <;> rfl

/-- `Pop`'s deferred step, after the delta's processing: one initial item fewer, synced once none
is left (`checkSynced`). -/
def FQ.popDone [FfiSyntax] (q : FQ) : FQ :=
  if 0 < q.initCount then
    { q with initCount := q.initCount - 1,
             synced := q.synced || (q.populated && q.initCount - 1 == 0) }
  else q

/-- The FIFO's ghost names: its state's, its lock token's, its synced flag's. -/
structure FifoNames where
  st : GName
  tok : GName
  sy : GName
  ex : GName
  ch : ChanNames

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **A Go `Delta` is the abstract delta `d`.** -/
def fdAt (OK : GoInterface → IProp GF) (d : FD) (v : Delta) : IProp GF :=
  match d with
  | .obj t o => iprop(⌜v = Delta.mk t o ∧
      ∃ (ty : go.GoType) (w : val), o = interface.mkOk (go.GoType.PointerType ty) w⌝ ∗ □ OK o)
  | .replaced objs rv => iprop(∃ sl : GoSlice, ⌜v = Delta.mk go!"ReplacedAll"
      (interface.mkOk ReplacedAllInfo.ty #(ReplacedAllInfo.mk rv sl))⌝ ∗ sl ↦* objs ∗
      □ ([∗list] o ∈ objs, OK o))
  | .bookmark rv => iprop(⌜v = Delta.mk go!"Bookmark"
      (interface.mkOk BookmarkInfo.ty #(BookmarkInfo.mk rv))⌝)

/-- **The synced flag has been set** (persistent): the FIFO's `synced` channel's broadcast. -/
def fifoSyncedLb (γ : FifoNames) : IProp GF := dghostVar γ.sy .discard true

instance fifoSyncedLb_persistent (γ : FifoNames) : Persistent (fifoSyncedLb (GF := GF) γ) := by
  unfold fifoSyncedLb; infer_instance

/-- The synced flag's part: the client's half while unset, a lower bound once set. -/
def syncedPart (γ : FifoNames) (b : Bool) : IProp GF :=
  if b then fifoSyncedLb γ else dghostVar γ.sy (.own (1 : Qp).half) false

/-- **The client's half of the queue's state.** -/
def fifoSt (γ : FifoNames) (q : FQ) : IProp GF :=
  iprop(ghostVar γ.st (1 : Qp).half q ∗ syncedPart γ q.synced)

/-- The lock's token. -/
def fifoTok (γ : FifoNames) (q : Qp) : IProp GF := ghostVar γ.tok q ()

/-- **The FIFO's resource**: the lock's half of the state, the fields it holds, each queued delta,
the `synced` channel (closed once synced, broadcasting `fifoSyncedLb`). -/
def fifoRes (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) (ch : GoChan) : IProp GF :=
  iprop(∃ (q : FQ) (sl : GoSlice) (vs : List Delta),
    ghostVar γ.ex 1 () ∗ ghostVar γ.st (1 : Qp).half q ∗
    (if q.synced then iprop(True) else dghostVar γ.sy (.own (1 : Qp).half) false) ∗
    f.[RealFIFO, go!"items"] ↦ sl ∗ sl ↦* vs ∗ ownSliceCap Delta sl (DFrac.own 1) ∗
    ([∗list] d;v ∈ q.items;vs, fdAt OK d v) ∗
    f.[RealFIFO, go!"populated"] ↦ q.populated ∗
    f.[RealFIFO, go!"initialPopulationCount"] ↦ (W64 q.initCount) ∗ ⌜q.initCount < 2 ^ 63⌝ ∗
    f.[RealFIFO, go!"syncedClosed"] ↦ q.synced ∗
    f.[RealFIFO, go!"closed"] ↦ q.closed ∗
    ownBroadcastChan ch γ.ch (fifoSyncedLb γ) (if q.synced then .Done else .Pending))

/-- The invariant holding the FIFO's resource or the lock token's whole. -/
def fifoInvN : Namespace := nroot.@"realfifo"

def fifoInv (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) (ch : GoChan) : IProp GF :=
  inv fifoInvN iprop(fifoRes f γ OK ch ∨ fifoTok γ 1)

instance fifoInv_persistent (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) (ch : GoChan) :
    Persistent (fifoInv (GF := GF) f γ OK ch) := by
  unfold fifoInv; infer_instance

/-- A gauge's and a histogram's contracts: `Set` and `Observe` return. -/
def obsOk (h : HistogramMetric) : IProp GF :=
  match h with
  | .nil => iprop(False)
  | .ok i => iprop(∀ x : w64, {{ True }} (App (Val #(methods i.ty go!"Observe" i.v)) (Val #x))
      {{ RET #(); True }})

instance obsOk_persistent (h : HistogramMetric) : Persistent (obsOk (GF := GF) h) := by
  cases h <;> unfold obsOk <;> infer_instance

/-- **The key function's contract, as the FIFO needs it**: on an object meeting `OK`, no error (the
FIFO discards the key: `addToItems_locked` only checks that the object has one). -/
def keyNoErr (OK : GoInterface → IProp GF) (kf : GoFunc) : IProp GF :=
  iprop(∀ o : GoInterface, {{ □ OK o }} (App (Val #kf) (Val #o))
    {{ (k : GoString) (err : GoInterface), RET (PairV #k #err); ⌜err = interface.nil⌝ }})

instance keyNoErr_persistent (OK : GoInterface → IProp GF) (kf : GoFunc) :
    Persistent (keyNoErr (GF := GF) OK kf) := by
  unfold keyNoErr; infer_instance

/-- **The key function returns** on any object (its slow-queue trace keys a delta of any kind;
`MetaNamespaceKeyFunc`'s accessor fails on a non-object, an error the trace ignores). -/
def keyAny (kf : GoFunc) : IProp GF :=
  iprop(∀ o : GoInterface, {{ True }} (App (Val #kf) (Val #o))
    {{ (k : GoString) (err : GoInterface), RET (PairV #k #err); True }})

instance keyAny_persistent (kf : GoFunc) : Persistent (keyAny (GF := GF) kf) := by
  unfold keyAny; infer_instance

/-- **The FIFO** (persistent): its fixed fields (the informers' configuration), the lock's guard
over the token, the condition variable over the lock, the invariant. -/
def isFIFO (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) : IProp GF :=
  iprop(∃ (ch : GoChan) (kf : GoFunc) (mp : Loc) (g : GaugeMetric) (h : HistogramMetric)
      (uwp : Bool) (idn : InformerNameAndResource),
    f.[RealFIFO, go!"keyFunc"] ↦□ kf ∗ keyNoErr OK kf ∗
    f.[RealFIFO, go!"transformer"] ↦□ func.nil ∗
    f.[RealFIFO, go!"emitAtomicEvents"] ↦□ true ∗
    f.[RealFIFO, go!"emitDeltaTypeBookmark"] ↦□ true ∗
    f.[RealFIFO, go!"unlockWhileProcessing"] ↦□ uwp ∗
    f.[RealFIFO, go!"batchSize"] ↦□ (W64 1000) ∗
    f.[RealFIFO, go!"synced"] ↦□ ch ∗
    f.[RealFIFO, go!"metrics"] ↦□ mp ∗
    mp.[fifoMetrics, go!"numberOfQueuedItem"] ↦□ g ∗ gaugeOk g ∗
    mp.[fifoMetrics, go!"processingLatency"] ↦□ h ∗ obsOk h ∗
    sync.isRWMutexGuard (f.[RealFIFO, go!"lock"]) (fifoTok γ) ∗
    sync.isCond (f.[RealFIFO, go!"cond"])
      ⟨go.GoType.PointerType _root_.Perennial.sync.RWMutex.ty, #(f.[RealFIFO, go!"lock"])⟩ ∗
    fifoInv f γ OK ch ∗
    f.[RealFIFO, go!"identifier"] ↦□ idn ∗ keyAny kf)

set_option synthInstance.maxSize 512 in
set_option synthInstance.maxHeartbeats 400000 in
instance isFIFO_persistent (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) :
    Persistent (isFIFO (GF := GF) f γ OK) := by
  unfold isFIFO; infer_instance

theorem qp_one_add_false (q : Qp) (h : (1 : Qp) + q ≤ 1) : False := by
  have h1 : (1 : Rat) + q.val ≤ 1 := h
  have := q.2
  grind

instance fifoTok_fractional (γ : FifoNames) : Fractional (fifoTok (GF := GF) γ) := by
  unfold fifoTok; infer_instance

open Iris.ProofMode in
/-- **Taking the FIFO's resource** with the lock's token: two credits strip the laters. -/
theorem fifo_acquire (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) (ch : GoChan) :
    ⊢ fifoInv f γ OK ch -∗ £ 1 -∗ £ 1 -∗ ▷ fifoTok γ 1 ={⊤}=∗ fifoRes f γ OK ch := by
  iintro #Hinv Hlc1 Hlc2 Htok
  unfold fifoInv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  imod lc_fupd_elim_later $$ Hlc2 Htok with Htok
  icases Hi with (HR | Htok')
  · imod Hclose $$ [Htok] with -
    · inext; iright; iexact Htok
    imodintro; iexact HR
  · iunfold fifoTok at Htok Htok'
    ihave %Hbad := ghostVar_valid_2 γ.tok () 1 () 1 $$ Htok Htok'
    exact (qp_one_add_false _ Hbad.1).elim

open Iris.ProofMode in
/-- **Giving the FIFO's resource back** for the lock's token, to unlock: a credit strips the
later of the invariant's content (another resource would duplicate the items' field). -/
theorem fifo_release (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) (ch : GoChan) :
    ⊢ fifoInv f γ OK ch -∗ £ 1 -∗ fifoRes f γ OK ch ={⊤}=∗ ▷ fifoTok γ 1 := by
  iintro #Hinv Hlc HR
  unfold fifoInv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with (HR' | Htok)
  · iunfold fifoRes at HR HR'
    icases HR with ⟨%q, %sl, %vs, Hex, -⟩
    icases HR' with ⟨%q', %sl', %vs', Hex', -⟩
    ihave %Hbad := ghostVar_valid_2 γ.ex () 1 () 1 $$ Hex Hex'
    exact (qp_one_add_false _ Hbad.1).elim
  · imod Hclose $$ [HR] with -
    · inext; ileft; iexact HR
    imodintro; inext; iexact Htok

open Iris.ProofMode in
/-- The FIFO's lock as the `Locker` its `Cond` waits on (`&f.lock`, a writer). -/
theorem fifo_locker (rw : Loc) (P : Qp → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isRWMutexGuard rw P ⊢
      sync.isLocker ⟨go.GoType.PointerType _root_.Perennial.sync.RWMutex.ty, #rw⟩
        iprop(sync.ownRWMutexWLocked rw P ∗ ▷ P 1) := by
  iintro ⟨#Hsync, #Hg⟩
  unfold sync.isLocker
  isplitl
  · imodintro
    iintro %Φ - HΦ
    wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as H
    iapply HΦ $$ H
  · imodintro
    iintro %Φ ⟨Hl, HP⟩ HΦ
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hl $HP]
    iapply HΦ; itrivial

open Iris.ProofMode in
/-- A delta queued at the end. -/
theorem fifo_push (OK : GoInterface → IProp GF) (ds : List FD) (vs : List Delta) (d : FD)
    (v : Delta) :
    ([∗list] x;y ∈ ds;vs, fdAt OK x y) ∗ fdAt OK d v ⊢
      [∗list] x;y ∈ ds ++ [d];vs ++ [v], fdAt OK x y := by
  iintro ⟨Hds, Hd⟩
  iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ x y => fdAt OK x y)).2
  iframe

open Iris.ProofMode in
/-- **A linearization point that keeps the synced flag**: with the lock's half, the state
becomes `upd q`. -/
theorem fifoSt_update (γ : FifoNames) (q : FQ) (upd : FQ → FQ)
    (hsy : ∀ q, (upd q).synced = q.synced) (K : FQ → IProp GF) :
    ghostVar γ.st (1 : Qp).half q ∗
      (|={⊤ \ ∅, ∅}=> ∃ q', fifoSt γ q' ∗ (fifoSt γ (upd q') ={∅, ⊤ \ ∅}=∗ K q')) ⊢
      |={⊤}=> ghostVar γ.st (1 : Qp).half (upd q) ∗ K q := by
  iintro ⟨Hst, HAU⟩
  rw [Iris.Std.LawfulSet.diff_empty]
  imod HAU with ⟨%q', Hst', Hcl⟩
  iunfold fifoSt at Hst'
  icases Hst' with ⟨Hst', Hsy⟩
  icombine Hst Hst' gives % ⟨_, heq⟩
  subst heq
  imod ghostVar_update_halves (upd q) $$ Hst Hst' with ⟨Hst, Hst'⟩
  imod Hcl $$ [Hst' Hsy] with HK
  · iunfold fifoSt; iframe; rw [hsy]; iexact Hsy
  imodintro
  iframe

open Iris.ProofMode in
/-- **A linearization point that may set the synced flag** (never unsets it): with the lock's
half and its part of the flag, the state becomes `upd q`; once synced, the flag's lower bound. -/
theorem fifoSt_update_sy (γ : FifoNames) (q : FQ) (upd : FQ → FQ)
    (hmono : q.synced = true → (upd q).synced = true) (K : FQ → IProp GF) :
    ghostVar γ.st (1 : Qp).half q ∗
      (if q.synced then iprop(True) else dghostVar γ.sy (.own (1 : Qp).half) false) ∗
      (|={⊤ \ ∅, ∅}=> ∃ q', fifoSt γ q' ∗ (fifoSt γ (upd q') ={∅, ⊤ \ ∅}=∗ K q')) ⊢
      |={⊤}=> ghostVar γ.st (1 : Qp).half (upd q) ∗
        (if (upd q).synced then iprop(True) else dghostVar γ.sy (.own (1 : Qp).half) false) ∗
        (if (upd q).synced then fifoSyncedLb γ else iprop(True)) ∗ K q := by
  iintro ⟨Hst, Hsy, HAU⟩
  rw [Iris.Std.LawfulSet.diff_empty]
  imod HAU with ⟨%q', Hst', Hcl⟩
  iunfold fifoSt at Hst'
  icases Hst' with ⟨Hst', Hsy'⟩
  icombine Hst Hst' gives % ⟨_, heq⟩
  subst heq
  imod ghostVar_update_halves (upd q) $$ Hst Hst' with ⟨Hst, Hst'⟩
  iunfold syncedPart at Hsy'
  cases hq : q.synced with
  | true =>
    have hu := hmono hq
    rw [hu]
    simp only [↓reduceIte]
    icases Hsy' with #Hlb
    imod Hcl $$ [Hst'] with HK
    · iunfold fifoSt; iframe; iunfold syncedPart; rw [hu]; simp only [↓reduceIte]; iexact Hlb
    imodintro
    iframe; iframe #
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hu : (upd q).synced with
    | true =>
      simp only [↓reduceIte]
      imod dghostVar_update_halves true _ _ _ $$ Hsy Hsy' with ⟨Hsy, -⟩
      imod dghostVar_persist _ _ _ $$ Hsy with #Hlb
      imod Hcl $$ [Hst'] with HK
      · iunfold fifoSt; iframe; iunfold syncedPart; rw [hu]; simp only [↓reduceIte]
        iunfold fifoSyncedLb; iexact Hlb
      imodintro
      iframe
      iunfold fifoSyncedLb; iexact Hlb
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      imod Hcl $$ [Hst' Hsy'] with HK
      · iunfold fifoSt; iframe; iunfold syncedPart; rw [hu]; simp only [Bool.false_eq_true, ↓reduceIte]
        iexact Hsy'
      imodintro
      iframe

open Iris.ProofMode in
/-- **Committing a caller's fancy update at the lock's state** `q`: its client half is `q`; the
update gives back `upd q` (a step that keeps the synced flag) and `K`. -/
theorem fifo_commit (γ : FifoNames) (q : FQ) (upd : FQ → FQ)
    (hsy : (upd q).synced = q.synced) (K : IProp GF) :
    ghostVar γ.st (1 : Qp).half q ∗
      (|={⊤, ∅}=> ∃ q', fifoSt γ q' ∗ (⌜q' = q⌝ -∗ fifoSt γ (upd q') ={∅, ⊤}=∗ K)) ⊢
      |={⊤}=> ghostVar γ.st (1 : Qp).half (upd q) ∗ K := by
  iintro ⟨Hst, HAU⟩
  imod HAU with ⟨%q', Hst', Hcl⟩
  iunfold fifoSt at Hst'
  icases Hst' with ⟨Hst', Hsy⟩
  icombine Hst Hst' gives % ⟨_, heq⟩
  subst heq
  imod ghostVar_update_halves (upd q) $$ Hst Hst' with ⟨Hst, Hst'⟩
  imod Hcl $$ %rfl [Hst' Hsy] with HK
  · iunfold fifoSt; iframe; rw [hsy]; iexact Hsy
  imodintro
  iframe

open Iris.ProofMode in
/-- **A reader's linearization point**: the lock's half agrees with the client's. -/
theorem fifoSt_peek (γ : FifoNames) (q : FQ) (K : FQ → IProp GF) :
    ghostVar γ.st (1 : Qp).half q ∗
      (|={⊤ \ ∅, ∅}=> ∃ q', fifoSt γ q' ∗ (fifoSt γ q' ={∅, ⊤ \ ∅}=∗ K q')) ⊢
      |={⊤}=> ghostVar γ.st (1 : Qp).half q ∗ K q := by
  iintro ⟨Hst, HAU⟩
  rw [Iris.Std.LawfulSet.diff_empty]
  imod HAU with ⟨%q', Hst', Hcl⟩
  iunfold fifoSt at Hst'
  icases Hst' with ⟨Hst', Hsy⟩
  icombine Hst Hst' gives % ⟨_, heq⟩
  subst heq
  imod Hcl $$ [Hst' Hsy] with HK
  · iunfold fifoSt; iframe
  imodintro
  iframe

end defs

end cache
end EtcdGrove
end Perennial

