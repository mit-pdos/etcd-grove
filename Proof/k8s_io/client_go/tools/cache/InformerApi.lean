/-
**The shared index informer's API, as its clients see it** (the DaemonSet run's track A,
`notes/k8s-daemonset-run/design.md`: "The informer as the controller sees it", "The handler
contract"). Lean-first. What the factory's typed informers hand out (`Informer()`) and what the
controller's constructor and handlers use; the internals (`InformerInv`, `InformerGlue`, the
reflector's `RefInf`) are what its proofs will rest on.

* `InfH`: an informer's fixed locations and ghost names: its store (`cache` `ca` over the
  thread-safe store `ts`, key function `kf`, names `γt`), the names of its FIFO's state (`γf`: the
  informer invariant reads only its `st`/`sy` components, which the informer's constructor
  allocates before the FIFO exists, `RunWithContext` creating the FIFO over them), the informer
  invariant's names `γi` (among them the store's index registry `γi.ix`: index name to the id of
  its relation in the store's family `Fam`, authoritative in the invariant over the store's
  `fnIds`).
* `infView γa r I Fam` (persistent): the store (`isCache` over the registered objects `infObj`, with
  indices `Fam`) and the informer invariant `infInv` (the store is the server's log's table at its
  version, versions monotone). It is the body of the controller's `dsctl.infAt` (track B):
  `infAt γa r ⟨…⟩ Fam` is `infView γa r I Fam` for the `InfLoc` with `I`'s fields.
* `infIdx I n j` (persistent): the store's index named `n` is relation `Fam j`, for good (an
  index is never removed; `AddIndexers` adds): a store read through the invariant sees
  `σs.fnIds !! n = some j` (`InformerAlloc.lean`, `infInv_readIdxAU`).
* `infObjIs γi r x o`: the Go object `x` is registered with the model object `o` of resource `r`
  (owned read-only, `objAt x DFrac.discard o`); `infObj γi r x` is `∃ o, infObjIs γi r x o`.
* **The handler contract** `handlerSpec γa r γi h H`: the handler `h` (a `ResourceEventHandler`)
  takes each event `e` it is called with, with the event's facts `evFacts γa r γi e`, from the
  registering code's resource `H evs` (the events delivered so far, on the listener's goroutine) to
  `H (evs ++ [e])` (`lhOk`, the listener's contract, at `Q _ e := evFacts …`). The facts
  (`evFacts`), all persistent:
  - `OnAdd(x, _)`: `x` registered with `o`, which is at its key in the log's table at some version
    of a past state (`inLog`);
  - `OnUpdate(old, cur)`: both registered (`oo`, `on`), of one key, `oo` in the table at a version
    `u`, `on` at a version `v ≥ u` (so a UID changes only across a deletion);
  - `OnDelete(x)`: `x` is a registered object `y`, or the tombstone `DeletedFinalStateUnknown{k, y}`
    of one, and `y`'s key is absent from the table at some version `v` of a past state, `y`'s own
    version at most `v` (`goneAfter`: the deletion is in the log, from `v` on the object is gone).
* `syncedFn f γi` (persistent): the function `f` (an `InformerSynced`, the informer's `HasSynced`
  method value) returns a boolean, `true` with `syncedFacts γi true` (the first list's version `v`,
  `infFirst`, and the store's version at least `v` from then on, `infRvLb`).
* `infReaders I r Fam` (persistent): the store's reader slots in a thread pool (under the thread
  bound), borrowed with a thread token: what a reading thread (a worker, a handler) uses.
* `isInformer x γa r I Fam` (persistent): **the informer as an interface value** (a
  `SharedIndexInformer`, whatever wrapper `x` is: `Informer()` returns a `*typedSharedIndexInformer`
  around the factory's): `infView`, `infReaders`, and the contracts of the methods the controller calls on it
  (`GetStore`, `GetIndexer`, `HasSynced` called and as a method value, `AddEventHandlerWithOptions`,
  `AddIndexers`).
* `infRunOk x` (persistent): `x.RunWithContext(ctx)` runs the informer (the factory's `Start`
  holds it, not the clients).

Scope (marked): handlers without a resync period (`HandlerOptions.ResyncPeriod` `nil`, and the
factory's default resync `0`): a resyncing handler's synthetic updates are not covered.
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefInf
public import Proof.k8s_io.client_go.tools.cache.ListenerDefs
public import Proof.k8s_io.client_go.tools.cache.RefCtx
public import Perennial.Proof.ThreadPool
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Reader

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open Iris Iris.BI apimodel cache k8s_io.client_go.tools.cache

/-- An informer's fixed locations and ghost names (see the file header). -/
structure InfH [GooseExts] where
  ca : Loc
  ts : Loc
  kf : GoFunc
  γf : FifoNames
  γt : TsNames
  γi : InfNames

/-! ### Encodings (the factory's registry of its informers is a ghost map of `InfH`) -/

instance Res.countable : Pos.Countable Res :=
  .ofInjective (fun r => match r with
      | .pods => Pos.Countable.encode (0 : Nat)
      | .nodes => Pos.Countable.encode (1 : Nat)
      | .daemonSets => Pos.Countable.encode (2 : Nat)
      | .revisions => Pos.Countable.encode (3 : Nat))
    (by intro a b h; cases a <;> cases b <;> simp_all [Pos.encode_eq_iff])

/-- A channel's ghost names as numbers. -/
def chanCode (c : ChanNames) : List Nat :=
  [c.stateName, c.offerLockName, c.offerParkedPropName, c.offerParkedPredName,
    c.offerContinuationName, c.chanCap.toNat]

theorem chanCode_inj {c c' : ChanNames} (h : chanCode c = chanCode c') : c = c' := by
  obtain ⟨a, b, c, d, e, f⟩ := c
  obtain ⟨a', b', c', d', e', f'⟩ := c'
  simp only [chanCode, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hf⟩ := h
  have : f = f' := BitVec.eq_of_toNat_eq hf
  subst this
  rfl

/-- An informer's ghost names and locations as numbers, locations and a function. -/
def InfH.code [GooseExts] (I : InfH) :
    (Loc × Loc × GoFunc) × (List Nat × List Nat) × (Loc × Loc) × List Nat :=
  ((I.ca, I.ts, I.kf),
   ([I.γf.st, I.γf.tok, I.γf.sy, I.γf.ex, I.γt.st, I.γt.ph], chanCode I.γf.ch),
   (I.γt.idx, I.γt.im),
   [I.γi.reg, I.γi.last, I.γi.pop, I.γi.sw, I.γi.rvlb, I.γi.first, I.γi.ix])

theorem InfH.code_inj [GooseExts] {I I' : InfH} (h : I.code = I'.code) : I = I' := by
  obtain ⟨ca, ts, kf, ⟨fst, ftok, fsy, fex, fch⟩, ⟨tst, tph, tidx, tim⟩,
    ⟨r1, r2, r3, r4, r5, r6, r7⟩⟩ := I
  obtain ⟨ca', ts', kf', ⟨fst', ftok', fsy', fex', fch'⟩, ⟨tst', tph', tidx', tim'⟩,
    ⟨r1', r2', r3', r4', r5', r6', r7'⟩⟩ := I'
  simp only [InfH.code, Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hch⟩, ⟨rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ := h
  rw [chanCode_inj hch]

instance InfH.countable [GooseExts] : Pos.Countable InfH :=
  .ofInjective (fun I => Pos.Countable.encode I.code)
    (by intro a b h; rw [Pos.encode_eq_iff] at h; exact InfH.code_inj h)

/-! ### The events' facts -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **The informer's store and invariant** (persistent): see the file header. -/
def infView (γa : ApiNames) (r : Res) (I : InfH) (Fam : Nat → Fn GF) : IProp GF :=
  iprop(isCache I.ca I.ts I.γt (infObj I.γi r) Fam I.kf ∗ infInv γa r I.γf I.γt I.γi)

instance infView_persistent (γa : ApiNames) (r : Res) (I : InfH) (Fam : Nat → Fn GF) :
    Persistent (infView γa r I Fam) := by
  unfold infView; infer_instance

/-- **The store's index `n` is relation `Fam j`**, for good (persistent). -/
def infIdx (I : InfH) (n : GoString) (j : Nat) : IProp GF := n ↪[I.γi.ix]□ j

instance infIdx_persistent (I : InfH) (n : GoString) (j : Nat) :
    Persistent (infIdx (GF := GF) I n j) := by
  unfold infIdx; infer_instance

open Iris.ProofMode in
/-- An index name has one relation. -/
theorem infIdx_agree (I : InfH) (n : GoString) (j j' : Nat) :
    infIdx (GF := GF) I n j ∗ infIdx I n j' ⊢ ⌜j = j'⌝ := by
  iintro ⟨H1, H2⟩
  unfold infIdx
  iapply (ghostMapElem_agree n I.γi.ix DFrac.discard DFrac.discard j j') $$ H1 H2

/-- **`x` is registered with the model object `o` of resource `r`** (persistent). -/
def infObjIs (γi : InfNames) (r : Res) (x : GoInterface) (o : Obj) : IProp GF :=
  iprop(x ↪[γi.reg]□ o ∗ □ apimodel.objAt x DFrac.discard o ∗ ⌜o.res = r⌝)

instance infObjIs_persistent (γi : InfNames) (r : Res) (x : GoInterface) (o : Obj) :
    Persistent (infObjIs (GF := GF) γi r x o) := by
  unfold infObjIs; infer_instance

theorem infObj_iff (γi : InfNames) (r : Res) (x : GoInterface) :
    infObj (GF := GF) γi r x ⊣⊢ ∃ o, infObjIs γi r x o := by
  unfold infObj infObjIs; exact .rfl

open Iris.ProofMode in
/-- A registered object has one model object. -/
theorem infObjIs_agree (γi : InfNames) (r : Res) (x : GoInterface) (o o' : Obj) :
    infObjIs (GF := GF) γi r x o ∗ infObjIs γi r x o' ⊢ ⌜o = o'⌝ := by
  unfold infObjIs
  iintro ⟨⟨H1, -, -⟩, ⟨H2, -, -⟩⟩
  iapply (ghostMapElem_agree x γi.reg DFrac.discard DFrac.discard o o') $$ H1 H2

/-- **`o` is in the server's log**: at its key in the table of some version `v` of a past state's
log (persistent). -/
def inLog (γa : ApiNames) (r : Res) (o : Obj) : IProp GF :=
  iprop(∃ (σp : apimodel.St) (v : Nat), pastSt γa σp ∗
    ⌜tableAt (σp.tbl r).log v !! o.key = some o⌝)

instance inLog_persistent (γa : ApiNames) (r : Res) (o : Obj) :
    Persistent (inLog (GF := GF) γa r o) := by
  unfold inLog; infer_instance

/-- **`o`'s key is gone after `o`**: absent from the table of some version `v` of a past state's
log, `o`'s own version at most `v` (persistent). -/
def goneAfter (γa : ApiNames) (r : Res) (o : Obj) : IProp GF :=
  iprop(∃ (σp : apimodel.St) (v : Nat) (n : w64), pastSt γa σp ∗
    ⌜tableAt (σp.tbl r).log v !! o.key = none ∧ o.meta.ResourceVersion' = rvStr n ∧
      n.toNat ≤ v⌝)

instance goneAfter_persistent (γa : ApiNames) (r : Res) (o : Obj) :
    Persistent (goneAfter (GF := GF) γa r o) := by
  unfold goneAfter; infer_instance

/-- **What a handler is told with each event** (persistent): see the file header. -/
def evFacts (γa : ApiNames) (r : Res) (γi : InfNames) : Ev → IProp GF
  | .add x _ => iprop(∃ o, infObjIs γi r x o ∗ inLog γa r o)
  | .update old new => iprop(∃ (oo on : Obj), infObjIs γi r old oo ∗ infObjIs γi r new on ∗
      ∃ (σp : apimodel.St) (u v : Nat), pastSt γa σp ∗
        ⌜oo.key = on.key ∧ u ≤ v ∧ tableAt (σp.tbl r).log u !! oo.key = some oo ∧
          tableAt (σp.tbl r).log v !! on.key = some on⌝)
  | .delete x => iprop(∃ (y : GoInterface) (o : Obj),
      ⌜x = y ∨ ∃ k, x = tombstone k y⌝ ∗ infObjIs γi r y o ∗ goneAfter γa r o)

instance evFacts_persistent (γa : ApiNames) (r : Res) (γi : InfNames) (e : Ev) :
    Persistent (evFacts (GF := GF) γa r γi e) := by
  cases e <;> unfold evFacts <;> infer_instance

/-- **The handler contract** (persistent): `h`'s `OnAdd`/`OnUpdate`/`OnDelete` take each event,
with its facts, from the registering code's `H evs` to `H (evs ++ [e])`. -/
def handlerSpec (γa : ApiNames) (r : Res) (γi : InfNames) (h : GoInterface)
    (H : List Ev → IProp GF) : IProp GF :=
  lhOk h H (fun _ e => evFacts γa r γi e)

instance handlerSpec_persistent (γa : ApiNames) (r : Res) (γi : InfNames) (h : GoInterface)
    (H : List Ev → IProp GF) : Persistent (handlerSpec γa r γi h H) := by
  unfold handlerSpec; infer_instance

/-- **An `InformerSynced` function** (persistent): `f()` returns, `true` with the first list in the
store (`syncedFacts`). -/
def syncedFn (f : GoFunc) (γi : InfNames) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ b : Bool, syncedFacts γi b -∗ Φ #b) -∗
    WP (App (Val #f) (Val #())) {{ Φ }})

instance syncedFn_persistent (f : GoFunc) (γi : InfNames) :
    Persistent (syncedFn (GF := GF) f γi) := by
  unfold syncedFn; infer_instance

/-- **Handler options as the controller passes them**: no resync period (scope, see the file
header), a logger read-only or none. -/
def handlerOptsOk (opts : HandlerOptions) : IProp GF :=
  iprop(⌜opts.ResyncPeriod' = null⌝ ∗
    (⌜opts.Logger' = null⌝ ∨ ∃ lg : github_com.go_logr.logr.Logger, opts.Logger' ↦□ lg))

instance handlerOptsOk_persistent (opts : HandlerOptions) :
    Persistent (handlerOptsOk (GF := GF) opts) := by
  unfold handlerOptsOk; infer_instance

/-- The informers' reader pools' namespace. -/
def infPoolN : Namespace := nroot.@"informer.readers"

/-- **The store's reader slots, for any thread** (persistent): under the adequacy theorem's thread
bound, a pool of the store lock's reader slots (`tsReader`), which a thread borrows with its thread
token (`threadPool.borrow`) for a read and gives back (`threadPool.giveBack`); the owner's pattern
of `notes/bounds-plan.md` (the lessor's `slotsPool`). -/
def infReaders (I : InfH) (r : Res) (Fam : Nat → Fn GF) : IProp GF :=
  iprop(□ (⌜threadBound GF ≤ 2 ^ 30 - 1⌝ → ∃ γp : GName,
    threadPool.isThreadPool infPoolN γp (tsReader I.ts I.γt (infObj I.γi r) Fam)))

instance infReaders_persistent (I : InfH) (r : Res) (Fam : Nat → Fn GF) :
    Persistent (infReaders (GF := GF) I r Fam) := by
  unfold infReaders; infer_instance

/-- The store as an interface value (`GetStore()`'s and `GetIndexer()`'s result). -/
def storeVal (I : InfH) : GoInterface :=
  interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #I.ca

/-- **The informer as an interface value** (persistent): see the file header. -/
def isInformer (x : GoInterface) (γa : ApiNames) (r : Res) (I : InfH) (Fam : Nat → Fn GF) :
    IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜x = interface.ok i⌝ ∗ infView γa r I Fam ∗ infReaders I r Fam ∗
    -- `GetStore()`, `GetIndexer()`: the store
    □ (∀ Φ : val → IProp GF, ▷ Φ #(storeVal I) -∗
        WP (App (Val #(methods i.ty go!"GetStore" i.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF, ▷ Φ #(storeVal I) -∗
        WP (App (Val #(methods i.ty go!"GetIndexer" i.v)) (Val #())) {{ Φ }}) ∗
    -- `HasSynced`, called or as a method value
    syncedFn (methods i.ty go!"HasSynced" i.v) I.γi ∗
    -- `AddEventHandlerWithOptions(h, opts)`: the handler registered (its listener gets `H []`);
    -- an error only once the informer has stopped, `H []` given back
    □ (∀ (h : GoInterface) (opts : HandlerOptions) (H : List Ev → IProp GF)
        (Φ : val → IProp GF),
        handlerSpec γa r I.γi h H -∗ handlerOptsOk opts -∗ H [] -∗
        ▷ (∀ (reg err : GoInterface),
            (⌜err = interface.nil⌝ ∨ (⌜err ≠ interface.nil⌝ ∗ H [])) -∗ Φ (PairV #reg #err)) -∗
        WP (App (App (Val #(methods i.ty go!"AddEventHandlerWithOptions" i.v)) (Val #h))
          (Val #opts)) {{ Φ }}) ∗
    -- `AddIndexers(m)`: the indexers `nfv` (relations `Fam (nids n)`): on success each registered
    -- for good; an error (a name already registered, or the informer stopped) changes nothing
    □ (∀ (nm : Loc) (dn : DFrac) (nfv : GMap GoString GoFunc) (nids : GMap GoString Nat)
        (Φ : val → IProp GF),
        ⌜GMap.size nfv ≤ 2 ^ 62⌝ -∗ nm ↦${dn} nfv -∗
        fnsOk (infObj I.γi r) nfv (GMap.fmap Fam nids) -∗
        ▷ (∀ (err : GoInterface), nm ↦${dn} nfv -∗
            (⌜err ≠ interface.nil⌝ ∨
              (⌜err = interface.nil⌝ ∗ [∗map] n ↦ j ∈ nids, infIdx I n j)) -∗ Φ #err) -∗
        WP (App (Val #(methods i.ty go!"AddIndexers" i.v)) (Val #nm)) {{ Φ }}))

instance isInformer_persistent (x : GoInterface) (γa : ApiNames) (r : Res) (I : InfH)
    (Fam : Nat → Fn GF) : Persistent (isInformer x γa r I Fam) := by
  unfold isInformer; infer_instance

open Iris.ProofMode in
/-- **The store and invariant of an informer** (the controller's `infAt`). -/
theorem isInformer_view (x : GoInterface) (γa : ApiNames) (r : Res) (I : InfH)
    (Fam : Nat → Fn GF) : isInformer x γa r I Fam ⊢ infView γa r I Fam := by
  unfold isInformer
  iintro ⟨%i, -, #Hv, -⟩
  iexact Hv

open Iris.ProofMode in
/-- **The store's reader pool of an informer.** -/
theorem isInformer_readers (x : GoInterface) (γa : ApiNames) (r : Res) (I : InfH)
    (Fam : Nat → Fn GF) : isInformer x γa r I Fam ⊢ infReaders I r Fam := by
  unfold isInformer
  iintro ⟨%i, -, -, #Hr, -⟩
  iexact Hr

end defs

section run
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **The informer runs** (persistent; the factory's `Start` runs it on a goroutine of its own):
`x.RunWithContext(ctx)` under a context whose `Done()` is one channel, returning (once the context
is done). Not a client's concern: the factory holds it (`informers.facLocked`). -/
def infRunOk (x : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜x = interface.ok i⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (ch : GoChan)
        (γch : ChanNames) (Φ : val → IProp GF),
        context.isContext ctx cs -∗ stableCtx ctx ch γch -∗ ▷ Φ #() -∗
        WP (App (Val #(methods i.ty go!"RunWithContext" i.v)) (Val #(GoInterface.ok ctx)))
          {{ Φ }}))

instance infRunOk_persistent (x : GoInterface) : Persistent (infRunOk (GF := GF) x) := by
  unfold infRunOk; infer_instance

end run

end informer
end EtcdGrove
end Perennial
