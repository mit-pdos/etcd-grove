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
* **Index relations by name** (review 1's M1): a client gives the relation of each index name,
  `FamN : GoString → Fn GF`; the store's (numbered) family is `famOf FamN`, the name `n` at id
  `idxId n` (`famOf_idxId`). `infIdx I n` (persistent): the store's index named `n` is registered,
  for good (an index is never removed; `AddIndexers` adds): a store read through the invariant sees
  `σs.fnIds !! n = some (idxId n)` (`InformerAlloc.lean`, `infInv_readIdxAU`), so the index
  computes `FamN n`, whoever registered it. `idxFnsOk OK FamN nfv`: the indexers `nfv` compute
  their names' relations.
* `infObjIs γi r x o`: the Go object `x` is registered with the model object `o` of resource `r`
  (owned read-only, `objAt x DFrac.discard o`); `infObj γi r x` is `∃ o, infObjIs γi r x o`.
* **The handler contract** `handlerSpec γa r γi h H`: the handler `h` (a `ResourceEventHandler`)
  takes each event `e` it is called with, with the event's facts `evFacts γa r γi e`, from the
  registering code's resource `H evs` (the events delivered so far, on the listener's goroutine) to
  `H (evs ++ [e])`, borrowing the listener goroutine's thread token (`lhOk`, the listener's
  contract, at `Q _ e := evFacts …`). The facts
  (`evFacts`), all persistent:
  - `OnAdd(x, _)`: `x` registered with `o`, which is at its key in the log's table at some version
    of a past state (`inLog`);
  - `OnUpdate(old, cur)`: both registered (`oo`, `on`), of one key, `oo` in the table at a version
    `u`, `on` at a version `v ≥ u` (so a UID changes only across a deletion);
  - `OnDelete(x)`: `x` is a registered object `y`, or the tombstone `DeletedFinalStateUnknown{k, y}`
    of one, and `y`'s key is absent from the table at some version `v` of a past state, `y`'s own
    version at most `v` (`goneAfter`: the deletion is in the log, from `v` on the object is gone),
    and `y` is the object of a change of the log (`seen`: a version the server stored, so its UID
    was at its key; review 1's H4). The add and update facts give `seen` too (`inLog_seen`).
* `syncedFn f γi` (persistent): the function `f` (an `InformerSynced`, the informer's `HasSynced`
  method value) returns a boolean, `true` with `syncedFacts γi true` (the first list's version `v`,
  `infFirst`, and the store's version at least `v` from then on, `infRvLb`).
* `infReaders I r Fam` (persistent): the store's reader slots in a thread pool (under the thread
  bound), borrowed with a thread token: what a reading thread (a worker, a handler) uses.
* **The not-started token** (the run's decision R6): a `Bool` ghost variable `γi.ns`, `false` until
  the informer starts. Its halves: the start lock's (`nsLock γ started`, in `SIIAt.siiLocked`, kept
  equal to the `started` field) and the callers' (`notStartedAt γ q`, fraction `q` of it, split
  among them; `infNotStarted γi q` for the informer's). A fraction says the informer has not
  started (`nsLock_agree`); the whole callers' half lets the start flip it (`nsLock_start`). The
  informer's creator chooses the name (`nsAlloc`): the factory preallocates one per resource and
  hands the callers' halves out at its construction (`informers.facNotStarted`).
* `isInformer x γa r I Fam` (persistent): **the informer as an interface value** (a
  `SharedIndexInformer`, whatever wrapper `x` is: `Informer()` returns a `*typedSharedIndexInformer`
  around the factory's): `infView`, `infReaders`, and the contracts of the methods the controller calls on it
  (`GetStore`, `GetIndexer`, `HasSynced` called and as a method value, `AddEventHandlerWithOptions`,
  `AddIndexers`), and the store's `LastStoreSyncResourceVersion` (a consistency store's getter:
  a version the store has reached for good, `infRvLb`, well formed or empty; the `AtomicFIFO` gate
  it reads is the informer's, review 1's H3). `AddEventHandlerWithOptions` and `AddIndexers` are specified **before the informer's start only** (decision R6, the
  controller's use): each borrows a fraction of the not-started token. **The handler contract is
  deferred** (decision R7): `AddEventHandlerWithOptions` takes no contract; it turns the fraction
  into `handlerPending γa r γi q h H`, which gives the fraction back only once activated with the
  handler's contract (`handlerPending_activate`), so a handler's contract may be proved after its
  registration (its closures may read what is stored later) but before the start
  (`handlerCell_started`). In Go both also work after
  the start (a handler registered late gets the store's items as initial adds; `AddIndexers`
  re-indexes the store, refused only once the informer has stopped): the restriction is the spec's.
* `infRunOk x γi` (persistent): `x.RunWithContext(ctx)` runs the informer, given the whole callers'
  half of the not-started token (the factory's `Start` calls it).

Scope (marked): the informers of the run's model API server (`apimodel`: `ApiNames`, its four
resources `Res`, its history's logs, its clientset), not of a real API server (review 1's M5).
Handlers without a resync period (`HandlerOptions.ResyncPeriod` `nil`, and the
factory's default resync `0`): a resyncing handler's synthetic updates are not covered.
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefInf
public import Proof.k8s_io.client_go.tools.cache.ListenerDefs
public import Proof.k8s_io.client_go.tools.cache.RefCtx
public import Perennial.Proof.ThreadPool
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Reader
public import Proof.k8s_io.apimachinery.pkg.util.resourceversion.Defs

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
   [I.γi.reg, I.γi.last, I.γi.pop, I.γi.sw, I.γi.rvlb, I.γi.first, I.γi.ix, I.γi.ns])

theorem InfH.code_inj [GooseExts] {I I' : InfH} (h : I.code = I'.code) : I = I' := by
  obtain ⟨ca, ts, kf, ⟨fst, ftok, fsy, fex, fch⟩, ⟨tst, tph, tidx, tim⟩,
    ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩⟩ := I
  obtain ⟨ca', ts', kf', ⟨fst', ftok', fsy', fex', fch'⟩, ⟨tst', tph', tidx', tim'⟩,
    ⟨r1', r2', r3', r4', r5', r6', r7', r8'⟩⟩ := I'
  simp only [InfH.code, Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hch⟩, ⟨rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ := h
  rw [chanCode_inj hch]

instance InfH.countable [GooseExts] : Pos.Countable InfH :=
  .ofInjective (fun I => Pos.Countable.encode I.code)
    (by intro a b h; rw [Pos.encode_eq_iff] at h; exact InfH.code_inj h)

/-! ### The not-started token -/

section token
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The not-started token's start-lock half**, at `b` (the `started` field). -/
def nsLock (γ : GName) (b : Bool) : IProp GF := ghostVar γ (1 : Qp).half b

instance nsLock_timeless (γ : GName) (b : Bool) : Timeless (nsLock (GF := GF) γ b) := by
  unfold nsLock; infer_instance

/-- **Fraction `q` of the not-started token's callers' half**: the informer has not started. -/
def notStartedAt (γ : GName) (q : Qp) : IProp GF := ghostVar γ q.half false

instance notStartedAt_timeless (γ : GName) (q : Qp) : Timeless (notStartedAt (GF := GF) γ q) := by
  unfold notStartedAt; infer_instance

instance notStartedAt_fractional (γ : GName) : Fractional (notStartedAt (GF := GF) γ) := by
  unfold notStartedAt; exact ghostVar_half_fractional γ false

/-- **The informer has not started** (fraction `q` of the callers' half of its token). -/
def infNotStarted (γi : InfNames) (q : Qp) : IProp GF := notStartedAt γi.ns q

instance infNotStarted_timeless (γi : InfNames) (q : Qp) :
    Timeless (infNotStarted (GF := GF) γi q) := by
  unfold infNotStarted; infer_instance

instance infNotStarted_fractional (γi : InfNames) : Fractional (infNotStarted (GF := GF) γi) := by
  unfold infNotStarted; exact notStartedAt_fractional γi.ns

open Iris.ProofMode in
/-- **A not-started token, allocated**: the start lock's half and the whole callers' half. -/
theorem nsAlloc : ⊢ |==> ∃ γ : GName, nsLock (GF := GF) γ false ∗ notStartedAt γ 1 := by
  imod (ghostVar_alloc (GF := GF) false) with ⟨%γ, H⟩
  ihave ⟨H1, H2⟩ := (ghostVar_split_half γ 1 false).1 $$ H
  imodintro
  iexists γ
  unfold nsLock notStartedAt
  iframe

open Iris.ProofMode in
/-- **The callers' fraction says the informer has not started.** -/
theorem nsLock_agree (γ : GName) (b : Bool) (q : Qp) :
    nsLock (GF := GF) γ b ∗ notStartedAt γ q ⊢ ⌜b = false⌝ := by
  unfold nsLock notStartedAt
  iintro ⟨H1, H2⟩
  iapply (ghostVar_agree γ b (1 : Qp).half false q.half) $$ H1 H2

open Iris.ProofMode in
/-- **The start**: with the whole callers' half, the start lock's half flips to `true` (the
callers' half is used up). -/
theorem nsLock_start (γ : GName) (b : Bool) :
    nsLock (GF := GF) γ b ∗ notStartedAt γ 1 ⊢ |==> nsLock γ true := by
  unfold nsLock notStartedAt
  iintro ⟨H1, H2⟩
  imod (ghostVar_update_halves true γ b false) $$ H1 H2 with ⟨H1, -⟩
  imodintro
  iexact H1

end token

/-! ### Index relations by name -/

section names
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An index name's relation id in the store's family** (an injective code: client-go's index
names are a global convention, the store's family is keyed by them). -/
def idxId (n : GoString) : Nat := (Pos.Countable.encode n).toNat

theorem idxId_inj {a b : GoString} (h : idxId a = idxId b) : a = b :=
  Pos.encode_eq_iff.1 (Pos.Pos_toNat_inj h)

open Classical in
/-- **The store's family of a family of relations by index name** (`FamN n` at `idxId n`). -/
def famOf (FamN : GoString → Fn GF) : Nat → Fn GF :=
  fun j => if h : ∃ n, idxId n = j then FamN (Classical.choose h) else fun _ _ => iprop(False)

theorem famOf_idxId (FamN : GoString → Fn GF) (n : GoString) : famOf FamN (idxId n) = FamN n := by
  unfold famOf
  have h : ∃ n', idxId n' = idxId n := ⟨n, rfl⟩
  rw [dite_cond_eq_true (eq_true h), idxId_inj (Classical.choose_spec h)]

end names

/-! ### The log's objects -/

section log
variable [GooseExts]

/-- The objects of the log's tables meet what the log's changes meet. -/
theorem replay_prop (P : Obj → Prop) : ∀ (l : List Change) (M : GMap Key Obj),
    (∀ key o, M !! key = some o → P o) → (∀ c ∈ l, P c.obj) →
    ∀ key o, (l.foldl applyChange M) !! key = some o → P o
  | [], M, h, _ => h
  | c :: l, M, h, hl => by
    simp only [List.foldl_cons]
    apply replay_prop P l
    · intro key o hk
      unfold applyChange at hk
      cases ht : c.typ with
      | deleted =>
        rw [ht, GMap.lookup_delete_iff] at hk
        split at hk
        · cases hk
        · exact h key o hk
      | added | modified =>
        rw [ht, GMap.lookup_insert_eq_iff] at hk
        split at hk
        · simp only [Option.some.injEq] at hk; subst hk; exact hl c List.mem_cons_self
        · exact h key o hk
    · exact fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')

/-- **An object of a table of the log is the object of a change of the log.** -/
theorem tableAt_seen (l : List Change) (v : Nat) (key : Key) (o : Obj)
    (h : tableAt l v !! key = some o) : ∃ ch ∈ l, ch.obj = o := by
  refine replay_prop (fun o => ∃ ch ∈ l, ch.obj = o) (l.filter (fun c => decide (c.rv.toNat ≤ v)))
    ∅ (by intro key o h; simp at h) ?_ key o h
  intro c hc
  exact ⟨c, (List.mem_filter.1 hc).1, rfl⟩

end log

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

/-- **The store's index named `n` is registered**, for good (persistent): with the store's
relation id of its name (`idxId n`), so its relation is the client's `FamN n` (`famOf_idxId`). -/
def infIdx (I : InfH) (n : GoString) : IProp GF := n ↪[I.γi.ix]□ idxId n

instance infIdx_persistent (I : InfH) (n : GoString) : Persistent (infIdx (GF := GF) I n) := by
  unfold infIdx; infer_instance

/-- **The indexers `nfv` compute their names' relations** (persistent): each function `f` of name
`n` meets `FamN n` on the informer's objects `OK`. -/
def idxFnsOk (OK : GoInterface → IProp GF) (FamN : GoString → Fn GF)
    (nfv : GMap GoString GoFunc) : IProp GF :=
  iprop([∗map] n ↦ f ∈ nfv, fnOk OK f (FamN n))

instance idxFnsOk_persistent (OK : GoInterface → IProp GF) (FamN : GoString → Fn GF)
    (nfv : GMap GoString GoFunc) : Persistent (idxFnsOk OK FamN nfv) := by
  unfold idxFnsOk; infer_instance

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

/-- **`o` is the object of a change of the server's log** (of a past state; persistent): a version
the server stored (so its UID was at its key from that change's version). -/
def seen (γa : ApiNames) (r : Res) (o : Obj) : IProp GF :=
  iprop(∃ σp : apimodel.St, pastSt γa σp ∗ ⌜∃ ch ∈ (σp.tbl r).log, ch.obj = o⌝)

instance seen_persistent (γa : ApiNames) (r : Res) (o : Obj) :
    Persistent (seen (GF := GF) γa r o) := by
  unfold seen; infer_instance

open Iris.ProofMode in
/-- **An object in a table of the log is the object of a change of the log.** -/
theorem inLog_seen (γa : ApiNames) (r : Res) (o : Obj) : inLog (GF := GF) γa r o ⊢ seen γa r o := by
  unfold inLog seen
  iintro ⟨%σp, %v, #Hp, %h⟩
  iexists σp
  iframe #
  ipureintro
  exact tableAt_seen _ v o.key o h

/-- **What a handler is told with each event** (persistent): see the file header. -/
def evFacts (γa : ApiNames) (r : Res) (γi : InfNames) : Ev → IProp GF
  | .add x _ => iprop(∃ o, infObjIs γi r x o ∗ inLog γa r o)
  | .update old new => iprop(∃ (oo on : Obj), infObjIs γi r old oo ∗ infObjIs γi r new on ∗
      ∃ (σp : apimodel.St) (u v : Nat), pastSt γa σp ∗
        ⌜oo.key = on.key ∧ u ≤ v ∧ tableAt (σp.tbl r).log u !! oo.key = some oo ∧
          tableAt (σp.tbl r).log v !! on.key = some on⌝)
  | .delete x => iprop(∃ (y : GoInterface) (o : Obj),
      ⌜x = y ∨ ∃ k, x = tombstone k y⌝ ∗ infObjIs γi r y o ∗ goneAfter γa r o ∗ seen γa r o)

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

/-- The handlers' contract cells' namespace. -/
def lsnN : Namespace := nroot.@"informer.handler"

/-- **A registered handler's contract cell** `γc`: pending (its flag `false`, holding the
not-started fraction `q` its registration took), or active (flag `true`, the handler's contract). -/
def handlerCell (γa : ApiNames) (r : Res) (γi : InfNames) (γc : GName) (q : Qp) (h : GoInterface)
    (H : List Ev → IProp GF) : IProp GF :=
  iprop((ghostVar γc (1 : Qp).half false ∗ infNotStarted γi q) ∨
    (ghostVar γc (1 : Qp).half true ∗ handlerSpec γa r γi h H))

/-- **A handler registered, its contract pending** (`AddEventHandlerWithOptions`' result): its
cell, and the cell's other flag half. It holds the fraction `q` of the not-started token, which only
its activation (`handlerPending_activate`, with the contract) gives back: so every handler
registered is active before the informer starts (`RunWithContext` needs the whole token,
`handlerCell_started`). -/
def handlerPending (γa : ApiNames) (r : Res) (γi : InfNames) (q : Qp) (h : GoInterface)
    (H : List Ev → IProp GF) : IProp GF :=
  iprop(∃ γc : GName, inv lsnN (handlerCell γa r γi γc q h H) ∗ ghostVar γc (1 : Qp).half false)

open Iris.ProofMode in
/-- **A pending handler activated** with its contract: the not-started fraction back. -/
theorem handlerPending_activate (γa : ApiNames) (r : Res) (γi : InfNames) (q : Qp)
    (h : GoInterface) (H : List Ev → IProp GF) :
    handlerPending γa r γi q h H ∗ handlerSpec γa r γi h H ⊢ |={⊤}=> infNotStarted γi q := by
  unfold handlerPending
  iintro ⟨⟨%γc, #Hinv, Hc⟩, #Hspec⟩
  iinv Hinv with Hcell Hclose
  iunfold handlerCell at Hcell
  icases Hcell with (⟨>Hc', >Hns⟩ | ⟨>Hc', -⟩)
  · imod (ghostVar_update_halves true γc false false) $$ Hc Hc' with ⟨-, Hc'⟩
    imod Hclose $$ [Hc'] with -
    · inext; iunfold handlerCell; iright; iframe; iexact Hspec
    imodintro
    iexact Hns
  · icombine Hc Hc' gives % ⟨_, hb⟩
    cases hb

open Iris.ProofMode in
/-- **At the start every registered handler is active**: with the start lock's half and the whole
callers' half of the not-started token, a handler's cell holds its contract. -/
theorem handlerCell_started (γa : ApiNames) (r : Res) (γi : InfNames) (γc : GName) (q : Qp)
    (h : GoInterface) (H : List Ev → IProp GF) (b : Bool) :
    inv lsnN (handlerCell γa r γi γc q h H) ∗ nsLock γi.ns b ∗ infNotStarted γi 1 ⊢
      |={⊤}=> nsLock γi.ns b ∗ infNotStarted γi 1 ∗ ▷ handlerSpec γa r γi h H := by
  iintro ⟨#Hinv, Hl, Hn⟩
  iinv Hinv with Hcell Hclose
  iunfold handlerCell at Hcell
  icases Hcell with (⟨>Hc, >Hq⟩ | ⟨Hc, #Hspec⟩)
  · unfold nsLock infNotStarted notStartedAt
    icombine Hl Hn gives % ⟨_, hb⟩
    subst hb
    ihave Hw := (ghostVar_split_half γi.ns 1 false).2 $$ [Hl Hn]
    · iframe
    icombine Hw Hq gives % ⟨hq, -⟩
    exact absurd hq (Qp_one_add_not_le _)
  · imod Hclose $$ [Hc] with -
    · inext; iunfold handlerCell; iright; iframe; iexact Hspec
    imodintro
    iframe
    iexact Hspec

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
def isInformer (x : GoInterface) (γa : ApiNames) (r : Res) (I : InfH) (FamN : GoString → Fn GF) :
    IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜x = interface.ok i⌝ ∗ infView γa r I (famOf FamN) ∗
    infReaders I r (famOf FamN) ∗
    -- `GetStore()`, `GetIndexer()`: the store
    □ (∀ Φ : val → IProp GF, ▷ Φ #(storeVal I) -∗
        WP (App (Val #(methods i.ty go!"GetStore" i.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF, ▷ Φ #(storeVal I) -∗
        WP (App (Val #(methods i.ty go!"GetIndexer" i.v)) (Val #())) {{ Φ }}) ∗
    -- `HasSynced`, called or as a method value
    syncedFn (methods i.ty go!"HasSynced" i.v) I.γi ∗
    -- `AddEventHandlerWithOptions(h, opts)`, before the start: the handler registered (its
    -- listener gets `H []`, and every event from the first), no error; its contract pending
    -- (`handlerPending`, holding the fraction `q` until activated with the contract)
    □ (∀ (q : Qp) (h : GoInterface) (opts : HandlerOptions) (H : List Ev → IProp GF)
        (Φ : val → IProp GF),
        infNotStarted I.γi q -∗ handlerOptsOk opts -∗ H [] -∗
        ▷ (∀ (reg : GoInterface), handlerPending γa r I.γi q h H -∗
            Φ (PairV #reg #(interface.nil : GoInterface))) -∗
        WP (App (App (Val #(methods i.ty go!"AddEventHandlerWithOptions" i.v)) (Val #h))
          (Val #opts)) {{ Φ }}) ∗
    -- `AddIndexers(m)`, before the start: the indexers `nfv`, each computing its name's relation
    -- (`FamN n`): on success each registered for good; Go refuses the whole map if one of its
    -- names is already registered (`storeIndex.addIndexers`, nothing added): then that name is
    -- (with its relation, by name)
    □ (∀ (q : Qp) (nm : Loc) (dn : DFrac) (nfv : GMap GoString GoFunc) (Φ : val → IProp GF),
        infNotStarted I.γi q -∗ ⌜GMap.size nfv ≤ 2 ^ 62⌝ -∗ nm ↦${dn} nfv -∗
        idxFnsOk (infObj I.γi r) FamN nfv -∗
        ▷ (∀ (err : GoInterface), infNotStarted I.γi q -∗ nm ↦${dn} nfv -∗
            ((⌜err ≠ interface.nil⌝ ∗ ∃ n, ⌜n ∈ nfv⌝ ∗ infIdx I n) ∨
              (⌜err = interface.nil⌝ ∗ [∗map] n ↦ _f ∈ nfv, infIdx I n)) -∗ Φ #err) -∗
        WP (App (Val #(methods i.ty go!"AddIndexers" i.v)) (Val #nm)) {{ Φ }}) ∗
    -- the store's `LastStoreSyncResourceVersion()` (a consistency store's getter, the
    -- `AtomicFIFO` gate on): a version the store has reached for good, well formed or empty
    □ (∀ Φ : val → IProp GF,
        ▷ (∀ rv : GoString, ⌜rv = [] ∨ resourceversion.wellFormed rv = true⌝ -∗
            infRvLb I.γi (resourceversion.decVal rv) -∗ Φ #rv) -∗
        WP (App (Val #(methods (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty)
          go!"LastStoreSyncResourceVersion" #I.ca)) (Val #())) {{ Φ }}))

instance isInformer_persistent (x : GoInterface) (γa : ApiNames) (r : Res) (I : InfH)
    (FamN : GoString → Fn GF) : Persistent (isInformer x γa r I FamN) := by
  unfold isInformer; infer_instance

open Iris.ProofMode in
/-- **The store and invariant of an informer** (the controller's `infAt`). -/
theorem isInformer_view (x : GoInterface) (γa : ApiNames) (r : Res) (I : InfH)
    (FamN : GoString → Fn GF) : isInformer x γa r I FamN ⊢ infView γa r I (famOf FamN) := by
  unfold isInformer
  iintro ⟨%i, -, #Hv, -⟩
  iexact Hv

open Iris.ProofMode in
/-- **The store's reader pool of an informer.** -/
theorem isInformer_readers (x : GoInterface) (γa : ApiNames) (r : Res) (I : InfH)
    (FamN : GoString → Fn GF) : isInformer x γa r I FamN ⊢ infReaders I r (famOf FamN) := by
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
`x.RunWithContext(ctx)`, with the whole callers' half of the not-started token (used up), under a
context whose `Done()` is one channel, returning (once the context is done). The factory holds it
(`informers.facLocked`). -/
def infRunOk (x : GoInterface) (γi : InfNames) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜x = interface.ok i⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (ch : GoChan)
        (γch : ChanNames) (Φ : val → IProp GF),
        context.isContext ctx cs -∗ stableCtx ctx ch γch -∗ infNotStarted γi 1 -∗ ▷ Φ #() -∗
        WP (App (Val #(methods i.ty go!"RunWithContext" i.v)) (Val #(GoInterface.ok ctx)))
          {{ Φ }}))

instance infRunOk_persistent (x : GoInterface) (γi : InfNames) :
    Persistent (infRunOk (GF := GF) x γi) := by
  unfold infRunOk; infer_instance

end run

end informer
end EtcdGrove
end Perennial
