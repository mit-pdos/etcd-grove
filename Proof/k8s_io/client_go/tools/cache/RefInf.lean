/-
**The reflector against the informer's contract** (phase 4 of `notes/k8s-daemonset-plan.md`, fifth
round): what the reflector's specs (`list`, `watch`, `ListAndWatchWithContext`, ...) are stated
with, and the lemmas that connect the model API server's list and watch to the informer invariant's
pushes (`infInv_pushChangeAU`, `infInv_pushBookmarkAU`, `infInv_pushReplaceAU`). Lean-first.

* `reflFixed r f lw et dh` (persistent): the reflector's fields its goroutine only reads, as the
  informer's constructor leaves them in `Main`: the store the FIFO `f`, the list-watch `lw`, the
  expected type `et`, no expected GVK, resync period `0`, watch-list off, a real clock, the
  backoff `dh` (`delayOk`: it returns a duration).
* `reflSt r γi n`: the reflector's goroutine's own state: its last synced version and flag
  (`reflOwn`), `paginatedResult`, and the informer invariant's other half of the reflector's last
  version, `n` (`reflLast`), the Go string the decimal of `n` (`rvRel`), positive.
* `lwOk lw γa cfg res` (persistent): the list-watch lists and watches resource `res` of the model
  API server, all namespaces, as its typed clients do (`typedListRet`, `watchRet`), every error
  printable (`fmt.argOk`). In `Main` the typed informers' list-watch closures do (gap D2: their
  constructors are names-only), so for `Main` this is a named hypothesis of the construction.
* `keysOk γa` (persistent): every state the server reaches has keys without a slash (the store's
  key strings are injective on them, `keyGood`; the informer invariant keeps it). A property of
  `Main`'s writers (the names it creates), for the controller's proof to discharge.
* `curOk res p σ`: the watch's cursor `p` (log index, version) is where `logStart` puts the version
  in `σ`'s log, the version at most `σ`'s.
* `wL`, `wC`: the watch loop's state between events (`L`) and between an event's push and its
  callback (`C`), for `handleAnyWatch`'s hypothesis; `watch_evStepOk` proves its per-event step from
  the informer invariant.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerGlue
public import Proof.k8s_io.client_go.tools.cache.RefDefs
public import Proof.k8s_io.client_go.tools.cache.RefWatchDefs
public import Spec.fmt.Errorf
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.WatchLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.WriteLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode apimodel informer k8s_io.client_go.tools.cache

/-! ### The watch's cursor in the log -/

section pure
variable [FfiSyntax]

/-- **The watch's cursor `p`** in `σ`'s log of resource `res`: the first change after its version
`p.2`, which is at most `σ`'s. -/
def curOk (res : Res) (p : Pos') (σ : apimodel.St) : Prop :=
  p.1 = logStart (σ.tbl res).log p.2 ∧ p.2.toNat ≤ σ.rev.toNat

/-- Changes after the version a cursor starts at leave it. -/
theorem logStart_append (l l' : List Change) (n : w64) (h : ∀ d ∈ l', n.toNat < d.rv.toNat) :
    logStart (l ++ l') n = logStart l n := by
  unfold logStart
  induction l with
  | nil =>
    cases l' with
    | nil => rfl
    | cons d l' =>
      have := h d List.mem_cons_self
      simp [show ¬ d.rv.toNat ≤ n.toNat by omega]
  | cons c l ih =>
    by_cases hc : c.rv.toNat ≤ n.toNat
    · simp [hc, ih]
    · simp [hc]

theorem takeWhile_len_le {α : Type} (p : α → Bool) (l : List α) :
    (l.takeWhile p).length ≤ l.length := by
  have := congrArg List.length (List.takeWhile_append_dropWhile (p := p) (l := l))
  rw [List.length_append] at this
  omega

/-- Before the cursor, every change is at most its version. -/
theorem logStart_le (l : List Change) (n : w64) :
    ∀ j, j < logStart l n → ∀ d, l[j]? = some d → d.rv.toNat ≤ n.toNat := by
  unfold logStart
  induction l with
  | nil => intro j hj; simp at hj
  | cons c l ih =>
    intro j hj d hd
    by_cases hc : c.rv.toNat ≤ n.toNat
    · cases j with
      | zero => simp at hd; subst hd; exact hc
      | succ j =>
        have hc' : decide (c.rv.toNat ≤ n.toNat) = true := by simp [hc]
        simp only [List.takeWhile_cons, hc', ite_true, List.length_cons] at hj
        exact ih j (by omega) d (by simpa using hd)
    · have hc' : decide (c.rv.toNat ≤ n.toNat) = false := by simp [hc]
      simp [hc'] at hj

/-- Every change of a well-formed state's log is at most its version, so the cursor at that
version is past them all. -/
theorem logStart_rev (σ : apimodel.St) (hwf : σ.wf) (res : Res) :
    logStart (σ.tbl res).log σ.rev = (σ.tbl res).log.length := by
  have hle : ∀ d ∈ (σ.tbl res).log, d.rv.toNat ≤ σ.rev.toNat := fun d hd => (hwf.log_le res d hd).2
  unfold logStart
  generalize (σ.tbl res).log = l at hle
  induction l with
  | nil => rfl
  | cons d l ih =>
    have hd : decide (d.rv.toNat ≤ σ.rev.toNat) = true := by simp [hle d List.mem_cons_self]
    simp only [List.takeWhile_cons, hd, ite_true, List.length_cons]
    rw [ih (fun e he => hle e (List.mem_cons_of_mem _ he))]

/-- **A cursor stays one in a later state.** -/
theorem curOk_later (res : Res) (p : Pos') (σ σ' : apimodel.St) (hle : apimodel.St.le σ σ') (h : curOk res p σ) :
    curOk res p σ' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hrev, -, hlog⟩ := hle
  obtain ⟨⟨l', hl'⟩, hlater⟩ := hlog res
  refine ⟨?_, by omega⟩
  rw [← hl', logStart_append _ l' p.2 (fun d hd => ?_)]
  · exact h1
  · rw [← hl', List.drop_left] at hlater
    have := hlater d hd
    omega

/-- **An issued version** is the number whose decimal form it is. -/
theorem issuedMap_rvStr (k : Nat) (hk : k < 2 ^ 64) (s : GoString) (n : w64)
    (h : issuedMap k !! s = some n) : s = rvStr n := by
  induction k with
  | zero => simp [issuedMap] at h
  | succ k ih =>
    simp only [issuedMap, GMap.lookup_insert_eq_iff] at h
    split at h
    · rename_i hs; cases h; exact hs.symm
    · exact ih (by omega) h

theorem issued_rvStr (σ : apimodel.St) (w n : w64) (h : σ.issued (rvStr w) = some n) : n = w := by
  have := issuedMap_rvStr σ.rev.toNat (by have := σ.rev.isLt; omega) _ n h
  exact (decStr_inj this).symm

theorem decStr_zero : decStr (W64 0) = go!"0" := by
  rw [decStr_eq, show (W64 0).toNat = 0 from rfl, baseDigits]
  simp [digitChar]

/-- A positive version's decimal form is neither `""` nor `"0"` (a watch from it is not a
"from any version" watch, with synthetic `ADDED` events). -/
theorem rvStr_pos (w : w64) (h : 1 ≤ w.toNat) : rvStr w ≠ go!"" ∧ rvStr w ≠ go!"0" := by
  refine ⟨decStr_ne_nil w, fun he => ?_⟩
  rw [← decStr_zero] at he
  have := decStr_inj he
  subst this
  simp at h

/-- **The cursor a watch from an issued version starts at.** -/
theorem curOk_start (res : Res) (σ : apimodel.St) (n0 : w64) (h : ∃ s, σ.issued s = some n0) :
    curOk res (logStart (σ.tbl res).log n0, n0) σ := by
  obtain ⟨s, hs⟩ := h
  exact ⟨rfl, issuedMap_le σ.rev.toNat s n0 (by have := σ.rev.isLt; omega) hs⟩

/-- **A change step**: the log's entry at the cursor is the next change after its version, and the
cursor after it is the change's. -/
theorem curOk_change (res : Res) (p : Pos') (σ : apimodel.St) (hwf : σ.wf) (c : Change)
    (h : curOk res p σ) (hc : (σ.tbl res).log[p.1]? = some c) :
    NextChange (σ.tbl res).log p.2.toNat c ∧ curOk res (p.1 + 1, c.rv) σ := by
  obtain ⟨h1, -⟩ := h
  have hc' : (σ.tbl res).log[((σ.tbl res).log.takeWhile
      (fun d => decide (d.rv.toNat ≤ p.2.toNat))).length]? = some c := by
    rw [show ((σ.tbl res).log.takeWhile (fun d => decide (d.rv.toNat ≤ p.2.toNat))).length = p.1
      from h1.symm]
    exact hc
  obtain ⟨hn, hlen⟩ := next_logStart _ (hwf.log_sorted res) p.2.toNat c hc'
  refine ⟨hn, ?_, (hwf.log_le res c hn.1).2⟩
  show p.1 + 1 = logStart (σ.tbl res).log c.rv
  unfold logStart at h1 ⊢
  rw [hlen, ← h1]

end pure

/-! ### The reflector's predicates -/

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The list-watch lists and watches resource `res`** of the model API server (persistent): see
the file header. -/
def lwOk (lw : GoInterfaceOk) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res) : IProp GF :=
  iprop(□ (∀ (ctx : GoInterface) (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions)
      (dq : DFrac) (lo : kd.meta.ListOptions) (Φ : val → IProp GF),
      kd.meta.ListOptions.own opts dq lo -∗
      ▷ (∀ (q : Loc) (err : GoInterface) (σ : apimodel.St), kd.meta.ListOptions.own opts dq lo -∗
          typedListRet γa cfg.FailReads' false res go!"" lo σ q err -∗ fmt.argOk err -∗
          Φ (PairV #(interface.mkOk (go.GoType.PointerType (resListTy res)) #q) #err)) -∗
      WP (App (App (Val #(methods lw.ty go!"ListWithContext" lw.v)) (Val #ctx)) (Val #opts))
        {{ Φ }}) ∗
    □ (∀ (ctx : GoInterface) (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions)
      (dq : DFrac) (lo : kd.meta.ListOptions) (Φ : val → IProp GF),
      kd.meta.ListOptions.own opts dq lo -∗
      ▷ (∀ (w err : GoInterface) (σ : apimodel.St), kd.meta.ListOptions.own opts dq lo -∗
          watchRet γa cfg false res go!"" lo σ w err -∗ fmt.argOk err -∗ Φ (PairV #w #err)) -∗
      WP (App (App (Val #(methods lw.ty go!"WatchWithContext" lw.v)) (Val #ctx)) (Val #opts))
        {{ Φ }}))

instance lwOk_persistent (lw : GoInterfaceOk) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res) :
    Persistent (lwOk (GF := GF) lw γa cfg res) := by
  unfold lwOk; infer_instance

/-- **The deep value of a `ListOptions` literal** whose `SendInitialEvents` is `nil`, its timeout
pointer's target `ts`. -/
def loOf (v : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions) (ts : Option w64) :
    kd.meta.ListOptions :=
  ⟨⟨v.TypeMeta'.Kind', v.TypeMeta'.APIVersion'⟩, v.LabelSelector', v.FieldSelector', v.Watch',
    v.AllowWatchBookmarks', v.ResourceVersion', v.ResourceVersionMatch', ts, v.Limit', v.Continue',
    none, v.ShardSelector'⟩

theorem lo_own_intro (v : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions) (ts : Option w64)
    (dq : DFrac) (hsie : v.SendInitialEvents' = null) :
    ownPtrD (GF := GF) ownBaseD v.TimeoutSeconds' dq ts ⊢ kd.meta.ListOptions.own v dq (loOf v ts) := by
  iintro H
  unfold kd.meta.ListOptions.own kd.meta.TypeMeta.own loOf
  iframe
  simp only [ownPtrD]
  iframe
  ipureintro
  simp [hsie]

open Iris.ProofMode in
/-- An API error is not `nil`. -/
theorem errIs_ne_nil (err : GoInterface) (e : ApiErr) :
    apimodel.errIs (GF := GF) err e ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold apimodel.errIs
  iintro ⟨%p, %st, %h, -⟩
  ipureintro
  rw [h]
  simp [interface.mkOk]

open Iris.ProofMode in
/-- **What a watch without selectors returns**: an error (and no watch), or the watch. -/
theorem watchRet_cases (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res)
    (lo : kd.meta.ListOptions) (σ : apimodel.St) (w err : GoInterface)
    (hls : lo.LabelSelector' = go!"") (hfs : lo.FieldSelector' = go!"")
    (hsie : lo.SendInitialEvents' = none) :
    watchRet (GF := GF) γa cfg false res go!"" lo σ w err ⊢
      ⌜w = interface.nil ∧ err ≠ interface.nil⌝ ∨
      (⌜err = interface.nil⌝ ∗ ∃ (γw : WatchNames) (inits : List Obj) (n0 : w64),
        watchAt w γa γw res go!"" (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !false) inits ∗
        watchCons γw 0 (logStart (σ.tbl res).log n0, n0) ∗ pastSt γa σ ∗
        ⌜watchStartOk res go!"" lo σ inits n0⌝) := by
  unfold watchRet
  rw [ite_eq_right (by simp [hls, hfs, hsie])]
  iintro (⟨⟨-, %hw⟩, Herr⟩ | ⟨⟨%hw, -⟩, Herr⟩ | ⟨%he, H⟩)
  · ihave %hne := errIs_ne_nil err _ $$ Herr
    ileft; ipureintro; exact ⟨hw, hne⟩
  · ihave %hne := errIs_ne_nil err _ $$ Herr
    ileft; ipureintro; exact ⟨hw, hne⟩
  · iright; iframe; ipureintro; exact he

/-- **The backoff returns a duration** (persistent). -/
def delayOk (dh : GoFunc) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ d : time.Duration, Φ #d) -∗
    WP (App (Val #dh) (Val #())) {{ Φ }})

instance delayOk_persistent (dh : GoFunc) : Persistent (delayOk (GF := GF) dh) := by
  unfold delayOk; infer_instance

/-- **Every state the server reaches has good keys** (persistent). -/
def keysOk (γa : ApiNames) : IProp GF :=
  iprop(□ ∀ σ : apimodel.St, pastSt γa σ -∗ ⌜∀ res, ∀ c ∈ (σ.tbl res).log, keyGood c.obj.key⌝)

instance keysOk_persistent (γa : ApiNames) : Persistent (keysOk (GF := GF) γa) := by
  unfold keysOk; infer_instance

/-- The reflector's fixed fields, part 1 (persistent): the store, list-watch, expected type and GVK,
resync period, watch-list switch, clock. -/
def reflFixed1 (r f : Loc) (lw : GoInterfaceOk) (et : reflect.Type') : IProp GF :=
  iprop(∃ c : k8s_io.utils.clock.RealClock,
    r.[Reflector, go!"store"] ↦□ interface.mkOk (go.GoType.PointerType RealFIFO.ty) #f ∗
    r.[Reflector, go!"listerWatcher"] ↦□ interface.ok lw ∗
    r.[Reflector, go!"expectedType"] ↦□ et ∗
    r.[Reflector, go!"expectedGVK"] ↦□ (null : Loc) ∗
    r.[Reflector, go!"resyncPeriod"] ↦□ (W64 0 : time.Duration) ∗
    r.[Reflector, go!"useWatchList"] ↦□ false ∗
    r.[Reflector, go!"clock"] ↦□
      (interface.mkOk k8s_io.utils.clock.RealClock.ty #c : k8s_io.utils.clock.Clock))

instance reflFixed1_persistent (r f : Loc) (lw : GoInterfaceOk) (et : reflect.Type') :
    Persistent (reflFixed1 (GF := GF) r f lw et) := by
  unfold reflFixed1; infer_instance

/-- The reflector's fixed fields, part 2 (persistent): the backoff, names, page size, retry
duration, resync and error-handler functions. -/
def reflFixed2 (r : Loc) (dh : GoFunc) : IProp GF :=
  iprop(∃ (name td : GoString) (ps : w64) (md : time.Duration) (sr weh : GoFunc),
    r.[Reflector, go!"delayHandler"] ↦□ dh ∗
    r.[Reflector, go!"name"] ↦□ name ∗
    r.[Reflector, go!"typeDescription"] ↦□ td ∗
    r.[Reflector, go!"WatchListPageSize"] ↦□ ps ∗
    r.[Reflector, go!"MaxInternalErrorRetryDuration"] ↦□ md ∗
    r.[Reflector, go!"ShouldResync"] ↦□ sr ∗
    r.[Reflector, go!"watchErrorHandler"] ↦□ weh)

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
instance reflFixed2_persistent (r : Loc) (dh : GoFunc) :
    Persistent (reflFixed2 (GF := GF) r dh) := by
  unfold reflFixed2; infer_instance

/-- **The reflector's fixed fields** (persistent): see the file header. -/
def reflFixed (r f : Loc) (lw : GoInterfaceOk) (et : reflect.Type') (dh : GoFunc) : IProp GF :=
  iprop(reflFixed1 r f lw et ∗ reflFixed2 r dh ∗ delayOk dh)

instance reflFixed_persistent (r f : Loc) (lw : GoInterfaceOk) (et : reflect.Type') (dh : GoFunc) :
    Persistent (reflFixed (GF := GF) r f lw et dh) := by
  unfold reflFixed; infer_instance

/-- A last version is positive (a list's or an event's: the model's versions start at `1`). -/
def lastPos (n : Option Nat) : Prop := ∀ k, n = some k → 1 ≤ k

/-- **The reflector's fields its goroutine owns besides the versions**: `paginatedResult` (written by
`list`) and the watch timeouts (read through a pointer to the field, `(*time.Duration).Seconds`,
whose boundary spec takes the field owned). -/
def reflMisc (r : Loc) : IProp GF :=
  iprop(∃ (pr : Bool) (mn mx : time.Duration), r.[Reflector, go!"paginatedResult"] ↦ pr ∗
    r.[Reflector, go!"minWatchTimeout"] ↦ mn ∗ r.[Reflector, go!"maxWatchTimeout"] ↦ mx)

/-- **The reflector goroutine's state**: see the file header. -/
def reflSt (r : Loc) (γi : InfNames) (n : Option Nat) : IProp GF :=
  iprop(∃ (v : GoString) (u : Bool), reflOwn r v u ∗ reflMisc r ∗ reflLast γi n ∗
    ⌜rvRel v n ∧ lastPos n⌝)

/-- **The watch loop's state after an event** (`handleAnyWatch`'s `L`): the reflector's fields at
the watch's version `p.2`, the informer's last version it, the cursor in a past state's log. -/
def wL (r : Loc) (γa : ApiNames) (γi : InfNames) (res : Res) (_i : Nat) (p : Pos') : IProp GF :=
  iprop(∃ (u : Bool) (σ : apimodel.St), reflOwn r (rvStr p.2) u ∗
    reflMisc r ∗ reflLast γi (some p.2.toNat) ∗ pastSt γa σ ∗
    ⌜1 ≤ p.2.toNat ∧ curOk res p σ⌝)

/-- **The watch loop's state between an event's push and its callback** (`handleAnyWatch`'s `C`):
as `wL`, but the reflector's field still the previous version, the event's `rv` the decimal of
the new one. -/
def wC (r : Loc) (γa : ApiNames) (γi : InfNames) (res : Res) (_i : Nat) (p : Pos') (rv : GoString) :
    IProp GF :=
  iprop(∃ (v : GoString) (u : Bool) (σ : apimodel.St), reflOwn r v u ∗
    reflMisc r ∗ reflLast γi (some p.2.toNat) ∗ pastSt γa σ ∗
    ⌜rv = rvStr p.2 ∧ 1 ≤ p.2.toNat ∧ curOk res p σ⌝)

end defs

/-! ### Each watch event's step through the informer invariant -/

section glue
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The later of two past states, ordered. -/
theorem later_of_cmp (σ σ1 : apimodel.St) (h : apimodel.St.le σ σ1 ∨ apimodel.St.le σ1 σ) :
    ∃ σq : apimodel.St, apimodel.St.le σ σq ∧ apimodel.St.le σ1 σq ∧ (σq = σ ∨ σq = σ1) := by
  rcases h with h | h
  · exact ⟨σ1, h, St.le_refl _, Or.inr rfl⟩
  · exact ⟨σ, St.le_refl _, h, Or.inl rfl⟩

/-- A log entry of an earlier state is the later state's at the same index. -/
theorem log_get_later (res : Res) (σ1 σq : apimodel.St) (hle : apimodel.St.le σ1 σq) (j : Nat) (c : Change)
    (h : (σ1.tbl res).log[j]? = some c) : (σq.tbl res).log[j]? = some c := by
  obtain ⟨-, -, hlog⟩ := hle
  obtain ⟨⟨l', hl'⟩, -⟩ := hlog res
  rw [← hl', List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

/-- The FIFO delta type of a logged change's watch event. -/
theorem watchFdTy_typ (t : EvTy) : watchFdTy t.str = fdTypeOf t := by
  cases t <;> rfl

theorem zeroObj_res (res : Res) : (zeroObj res).res = res := by cases res <;> rfl

theorem evTy_str_ne_bookmark (t : EvTy) : t.str ≠ go!"BOOKMARK" := by
  cases t <;> simp [EvTy.str]

open Iris.ProofMode in
/-- An object's interface value is not `nil`. -/
theorem objAt_ne_nil (x : GoInterface) (dq : DFrac) (o : Obj) :
    (apimodel.objAt x dq o : IProp GF) ⊢ ⌜x ≠ interface.nil⌝ := by
  cases o <;> simp only [apimodel.objAt] <;> iintro ⟨%l, %h, -⟩ <;> ipureintro <;> rw [h] <;>
    simp [interface.mkOk]

theorem evTy_str_cases (t : EvTy) :
    t.str = go!"ADDED" ∨ t.str = go!"MODIFIED" ∨ t.str = go!"DELETED" := by
  cases t <;> simp [EvTy.str]

/-- **Each watch event's step** (`evStepOk`, for the reflector's `watch`): through the informer
invariant, the event's change pushed (`infInv_pushChangeAU`, the object registered first) or its
bookmark (`infInv_pushBookmarkAU`), the watch's cursor and the reflector's last version moved to
the event's. -/
theorem watch_evStepOk (r : Loc) (γa : ApiNames) (res : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (γw : WatchNames) (bm : Bool) :
    ⊢ infInv (GF := GF) γa res γf γt γi -∗ keysOk γa -∗
      evStepOk γa γw res bm [] γf (infObj γi res) (wL r γa γi res) (wC r γa γi res) := by
  iintro #Hinv #Hkeys
  iunfold keysOk at Hkeys
  unfold evStepOk
  imodintro
  iintro %i %p %ev HL #Hidx Hev
  iunfold wL at HL
  icases HL with ⟨%u, %σ, Hown, Hpr, Hlast, #Hσ, %hpc⟩
  obtain ⟨hpos, hcur⟩ := hpc
  iunfold evOk at Hev
  icases Hev with ⟨%p0, %p', %σ1, %o, #Hi0, #Hi1, #Hσ1, %hstep, Hobj⟩
  simp only [Int.toNat_natCast]
  ihave %hp0 := mono_list_idx_agree γw.cur i p p0 $$ Hidx Hi0
  subst hp0
  ihave %hcmp := pastSt_cmp γa σ σ1 $$ Hσ Hσ1
  obtain ⟨σq, hσq, hσ1q, hq⟩ := later_of_cmp σ σ1 hcmp
  ihave #Hσq : pastSt γa σq $$ []
  · rcases hq with rfl | rfl
    · iexact Hσ
    · iexact Hσ1
  ihave #Hwf1 := Hσ1
  iunfold pastSt at Hwf1
  icases Hwf1 with ⟨%H1, -, %hH1⟩
  have hwf1 : σ1.wf := hH1.2.1
  ihave #Hwfq := Hσq
  iunfold pastSt at Hwfq
  icases Hwfq with ⟨%Hq, -, %hHq⟩
  have hwfq : σq.wf := hHq.2.1
  ihave %hgood1 := Hkeys $$ %σ1 Hσ1
  ihave %hgoodq := Hkeys $$ %σq Hσq
  have hcurq : curOk res p σq := curOk_later res p σ σq hσq hcur
  simp only [Int.toNat_natCast] at hstep
  rcases hstep with ⟨hlt, -⟩ | ⟨-, c, hc, hpp, hrange, -, hp2, htyp, ho⟩ |
      ⟨-, -, hpp, hp1, hrange, hp2, hlt, htyp, ho⟩
  · simp at hlt
  · -- a change: the log's next after the cursor, at index `p.1`
    have hp' : p'.1 = p.1 + 1 := by
      rcases Nat.lt_or_ge p.1 (p'.1 - 1) with hj | hj
      · have hlen : p'.1 - 1 < (σ1.tbl res).log.length := (List.getElem?_eq_some_iff.1 hc).1
        obtain ⟨d, hd⟩ : ∃ d, (σ1.tbl res).log[p.1]? = some d :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have := hrange p.1 (Nat.le_refl _) hj d hd
        simp [inNs] at this
      · omega
    rw [hp', Nat.add_sub_cancel] at hc
    have hcq := log_get_later res σ1 σq hσ1q p.1 c hc
    obtain ⟨hnext, hcur'⟩ := curOk_change res p σq hwfq c hcurq hcq
    have hc1 : c ∈ (σ1.tbl res).log := List.mem_of_getElem? hc
    obtain ⟨hres, hrvo⟩ := hwf1.log_obj res c hc1
    subst ho
    imod infInv_register γa res γf γt γi ev.Object' c.obj hres $$ Hinv Hobj with ⟨#Hok, #Hreg⟩
    ihave #Hobjd : □ apimodel.objAt ev.Object' DFrac.discard c.obj $$ [Hok]
    · iunfold infObj at Hok
      icases Hok with ⟨%o', #Hx', #Ho', -⟩
      ihave %ho' := ghostMapElem_agree ev.Object' γi.reg DFrac.discard DFrac.discard c.obj o' $$ Hreg Hx'
      subst ho'
      iexact Ho'
    ihave %hnil := objAt_ne_nil ev.Object' DFrac.discard c.obj $$ Hobjd
    have hpe : p' = (p.1 + 1, c.rv) := Prod.ext hp' hp2
    have hpos' : 1 ≤ c.rv.toNat := by have := (hwf1.log_le res c hc1).1; omega
    imodintro
    iexists c.obj, p'
    iframe #
    isplitr
    · ipureintro; exact hres
    unfold evAct
    rw [htyp, ite_eq_left_of_eq_true _ _ (eq_true (evTy_str_cases c.typ)), watchFdTy_typ]
    iframe #
    unfold fifoAU
    iapply (infInv_pushChangeAU γa res γf γt γi p.2.toNat σq c ev.Object' hnext (hgoodq res) hnil
      (wC r γa γi res (i + 1) p' c.obj.meta.ResourceVersion')) $$ Hinv Hσq Hreg Hlast
    iintro Hlast
    unfold wC
    iexists (rvStr p.2), u, σq
    rw [hpe]
    iframe
    iframe #
    ipureintro
    exact ⟨hrvo, hpos', hcur'⟩
  · -- a bookmark: no change since the cursor, at the version of the state the event came from
    have hp1' : p.1 = (σ1.tbl res).log.length := by
      rcases Nat.lt_or_ge p.1 (σ1.tbl res).log.length with hj | hj
      · obtain ⟨d, hd⟩ : ∃ d, (σ1.tbl res).log[p.1]? = some d :=
          ⟨_, List.getElem?_eq_getElem hj⟩
        have := hrange p.1 (Nat.le_refl _) (by omega) d hd
        simp [inNs] at this
      · omega
    have hq1 : Quiet (σ1.tbl res).log p.2.toNat σ1.rev.toNat := by
      refine ⟨by rw [← hp2]; omega, fun d hd hlt' => ?_⟩
      exfalso
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hd
      have hjlen : j < (σ1.tbl res).log.length := (List.getElem?_eq_some_iff.1 hj).1
      have hjq := log_get_later res σ1 σq hσ1q j d hj
      have := logStart_le (σq.tbl res).log p.2 j (by rw [← hcurq.1]; omega) d hjq
      omega
    imod objAt_persist ev.Object' (DFrac.own 1) o $$ Hobj with #Hobjd
    subst ho
    have hpe : p' = ((σ1.tbl res).log.length, σ1.rev) := Prod.ext (by omega) hp2
    have hcur' : curOk res ((σ1.tbl res).log.length, σ1.rev) σq := by
      refine ⟨?_, hσ1q.1⟩
      obtain ⟨-, -, hlog⟩ := hσ1q
      obtain ⟨⟨l', hl'⟩, hlater⟩ := hlog res
      show (σ1.tbl res).log.length = logStart (σq.tbl res).log σ1.rev
      rw [← hl', logStart_append _ l' σ1.rev (fun d hd => ?_), logStart_rev σ1 hwf1 res]
      rw [← hl', List.drop_left] at hlater
      exact hlater d hd
    imodintro
    iexists ((zeroObj res).modMeta fun m => { m with ResourceVersion' := rvStr σ1.rev }), p'
    iframe #
    isplitr
    · ipureintro; simp [zeroObj_res]
    unfold evAct
    rw [htyp]
    simp only [show ¬ (go!"BOOKMARK" = go!"ADDED" ∨ go!"BOOKMARK" = go!"MODIFIED" ∨
      go!"BOOKMARK" = go!"DELETED") by decide, ↓reduceIte, Obj.meta_modMeta]
    unfold fifoAU
    iapply (infInv_pushBookmarkAU γa res γf γt γi p.2.toNat σ1 σ1.rev hq1 (Nat.le_refl _)
      (hgood1 res) (wC r γa γi res (i + 1) p' (rvStr σ1.rev))) $$ Hinv Hσ1 Hlast
    iintro Hlast
    unfold wC
    iexists (rvStr p.2), u, σq
    rw [hpe]
    iframe
    iframe #
    ipureintro
    exact ⟨rfl, hwf1.rev_pos, hcur'⟩

end glue

end cache
end EtcdGrove
end Perennial
