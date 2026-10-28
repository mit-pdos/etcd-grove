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
  printable (`fmt.argOk`); a list is of a state at least any past state the caller knew before the
  call (the typed clients' `List` is logically atomic: it reads the current state). In `Main` the typed informers' list-watch closures do (gap D2: their
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
public import Proof.k8s_io.client_go.tools.pager.Defs
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
variable [FfiSyntax] [GoGlobalContext]

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

/-- **A well-formed state's table is its log's table at its version.** -/
theorem tableAt_rev (σ : apimodel.St) (hwf : σ.wf) (res : Res) :
    tableAt (σ.tbl res).log σ.rev.toNat = (σ.tbl res).objs := by
  rw [hwf.objs_replay res]
  unfold tableAt
  congr 1
  rw [List.filter_eq_self]
  intro c hc
  simpa using (hwf.log_le res c hc).2

theorem forall2_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      ∀ i (h1 : i < xs.length) (h2 : i < ys.length), R xs[i] ys[i]
  | _, _, .nil, i, h1, _ => by simp at h1
  | _, _, .cons hab hrest, 0, _, _ => hab
  | _, _, .cons _ hrest, i + 1, h1, h2 =>
      forall2_getElem hrest i (by simpa using h1) (by simpa using h2)

/-- **A list's objects, registered, are the table**: each listed Go object's registered model
object is in the table at the state's version, and each of the table's objects is a listed one's. -/
theorem listRel_of_list (res : Res) (σ : apimodel.St) (hwf : σ.wf) (os : List Obj)
    (hl : listOk res go!"" σ os) (R0 : Reg) (xs : List GoInterface)
    (h2 : List.Forall₂ (fun x o => R0 !! x = some o) xs os) :
    listRel R0 xs (tableAt (σ.tbl res).log σ.rev.toNat) := by
  rw [tableAt_rev σ hwf res]
  have hkeyed : ∀ key o, (σ.tbl res).objs !! key = some o → o.key = key := by
    rw [← tableAt_rev σ hwf res]; exact tableAt_keyed _ _
  have hmem : ∀ o, o ∈ os ↔ ∃ k, (σ.tbl res).objs !! k = some o := by
    intro o
    rw [hl.mem_iff]
    simp only [List.mem_map, List.mem_filter, inNs, _root_.decide_true, Bool.true_or, _root_.and_true]
    constructor
    · rintro ⟨⟨k, o'⟩, hm, rfl⟩; exact ⟨k, (GMap.mem_toList _ _ _).1 hm⟩
    · rintro ⟨k, hk⟩; exact ⟨⟨k, o⟩, (GMap.mem_toList _ _ _).2 hk, rfl⟩
  refine ⟨fun x hx => ?_, fun key o hko => ?_⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
    obtain ⟨o, ho, hR⟩ : ∃ o, os[i]? = some o ∧ R0 !! x = some o := by
      have hlen := h2.length_eq
      have hix : i < xs.length := (List.getElem?_eq_some_iff.1 hi).1
      have hi' : i < os.length := by omega
      refine ⟨os[i], List.getElem?_eq_getElem hi', ?_⟩
      have hx' : xs[i] = x := (List.getElem?_eq_some_iff.1 hi).2
      rw [← hx']
      exact forall2_getElem h2 i hix hi'
    obtain ⟨k, hk⟩ := (hmem o).1 (List.mem_of_getElem? ho)
    refine ⟨o, hR, ?_⟩
    rw [hkeyed k o hk]; exact hk
  · have ho : o ∈ os := (hmem o).2 ⟨key, hko⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ho
    have hlen := h2.length_eq
    have hi' : i < os.length := (List.getElem?_eq_some_iff.1 hi).1
    refine ⟨xs[i]'(by omega), List.getElem_mem _, ?_⟩
    have := forall2_getElem h2 i (by omega) hi'
    rw [this]
    exact congrArg some ((List.getElem?_eq_some_iff.1 hi).2)

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
      (dq : DFrac) (lo : kd.meta.ListOptions) (σ0 : apimodel.St) (Φ : val → IProp GF),
      kd.meta.ListOptions.own opts dq lo -∗ pastSt γa σ0 -∗
      ▷ (∀ (q : Loc) (err : GoInterface) (σ : apimodel.St), kd.meta.ListOptions.own opts dq lo -∗
          typedListRet γa cfg.FailReads' false res go!"" lo σ q err -∗ fmt.argOk err -∗
          ⌜apimodel.St.le σ0 σ⌝ -∗
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

/-- **The reflector goroutine's state**: see the file header; and a past state `σ0` whose version is
at least the reflector's last (so a later list is at least it). -/
def reflSt (r : Loc) (γa : ApiNames) (γi : InfNames) (n : Option Nat) : IProp GF :=
  iprop(∃ (v : GoString) (u : Bool) (σ0 : apimodel.St), reflOwn r v u ∗ reflMisc r ∗ reflLast γi n ∗
    pastSt γa σ0 ∗ ⌜rvRel v n ∧ lastPos n ∧ rvLe n (some σ0.rev.toNat)⌝)

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

/-- **Registering a list's objects** (the reflector, before its relist's `Replace`): each fresh
object registered with its model object, read-only (`infObj`, the FIFO's contract), and a registry
of them all, which maps each listed Go object to its model object. -/
theorem infInv_register_list (γa : ApiNames) (res : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) :
    ∀ (xs : List GoInterface) (os : List Obj), (∀ o ∈ os, o.res = res) →
    ⊢ infInv (GF := GF) γa res γf γt γi -∗ ([∗list] x;o ∈ xs;os, apimodel.objAt x (DFrac.own 1) o) ={⊤}=∗
      ∃ R0 : Reg, ([∗map] x ↦ o ∈ R0, x ↪[γi.reg]□ o) ∗ ([∗list] x ∈ xs, infObj γi res x) ∗
        ⌜List.Forall₂ (fun x o => R0 !! x = some o) xs os⌝
  | [], [], _ => by
    iintro #Hinv -
    imodintro
    iexists ∅
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; exact .nil
  | [], _ :: _, _ => by
    iintro - H
    ihave %h := BigSepL2.bigSepL2_nil_inv_left $$ H
    cases h
  | _ :: _, [], _ => by
    iintro - H
    ihave %h := BigSepL2.bigSepL2_nil_inv_right $$ H
    cases h
  | x :: xs, o :: os, hres => by
    iintro #Hinv H
    icases BigSepL2.bigSepL2_cons.1 $$ H with ⟨Hx, H⟩
    imod infInv_register_list γa res γf γt γi xs os (fun o' ho' => hres o' (List.mem_cons_of_mem _ ho'))
      $$ Hinv H with ⟨%R0, #HR0, #Hoks, %h2⟩
    imod infInv_register γa res γf γt γi x o (hres o List.mem_cons_self) $$ Hinv Hx with ⟨#Hok, #Hel⟩
    cases hx : R0 !! x with
    | some o' =>
      ihave #Hel' := BigSepM.bigSepM_lookup (Φ := fun x o => iprop(x ↪[γi.reg]□ o)) hx $$ HR0
      ihave %ho := ghostMapElem_agree x γi.reg DFrac.discard DFrac.discard o o' $$ Hel Hel'
      subst ho
      imodintro
      iexists R0
      isplitr
      · iframe #
      isplitr
      · iapply BigSepL.bigSepL_cons.2; iframe #
      ipureintro; exact .cons hx h2
    | none =>
      imodintro
      iexists <[x := o]> R0
      isplitr
      · iapply (BigSepM.bigSepM_insert (Φ := fun x o => iprop(x ↪[γi.reg]□ o)) hx).2
        iframe #
      isplitr
      · iapply BigSepL.bigSepL_cons.2; iframe #
      ipureintro
      refine .cons (GMap.lookup_insert _ _ _) ?_
      refine List.Forall₂.imp (fun {y o'} hy => ?_) h2
      rw [GMap.lookup_insert_eq_iff]
      split
      · rename_i hyx; subst hyx; rw [hx] at hy; cases hy
      · exact hy

open Iris.ProofMode in
/-- A typed list's pointer is not `nil`. -/
theorem typedListAt_ne_null (res : Res) (q : Loc) (os : List Obj) (rv : GoString) :
    typedListAt (GF := GF) res q os rv ⊢ typedListAt res q os rv ∗ ⌜q ≠ null⌝ := by
  cases res <;> simp only [typedListAt] <;> iintro ⟨%lv, %vs, %ds, Hq, %h, Hrest⟩ <;>
    ihave ⟨Hq, %hq⟩ := typedPointsto_not_null_dup _ _ _ $$ Hq <;>
    (isplitl; (iexists lv, vs, ds; iframe; ipureintro; exact h); ipureintro; exact hq)

/-- **A listed state** (`S` of the reflector's pager): the list's version the decimal of the state's,
its objects the state's table, the state at least `σ0`. -/
def listS (γa : ApiNames) (σ0 : apimodel.St) (res : Res) (_q : Loc) (os : List Obj) (rv : GoString) :
    IProp GF :=
  iprop(∃ σ : apimodel.St, pastSt γa σ ∗
    ⌜rv = rvStr σ.rev ∧ listOk res go!"" σ os ∧ apimodel.St.le σ0 σ⌝)

open Iris.ProofMode in
/-- **What the list-watch's `List` returns is a page result.** -/
theorem typedListRet_pageRes (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res)
    (lo : kd.meta.ListOptions) (σ0 σ : apimodel.St) (q : Loc) (err : GoInterface)
    (hle : apimodel.St.le σ0 σ) :
    typedListRet (GF := GF) γa cfg.FailReads' false res go!"" lo σ q err ∗ fmt.argOk err ⊢
      pager.pageRes res (listS γa σ0 res)
        (interface.mkOk (go.GoType.PointerType (resListTy res)) #q) err := by
  unfold typedListRet pager.pageRes
  iintro ⟨H, Hae⟩
  split
  · icases H with ⟨%hq, Herr⟩
    ihave %hne := errIs_ne_nil err _ $$ Herr
    ileft; iframe; ipureintro; exact ⟨hne, Or.inr (by rw [hq])⟩
  · icases H with (⟨⟨-, %hq⟩, Herr⟩ | ⟨%he, %os, Hl, %hl, #Hσ⟩)
    · ihave %hne := errIs_ne_nil err _ $$ Herr
      ileft; iframe; ipureintro; exact ⟨hne, Or.inr (by rw [hq])⟩
    · iright
      isplitr
      · ipureintro; exact he
      iexists q, os, rvStr σ.rev
      iframe
      isplitr
      · ipureintro; rfl
      unfold listS
      iexists σ
      iframe #
      ipureintro; exact ⟨rfl, hl, hle⟩

end glue

end cache
end EtcdGrove
end Perennial
