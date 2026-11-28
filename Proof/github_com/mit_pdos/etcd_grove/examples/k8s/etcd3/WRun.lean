/-
Lean-first (no Rocq counterpart).

# Running a watch: the driver's Go values and its view of the store's watch (stage 7f-6 D)

- `driverW`, the driver's `WatchSpec`: an annotated object is `objAtD`'s with `Annotated' := true`
  (`SetAnnotations` of the initial-events-end annotation; ledger 2026-11-16);
- `predWV x b`, `watchOptsV x p`: `watchOptions(in)`'s predicate (`predicate(in)` with
  `AllowWatchBookmarks := b`) and options (`SendInitialEvents` the cell `p`, `sieOfL x`);
- `lastObjL`: `lastObj`'s answer;
- `doneTok`/`donePD` (the driver's Done token), `kSeen` (what the received events satisfy),
  `kStopOk`;
- `predOk_driverW`: that predicate selects as `predicate(in)` (`selD x`, `predEmptyL x`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatchBridge
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOkDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Watch
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (WEvent Obj Input)

/-- `DObj` is countable (the store watch's ghost list of the received models, `k8sWatch`). -/
instance dobj_countable : Pos.Countable DObj :=
  .ofInjective (fun o => Pos.Countable.encode (o.ns, o.name, o.uid, o.val, o.node, o.app))
    (fun a b h => by
      have h' := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h'
      exact (DObj.ext_iff' a b).2 h')

section vals
variable [GooseExts] [GoLocalContext] [GoSemanticsFunctions] [GoGlobalContext]

/-- `watchOptions(in)`'s predicate: `predicate(in)`'s with `AllowWatchBookmarks := b`. -/
def predWV (x : Input) (b : Bool) : k8s_io.apiserver.pkg.storage.SelectionPredicate :=
  { predV x with AllowWatchBookmarks' := b }

/-- `watchOptions(in)`, its `SendInitialEvents` the cell `p` (`null` for none). -/
def watchOptsV (x : Input) (p : Loc) : k8s_io.apiserver.pkg.storage.ListOptions :=
  ⟨x.MinRV', matchOptL x, predWV x x.Bookmarks', x.Recursive', false, p, false⟩

/-- `lastObj(evs)`: the object of the last event that is neither an Error nor a bad event. -/
def lastObjL (evs : List WEv) : Option Obj :=
  (evs.reverse.find? fun e => decide (e.t ≠ 4 ∧ e.t ≠ 5)).map (·.o)

end vals

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- `SendInitialEvents`' cell as `watchOptions` returns it: `null`, or fresh and owned (its caller
persists it into `sendInitIs`). -/
def sendInitOwn (p : Loc) : Option Bool → IProp GF
  | none => iprop(⌜p = null⌝)
  | some b => iprop(p ↦ b)

/-- **The driver's annotated object** (`WatchSpec.annAt`): `objAtD`'s, with the annotation set. -/
def driverW : WatchSpec GF DObj where
  annAt x o rv := iprop(∃ (p : Loc) (n : w64),
    ⌜x = interface.mkOk (go.GoType.PointerType objTyD) #p ∧ p ≠ null ∧ rv = rvStr n⌝ ∗
    p ↦ { o.toObj n with Annotated' := true })

/-- **`watchOptions(in)`'s predicate selects as `predicate(in)`** (`predOk_driver`'s, with
`AllowWatchBookmarks` set, which neither `Matches` nor `Empty` reads). -/
theorem predOk_driverW
    (wp_Matches : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_Empty : storage.SelectionPredicate.Empty.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) (x : Input) (b : Bool) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ⊢
      selPredOk driverSpec (predWV x b) (selD x) (predEmptyL x) := by
  iintro #Hpkg
  ihave #Hl0 := labelSelOk_driver wp_LM wp_LE x $$ Hpkg
  ihave #Hf0 := fieldSelOk_driver wp_FM wp_FE x $$ Hpkg
  ihave #Hl : k8s.labelSelOk (predWV x b).Label' (labelSelL x).all' (lmL (labelSelL x)) $$ []
  · rw [show (predWV x b).Label' = (predV x).Label' from rfl]; iexact Hl0
  ihave #Hf : k8s.fieldSelOk (predWV x b).Field' (decide ((fieldSelForL x).n' = W64 0))
      (fmL (fieldSelForL x)) $$ []
  · rw [show (predWV x b).Field' = (predV x).Field' from rfl]; iexact Hf0
  ihave #Ps : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  unfold selPredOk
  isplitr
  · ipureintro
    refine ⟨rfl, fun he o => ?_⟩
    have := sel_answer x (o.toObj (W64 0))
    unfold predEmptyL at he
    simp only [selD]
    rw [← this, he]
  isplitr
  · imodintro
    iintro %pp %dq %x' %o %rv %Ψ Hp Ho HΨ
    rw [show (driverSpec (GF := GF)).objAt = objAtD from rfl]
    ihave #Hg0 := getAttrsOk_D wp_GA rv $$ Hpkg
    ihave #Hg : getAttrsOk (fun x o => objAtD x o rv) (predWV x b).GetAttrs'
        (fun o : DObj => labMapL (o.toObj (W64 0))) (fun o => fldMapL (o.toObj (W64 0))) $$ []
    · simp only [predWV, predV]; iexact Hg0
    wp_apply (wp_Matches DObj (fun x o => objAtD x o rv) pp dq (predWV x b) _ _ _ _ _ _ x' o rfl)
      $$ [$Hp $Hl $Hf $Hg $Ho] as ⟨Hp, Ho⟩
    have hs := sel_answer x (o.toObj (W64 0))
    simp only [selD]
    rw [← hs]
    iapply HΨ $$ Hp Ho
  · imodintro
    iintro %pp %dq %Ψ Hp HΨ
    wp_apply (wp_Empty pp dq (predWV x b) _ _ _ _ rfl) $$ [$Hp $Hl $Hf] as Hp
    simp only [predEmptyL]
    iapply HΨ $$ Hp

/-- **The driver's Done token** (`watchEvents`' context `WithCancel(Background())`, whose `PDone` is
`donePD γd`): held until the driver stops reading, it refutes the context's being done. -/
def doneTok (γd : GName) : IProp GF := dghostVar γd (DFrac.own 1) false

/-- The Done proposition of the driver's context: the driver has given up its token. -/
def donePD (γd : GName) : IProp GF := dghostVar γd DFrac.discard true

instance donePD_persistent (γd : GName) : Persistent (donePD (GF := GF) γd) := by
  unfold donePD; infer_instance

theorem doneTok_donePD (γd : GName) : doneTok (GF := GF) γd ∗ donePD γd ⊢ False := by
  unfold doneTok donePD
  iintro ⟨H1, H2⟩
  ihave %H := dghostVar_agree γd false (DFrac.own 1) true DFrac.discard $$ H1 H2
  cases H

/-- **A live watch whose context the driver can refute is not cancelled.** -/
theorem kCancelled_refute (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (γd : GName)
    (hcd : cd.PDone = donePD γd) :
    kLive γ ∗ doneTok γd ∗ kCancelled γ cd ⊢ False := by
  unfold kLive kCancelled kStopped
  iintro ⟨Hl, Ht, Hc⟩
  icases Hc with (Hs | #Hd)
  · ihave %H := dghostVar_agree γ.stop false (DFrac.own 1) true DFrac.discard $$ Hl Hs
    cases H
  · rw [hcd]
    iapply doneTok_donePD γd $$ [$Ht $Hd]

/-- **What the driver knows of the store events `kes` it received** (`kResElem`'s, with the
cancellation refuted): all Error events, or a prefix of the ideal stream from a start point tied to
a state its read update fired at, read at another. -/
def kSeen (c : StoreCfg GF DObj) (sel : DObj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (kes : List (KWEv DObj)) : IProp GF :=
  iprop(⌜kNonErr kes = []⌝ ∨
    ∃ (lb lb0 st : Nat) (σ σ0 : KVState), □ Q lb σ ∗ □ Q lb0 σ0 ∗
      ⌜kStartOk m σ0 st ∧ kStreamOk c.S.dec sel emp c.S.zero inS m σ st kes⌝)

/-- **`Stop()` of the store watch `wi`** (`k8sWatch`'s, persistent). -/
def kStopOk (wi : GoInterface) (γ : KWatchNames) : IProp GF :=
  iprop(∃ wo : GoInterfaceOk, ⌜wi = GoInterface.ok wo⌝ ∗
    □ (∀ Φ : val → IProp GF, (kLive γ ∨ kStopped γ) -∗ ▷ (kStopped γ -∗ Φ #()) -∗
      WP (App (Val #(methods wo.ty go!"Stop" wo.v)) (Val #())) {{ Φ }}))

instance kStopOk_persistent (wi : GoInterface) (γ : KWatchNames) :
    Persistent (kStopOk (GF := GF) wi γ) := by
  unfold kStopOk; infer_instance

/-- Two lists of mono-list elements at the same indices are equal. -/
theorem monoList_idxs_agree {A : Type} [Pos.Countable A] (γ : GName) :
    ∀ (L1 L2 : List A), L1.length = L2.length →
      ([∗list] j ↦ x ∈ L1, monoListIdxOwn (GF := GF) γ j x) ⊢
        ([∗list] j ↦ x ∈ L2, monoListIdxOwn γ j x) -∗ ⌜L1 = L2⌝ := by
  intro L1
  induction hn : L1.length generalizing L1 with
  | zero =>
    intro L2 h
    rw [List.length_eq_zero_iff.1 hn, List.length_eq_zero_iff.1 h.symm]
    iintro _ _; ipureintro; rfl
  | succ n ih =>
    intro L2 h
    have hne1 : L1 ≠ [] := by intro h1; subst h1; simp at hn
    have hne2 : L2 ≠ [] := by intro h2; subst h2; simp at h
    rw [← List.dropLast_concat_getLast hne1, ← List.dropLast_concat_getLast hne2]
    have hn1 : L1.dropLast.length = n := by simp [List.length_dropLast, hn]
    have hn2 : n = L2.dropLast.length := by simp [List.length_dropLast, ← h]
    iintro H1 H2
    icases BigSepL.bigSepL_snoc.1 $$ H1 with ⟨H1, Ha⟩
    icases BigSepL.bigSepL_snoc.1 $$ H2 with ⟨H2, Hb⟩
    ihave %He := ih L1.dropLast hn1 L2.dropLast hn2 $$ H1 H2
    rw [hn1, ← hn2]
    ihave %Hab := mono_list_idx_agree γ n (L1.getLast hne1) (L2.getLast hne2) $$ Ha Hb
    ipureintro
    rw [He, Hab]

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
