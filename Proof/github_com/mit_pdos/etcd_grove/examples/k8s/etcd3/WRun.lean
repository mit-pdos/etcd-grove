/-
Lean-first (no Rocq counterpart).

# Running a watch: the driver's Go values and its view of the store's watch (stage 7f-6 D)

- `driverW`, the driver's `WatchSpec`: an annotated object is `objAtD`'s with `Annotated' := true`
  (`SetAnnotations` of the initial-events-end annotation; ledger 2026-11-16);
- `predWV x b`, `watchOptsV x p`: `watchOptions(in)`'s predicate (`predicate(in)` with
  `AllowWatchBookmarks := b`) and options (`SendInitialEvents` the cell `p`, `sieOfL x`);
- `lastObjL`: `lastObj`'s answer;
- `predOk_driverW`: that predicate selects as `predicate(in)` (`selD x`, `predEmptyL x`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatchBridge
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Watch

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (WEvent Obj Input)

section vals
variable [GooseExts] [GoSemanticsFunctions] [GoGlobalContext]

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

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
