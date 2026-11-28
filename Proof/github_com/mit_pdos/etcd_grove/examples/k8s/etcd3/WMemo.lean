/-
Lean-first (no Rocq counterpart).

# The watch steps' memo (`wmemo`, `stepIdx`; k8s-dist K9 step 3, `notes/k8s-dist-k9.md`)

- `wkey`, `Input` and `Obj` are safe map keys: Go's `==` on two `wkey`s compares their fields one by
  one (`go_eq_struct`), the `Input`'s and its `Obj`'s too, each a pointer, string, integer or
  boolean, and is equality of values. Perennial has no lemma for a struct of comparable fields
  (`safeMapKey_of_go_eq` needs the whole comparison as one step), so `split_field_eq` steps
  through the fields: it splits on the first field comparison left in the goal
  (`notes/perennial-changes.md`, "A struct of comparable fields is a safe map key");
- `wentry k v`: the memo's entry `k ↦ v` is `watchOkL`'s verdict for the watch `k.in` with the events
  `k.evs` and failure `k.fail` (all `watchOkL` reads of the output, `watchOkL_out`), on the history
  `k.hist` holds (well formed, `HWf`: its store is its last);
- `memoOwn memo`: `memo`'s mutex, protecting the map `memo.m` (made) and its entries (persistent).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3
  (mcfg Input Output Obj wkey wmemo)

/-! ## `wkey` as a map key -/

attribute [ext] Obj Input wkey

instance wkey_decEq : DecidableEq wkey := fun a b => Classical.propDecidable (a = b)

section inj
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

include sem package_sem in
theorem wkey_intoVal_inj : Function.Injective (intoVal (V := wkey)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (wkey.TypeAssumptions.get_hist x) (wkey.TypeAssumptions.get_hist y) h))
  have := Input_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (wkey.TypeAssumptions.get_in x) (wkey.TypeAssumptions.get_in y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (wkey.TypeAssumptions.get_evs x) (wkey.TypeAssumptions.get_evs y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (wkey.TypeAssumptions.get_fail x) (wkey.TypeAssumptions.get_fail y) h))
  cases x; cases y; simp_all

instance wkey_intoValInj : go.IntoValInj wkey := ⟨wkey_intoVal_inj (sem := sem) (package_sem := package_sem)⟩

end inj

open Lean Elab Tactic Meta in
/-- Splits on the first comparison `decide (a = b)` in the goal whose sides are not both variables
(a field comparison of two keys; `HΦ`'s `decide (k = k')` is left), rewriting it to `true` in one
case and `false` in the other. -/
elab "split_field_eq" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some d := tgt.find? (fun e =>
      e.isAppOfArity ``Decidable.decide 2 &&
      match (e.getArg! 0).eq? with
      | some (_, a, b) => !(a.isFVar && b.isFVar)
      | none => false)
    | throwError "split_field_eq: no field comparison in the goal"
  let p ← Term.exprToSyntax (d.getArg! 0)
  evalTactic (← `(tactic| (by_cases hfe : $p <;>
    first
      | rw [decide_eq_true hfe]
      | rw [decide_eq_false hfe]
      | simp only [hfe, decide_true, decide_false])))

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A `wkey` is a safe map key: its `==` compares its fields (and its `Input`'s, and that one's
`Obj`'s) one by one, each a pointer, string, integer or boolean (`split_field_eq`). -/
instance wkey_safeMapKey (k : wkey) : SafeMapKey (GF := GF) wkey.ty k where
  key_ok := trivial
  wp_go_eq_map_key k' _ s E Φ := by
    iintro HΦ
    wp_pures
    repeat' (split_field_eq <;> (try wp_pures))
    all_goals first
      | (rw [decide_eq_false (show ¬ k = k' by rintro rfl; contradiction)]; iapply HΦ)
      | (rw [decide_eq_true (show k = k' by
          apply wkey.ext <;> (try apply Input.ext) <;> (try apply Obj.ext) <;> assumption)]
         iapply HΦ)

/-! ## The memo -/

/-- The memo's entry `k ↦ v`: `watchOkL`'s verdict on the history `k.hist` holds (see the file
header). -/
def wentry (k : wkey) (v : Bool) : IProp GF :=
  iprop(∃ H : HSt, histOwn k.hist' H.hist ∗ ⌜HWf H ∧ ∀ y : Output, y.WEvents' = k.evs' →
    y.WFailed' = k.fail' → v = watchOkL k.in' y H⌝)

instance wentry_persistent (k : wkey) (v : Bool) : Persistent (wentry (GF := GF) k v) := by
  unfold wentry; infer_instance

/-- **What `memo.mu` protects**: the map `memo.m`, made, and its entries. -/
def wmemoInv (memo : Loc) : IProp GF :=
  iprop(∃ (mm : GoMap) (M : GMap wkey Bool), structFieldRef wmemo go!"m" memo ↦ mm ∗ mm ↦$ M ∗
    [∗map] k ↦ v ∈ M, wentry k v)

/-- **`memo`'s mutex**, protecting `wmemoInv memo` (persistent). -/
def memoOwn (memo : Loc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    sync.isMutex (structFieldRef wmemo go!"mu" memo) (wmemoInv memo))

instance memoOwn_persistent (memo : Loc) : Persistent (memoOwn (GF := GF) memo) := by
  unfold memoOwn; infer_instance

/-- Storing an entry (over an older one for the key, if any). -/
theorem wentries_insert (M : GMap wkey Bool) (k : wkey) (v : Bool) :
    wentry (GF := GF) k v ⊢ ([∗map] k' ↦ v' ∈ M, wentry k' v') -∗
      [∗map] k' ↦ v' ∈ <[k := v]> M, wentry k' v' := by
  iintro #He HM
  cases h : M !! k with
  | none =>
    iapply (BigSepM.bigSepM_insert (Φ := fun k' v' => wentry (GF := GF) k' v') h).2
    isplitr
    · iexact He
    · iexact HM
  | some x =>
    icases (BigSepM.bigSepM_insert_acc (Φ := fun k' v' => wentry (GF := GF) k' v') h) $$ HM
      with ⟨-, Hacc⟩
    iapply Hacc
    iexact He

end defs

/-! ## `watchOkL` reads only the events and the failure of the output -/

theorem watchOkL_out (x : Input) (y y' : Output) (h : HSt) (he : y.WEvents' = y'.WEvents')
    (hf : y.WFailed' = y'.WFailed') : watchOkL x y h = watchOkL x y' h := by
  unfold watchOkL; rw [he, hf]

/-- A well-formed state is its history's (its store the history's last). -/
theorem HWf_eq {H H' : HSt} (h : HWf H) (h' : HWf H') (e : H.hist = H'.hist) : H = H' := by
  obtain ⟨_, h1⟩ := h; obtain ⟨_, h2⟩ := h'
  rw [e, h2] at h1
  cases H; cases H'; cases e; simp_all

end k8s_etcd3
end EtcdGrove
end Perennial
