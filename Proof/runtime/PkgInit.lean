/-
Package initialization that keeps what is initialized (decision D19e, 2026-10-18).

Perennial's `wp_package_init` hides the package-state map in `ownInitializing g` (`∃ σ,
ownGoState σ ∗ □ ...`), and every package's `wp_initialize'` returns an arbitrary map: after
a call, a proof no longer knows that a package initialized before is still initialized. So a
resource only a package's first initialization needs (the read package's registration rights,
D16) is needed by every theorem that might run it, and a program importing two packages that
lead to it needs it twice. Here, from Perennial's own instructions (`wp_PackageInitCheck`,
`Start`, `Finish`; `ownInitializing_unseal`):

* `ownInitLb g σ0`: `ownInitializing g` whose map has every package `σ0` has initialized
  initialized (`initLe σ0 σ`). A package's `wp_initialize'_lb` keeps it for every `σ0`:
  initializing a package only ever initializes more (`wp_package_init_lb`).
* `ownInitRes g q R`: `ownInitializing g` that also holds `R` unless the map has `q`
  initialized. `q`'s initializer takes `R` the one time it runs (`wp_package_init_res_self`);
  every other package's initializer passes it on (`wp_package_init_res`, `initRes_carry` for an
  import whose closure does not contain `q`, by its `_lb` form). So `R` is given once, to the
  first initializer that leads to `q`, and the later ones find `q` initialized.

The standard forms follow (`wp_init_of_lb`, `wp_init_of_res`). The general fix, which would
make this file unnecessary, is a Perennial change (`notes/decisions.md`, D19e).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- Every package initialized in `σ0` is initialized in `σ`. -/
def initLe (σ0 σ : GMap GoString Bool) : Prop :=
  ∀ p, σ0 !! p = some true → σ !! p = some true

theorem initLe_refl (σ : GMap GoString Bool) : initLe σ σ := fun _ h => h

theorem initLe_empty (σ : GMap GoString Bool) : initLe ∅ σ := by
  intro p h; simp at h

/-- Starting a package not initialized keeps the initialized ones. -/
theorem initLe_start {σ0 σ : GMap GoString Bool} {p : GoString} (h : initLe σ0 σ)
    (hσ : (σ !! p).getD false = false) : initLe σ0 (<[p := false]> σ) := by
  intro q hq
  have := h q hq
  simp only [GMap.lookup_insert_eq_iff]
  split
  · subst_vars; simp [this] at hσ
  · exact this

theorem initLe_finish {σ0 σ : GMap GoString Bool} (p : GoString) (h : initLe σ0 σ) :
    initLe σ0 (<[p := true]> σ) := by
  intro q hq
  simp only [GMap.lookup_insert_eq_iff]
  split
  · rfl
  · exact h q hq

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The packages initialized in `σ` have their facts (`ownInitializing`'s persistent part). -/
def initsOk (g : GoString → IProp GF) (σ : GMap GoString Bool) : IProp GF :=
  iprop([∗map] p ↦ b ∈ σ, if b then g p else iprop(True))

/-- `ownInitializing g`, its map having every package `σ0` has initialized initialized. -/
def ownInitLb (g : GoString → IProp GF) (σ0 : GMap GoString Bool) : IProp GF :=
  iprop(∃ σ, ownGoState σ ∗ □ initsOk g σ ∗ ⌜initLe σ0 σ⌝)

/-- `R`, unless the package `q` is initialized in `σ`. -/
def initRes (q : GoString) (R : IProp GF) (σ : GMap GoString Bool) : IProp GF :=
  if σ !! q = some true then iprop(True) else R

/-- `ownInitializing g` with `R`, unless the package `q` is initialized. -/
def ownInitRes (g : GoString → IProp GF) (q : GoString) (R : IProp GF) : IProp GF :=
  iprop(∃ σ, ownGoState σ ∗ □ initsOk g σ ∗ initRes q R σ)

theorem ownInitializing_lb (g : GoString → IProp GF) :
    ownInitializing g ⊢ ownInitLb g ∅ := by
  rw [ownInitializing_unseal]
  unfold ownInitializingDef ownInitLb initsOk
  iintro ⟨%σ, Hg, #Hi⟩
  iexists σ
  iframe Hg
  isplitl []
  · imodintro; iexact Hi
  · ipureintro; exact initLe_empty σ

theorem ownInitLb_initializing (g : GoString → IProp GF) (σ0 : GMap GoString Bool) :
    ownInitLb g σ0 ⊢ ownInitializing g := by
  rw [ownInitializing_unseal]
  unfold ownInitializingDef ownInitLb initsOk
  iintro ⟨%σ, Hg, #Hi, -⟩
  iexists σ
  iframe Hg
  imodintro; iexact Hi

theorem ownInitializing_res (g : GoString → IProp GF) (q : GoString) (R : IProp GF) :
    ownInitializing g ∗ R ⊢ ownInitRes g q R := by
  rw [ownInitializing_unseal]
  unfold ownInitializingDef ownInitRes initsOk initRes
  iintro ⟨⟨%σ, Hg, #Hi⟩, HR⟩
  iexists σ
  iframe Hg
  isplitl []
  · imodintro; iexact Hi
  · split
    · itrivial
    · iexact HR

theorem ownInitRes_initializing (g : GoString → IProp GF) (q : GoString) (R : IProp GF) :
    ownInitRes g q R ⊢ ownInitializing g := by
  rw [ownInitializing_unseal]
  unfold ownInitializingDef ownInitRes initsOk
  iintro ⟨%σ, Hg, #Hi, -⟩
  iexists σ
  iframe Hg
  imodintro; iexact Hi

theorem initRes_mono (q : GoString) (R : IProp GF) {σ σ' : GMap GoString Bool}
    (h : initLe σ σ') : initRes q R σ ⊢ initRes q R σ' := by
  unfold initRes
  by_cases hq : σ !! q = some true
  · simp only [h q hq, ↓reduceIte]; iintro -; itrivial
  · simp only [hq, ↓reduceIte]
    split
    · iintro -; itrivial
    · iintro H; iexact H

theorem initRes_start (q : GoString) (R : IProp GF) {σ : GMap GoString Bool} {p : GoString}
    (hσ : (σ !! p).getD false = false) : initRes q R σ ⊢ initRes q R (<[p := false]> σ) := by
  unfold initRes
  have hq : ((<[p := false]> σ) !! q = some true) ↔ (σ !! q = some true) := by
    simp only [GMap.lookup_insert_eq_iff]
    split
    · subst_vars
      constructor
      · intro h; cases h
      · intro h; simp [h] at hσ
    · exact Iff.rfl
  by_cases h : σ !! q = some true
  · simp only [h, hq.2 h, ↓reduceIte]; exact .rfl
  · simp only [h, (show ¬ _ from fun h' => h (hq.1 h')), ↓reduceIte]; exact .rfl

theorem initRes_finish (q : GoString) (R : IProp GF) (σ : GMap GoString Bool) (p : GoString) :
    initRes q R σ ⊢ initRes q R (<[p := true]> σ) :=
  initRes_mono q R (initLe_finish p (initLe_refl σ))

end defs

section package_init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- Perennial's `wp_package_init`, keeping the initialized packages: from `ownInitLb g σ0`, the
body runs (if at all) from `ownInitLb g σ0` and returns it, and so does `package.init`. -/
theorem wp_package_init_lb (pkg_name : GoString) [PkgInfo pkg_name] (f x : Binder) (body : Expr)
    (get_is_pkg_init : GoString → IProp GF) (isPkgInit : IProp GF) (Φ : val → IProp GF)
    (σ0 : GMap GoString Bool) (heq : get_is_pkg_init pkg_name = isPkgInit) :
    let init_func := RecV f x body
    iprop(ownInitLb get_is_pkg_init σ0 ∗
      (ownInitLb get_is_pkg_init σ0 -∗
        WP (App (Val init_func) (Val #())) {{ v, ⌜v.isPanic = false⌝ ∗ □ isPkgInit ∗
          ownInitLb get_is_pkg_init σ0 }}))
    ⊢ iprop((ownInitLb get_is_pkg_init σ0 ∗ isPkgInit -∗ Φ #()) -∗
      WP (App (Val (package.init pkg_name)) (Val init_func)) {{ Φ }}) := by
  intro init_func
  have hinit : init_func.isPanic = false := rfl
  clear_value init_func
  subst heq
  rw [package.init_unseal]
  unfold ownInitLb initsOk
  iintro ⟨Hown, Hpre⟩ HΦ
  wp_call
  icases Hown with ⟨%σ, Hg, #Hinit, %Hle⟩
  wp_apply_core wp_PackageInitCheck pkg_name σ $$ Hg
  iintro Hg
  cases hσ : (σ !! pkg_name).getD false
  · wp_pures
    wp_apply_core wp_PackageInitStart pkg_name σ $$ Hg
    iintro Hg
    wp_pures
    ihave Hpre := Hpre $$ [Hg]
    · iexists (<[pkg_name := false]> σ)
      iframe Hg
      isplitl []
      · imodintro
        iapply BigSepM.bigSepM_insert_elim $$ [] Hinit
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      · ipureintro; exact initLe_start Hle hσ
    wp_apply_core wp_wand $$ Hpre
    iintro %_ ⟨%Hnp, #Hinitd, Hown⟩
    icases Hown with ⟨%σ', Hg, #Hinit', %Hle'⟩
    wp_pures
    wp_apply_core wp_PackageInitFinish pkg_name σ' $$ Hg
    iintro Hg
    iapply HΦ
    iframe Hinitd
    iexists (<[pkg_name := true]> σ')
    iframe Hg
    isplitl []
    · imodintro
      iapply BigSepM.bigSepM_insert_elim $$ [] Hinit'
      simp only [↓reduceIte]
      iexact Hinitd
    · ipureintro; exact initLe_finish pkg_name Hle'
  · wp_pures
    iapply HΦ
    cases hl : σ !! pkg_name with
    | none => simp [hl] at hσ
    | some b =>
      simp [hl] at hσ
      subst hσ
      ihave Hx := BigSepM.bigSepM_lookup (Φ := fun k (b : Bool) =>
        if b then get_is_pkg_init k else iprop(True)) hl $$ Hinit
      isplitl [Hg]
      · iexists σ
        iframe Hg
        isplitl []
        · imodintro; iexact Hinit
        · ipureintro; exact Hle
      · simp only [↓reduceIte]
        iexact Hx

/-- Perennial's `wp_package_init`, passing on `R` (held unless `q` is initialized): the body runs
(if at all) from `ownInitRes g q R` and returns it. For `pkg_name = q` too, but `q`'s own
initializer uses `wp_package_init_res_self`, which gives its body `R`. -/
theorem wp_package_init_res (pkg_name : GoString) [PkgInfo pkg_name] (f x : Binder) (body : Expr)
    (get_is_pkg_init : GoString → IProp GF) (isPkgInit : IProp GF) (Φ : val → IProp GF)
    (q : GoString) (R : IProp GF) (heq : get_is_pkg_init pkg_name = isPkgInit) :
    let init_func := RecV f x body
    iprop(ownInitRes get_is_pkg_init q R ∗
      (ownInitRes get_is_pkg_init q R -∗
        WP (App (Val init_func) (Val #())) {{ v, ⌜v.isPanic = false⌝ ∗ □ isPkgInit ∗
          ownInitRes get_is_pkg_init q R }}))
    ⊢ iprop((ownInitRes get_is_pkg_init q R ∗ isPkgInit -∗ Φ #()) -∗
      WP (App (Val (package.init pkg_name)) (Val init_func)) {{ Φ }}) := by
  intro init_func
  have hinit : init_func.isPanic = false := rfl
  clear_value init_func
  subst heq
  rw [package.init_unseal]
  unfold ownInitRes initsOk
  iintro ⟨Hown, Hpre⟩ HΦ
  wp_call
  icases Hown with ⟨%σ, Hg, #Hinit, HR⟩
  wp_apply_core wp_PackageInitCheck pkg_name σ $$ Hg
  iintro Hg
  cases hσ : (σ !! pkg_name).getD false
  · wp_pures
    wp_apply_core wp_PackageInitStart pkg_name σ $$ Hg
    iintro Hg
    wp_pures
    ihave Hpre := Hpre $$ [Hg HR]
    · iexists (<[pkg_name := false]> σ)
      iframe Hg
      isplitl []
      · imodintro
        iapply BigSepM.bigSepM_insert_elim $$ [] Hinit
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      · iapply (initRes_start q R hσ) $$ HR
    wp_apply_core wp_wand $$ Hpre
    iintro %_ ⟨%Hnp, #Hinitd, Hown⟩
    icases Hown with ⟨%σ', Hg, #Hinit', HR⟩
    wp_pures
    wp_apply_core wp_PackageInitFinish pkg_name σ' $$ Hg
    iintro Hg
    iapply HΦ
    iframe Hinitd
    iexists (<[pkg_name := true]> σ')
    iframe Hg
    isplitl []
    · imodintro
      iapply BigSepM.bigSepM_insert_elim $$ [] Hinit'
      simp only [↓reduceIte]
      iexact Hinitd
    · iapply (initRes_finish q R σ' pkg_name) $$ HR
  · wp_pures
    iapply HΦ
    cases hl : σ !! pkg_name with
    | none => simp [hl] at hσ
    | some b =>
      simp [hl] at hσ
      subst hσ
      ihave Hx := BigSepM.bigSepM_lookup (Φ := fun k (b : Bool) =>
        if b then get_is_pkg_init k else iprop(True)) hl $$ Hinit
      isplitl [Hg HR]
      · iexists σ
        iframe Hg HR
        imodintro; iexact Hinit
      · simp only [↓reduceIte]
        iexact Hx

/-- The initializer of the package `q` itself: its body runs (if at all) from
`ownInitializing g ∗ R` (`q` is not initialized, so `R` is held) and spends `R`; afterwards `q`
is initialized, and `ownInitRes g q R` holds without it. -/
theorem wp_package_init_res_self (pkg_name : GoString) [PkgInfo pkg_name] (f x : Binder)
    (body : Expr) (get_is_pkg_init : GoString → IProp GF) (isPkgInit : IProp GF)
    (Φ : val → IProp GF) (R : IProp GF) (heq : get_is_pkg_init pkg_name = isPkgInit) :
    let init_func := RecV f x body
    iprop(ownInitRes get_is_pkg_init pkg_name R ∗
      (ownInitializing get_is_pkg_init ∗ R -∗
        WP (App (Val init_func) (Val #())) {{ v, ⌜v.isPanic = false⌝ ∗ □ isPkgInit ∗
          ownInitializing get_is_pkg_init }}))
    ⊢ iprop((ownInitRes get_is_pkg_init pkg_name R ∗ isPkgInit -∗ Φ #()) -∗
      WP (App (Val (package.init pkg_name)) (Val init_func)) {{ Φ }}) := by
  intro init_func
  have hinit : init_func.isPanic = false := rfl
  clear_value init_func
  subst heq
  rw [package.init_unseal]
  unfold ownInitRes initsOk
  iintro ⟨Hown, Hpre⟩ HΦ
  wp_call
  icases Hown with ⟨%σ, Hg, #Hinit, HR⟩
  wp_apply_core wp_PackageInitCheck pkg_name σ $$ Hg
  iintro Hg
  cases hσ : (σ !! pkg_name).getD false
  · wp_pures
    wp_apply_core wp_PackageInitStart pkg_name σ $$ Hg
    iintro Hg
    wp_pures
    have hn : ¬ σ !! pkg_name = some true := by intro h; simp [h] at hσ
    unfold initRes
    simp only [hn, ↓reduceIte]
    ihave Hpre := Hpre $$ [Hg HR]
    · iframe HR
      rw [ownInitializing_unseal]
      unfold ownInitializingDef
      iexists (<[pkg_name := false]> σ)
      iframe Hg
      imodintro
      iapply BigSepM.bigSepM_insert_elim $$ [] Hinit
      simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
    wp_apply_core wp_wand $$ Hpre
    iintro %_ ⟨%Hnp, #Hinitd, Hown⟩
    rw [ownInitializing_unseal]
    unfold ownInitializingDef
    icases Hown with ⟨%σ', Hg, #Hinit'⟩
    wp_pures
    wp_apply_core wp_PackageInitFinish pkg_name σ' $$ Hg
    iintro Hg
    iapply HΦ
    iframe Hinitd
    iexists (<[pkg_name := true]> σ')
    iframe Hg
    isplitl []
    · imodintro
      iapply BigSepM.bigSepM_insert_elim $$ [] Hinit'
      simp only [↓reduceIte]
      iexact Hinitd
    · simp only [GMap.lookup_insert_eq_iff, ↓reduceIte]
      itrivial
  · wp_pures
    iapply HΦ
    cases hl : σ !! pkg_name with
    | none => simp [hl] at hσ
    | some b =>
      simp [hl] at hσ
      subst hσ
      ihave Hx := BigSepM.bigSepM_lookup (Φ := fun k (b : Bool) =>
        if b then get_is_pkg_init k else iprop(True)) hl $$ Hinit
      isplitl [Hg HR]
      · iexists σ
        iframe Hg HR
        imodintro; iexact Hinit
      · simp only [↓reduceIte]
        iexact Hx

/-- An import that keeps the initialized packages (its `_lb` form) passes `R` on. -/
theorem initRes_carry (get_is_pkg_init : GoString → IProp GF) (q : GoString) (R : IProp GF)
    (v : val) (Q : IProp GF)
    (H : ∀ σ0, {{ ownInitLb get_is_pkg_init σ0 }} (App (Val v) (Val #()))
      {{ RET #(); ownInitLb get_is_pkg_init σ0 ∗ Q }}) :
    {{ ownInitRes get_is_pkg_init q R }} (App (Val v) (Val #()))
      {{ RET #(); ownInitRes get_is_pkg_init q R ∗ Q }} := by
  iintro %Φ Hown HΦ
  unfold ownInitRes
  icases Hown with ⟨%σ, Hg, #Hi, HR⟩
  iapply H σ $$ [Hg]
  · unfold ownInitLb
    iexists σ
    iframe Hg
    isplitl []
    · imodintro; iexact Hi
    · ipureintro; exact initLe_refl σ
  inext
  iintro ⟨Hown, HQ⟩
  unfold ownInitLb
  icases Hown with ⟨%σ', Hg, #Hi', %Hle⟩
  iapply HΦ
  iframe HQ
  iexists σ'
  iframe Hg
  isplitl []
  · imodintro; iexact Hi'
  · iapply (initRes_mono q R Hle) $$ HR

/-- The standard form from the `_lb` form. -/
theorem wp_init_of_lb (get_is_pkg_init : GoString → IProp GF) (v : val) (Q : IProp GF)
    (H : ∀ σ0, {{ ownInitLb get_is_pkg_init σ0 }} (App (Val v) (Val #()))
      {{ RET #(); ownInitLb get_is_pkg_init σ0 ∗ Q }}) :
    {{ ownInitializing get_is_pkg_init }} (App (Val v) (Val #()))
      {{ RET #(); ownInitializing get_is_pkg_init ∗ Q }} := by
  iintro %Φ Hown HΦ
  iapply H ∅ $$ [Hown]
  · iapply (ownInitializing_lb get_is_pkg_init) $$ Hown
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply (ownInitLb_initializing get_is_pkg_init ∅) $$ Hown

/-- The standard form with the resource (D16's) from the `_res` form. -/
theorem wp_init_of_res (get_is_pkg_init : GoString → IProp GF) (q : GoString) (R : IProp GF)
    (v : val) (Q : IProp GF)
    (H : {{ ownInitRes get_is_pkg_init q R }} (App (Val v) (Val #()))
      {{ RET #(); ownInitRes get_is_pkg_init q R ∗ Q }}) :
    {{ ownInitializing get_is_pkg_init ∗ R }} (App (Val v) (Val #()))
      {{ RET #(); ownInitializing get_is_pkg_init ∗ Q }} := by
  iintro %Φ Hown HΦ
  iapply H $$ [Hown]
  · iapply (ownInitializing_res get_is_pkg_init q R) $$ Hown
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply (ownInitRes_initializing get_is_pkg_init q R) $$ Hown

end package_init

end EtcdGrove
end Perennial
