/-
Package initialization with several packages' resources (mustreg, 2026-11-20): the list form of
`PkgInit.lean`'s `ownInitRes` (decision D19e), for programs whose import closure has several
packages whose initializers need a resource (`etc/gen-init.py`'s `PRE_RES`: each package whose
`init()` registers metrics with prometheus's default registry takes the right to register their
names, `prometheus.nameFree`, decision D16).

* `ownInitResL g L`: `ownInitializing g` with, for each `(q, R)` of `L`, `R` unless the package
  `q` is initialized. A package's initializer passes the list on (`wp_package_init_resL`), or, if
  its own entry is in it, takes its `R` the one time it runs (`wp_package_init_resL_self`).
* An import whose closure has only some of the list's packages (`Lx`, a sublist of `L`) passes
  the rest on unchanged (`initResL_sub`): whatever the import initializes, the packages initialized
  before stay initialized (Perennial's monotone package map, `ownGoStateLb`), so the resources held
  for them stay held. An import with none of them uses its `_lb` form (`initResL_carry`).
* `regResL qs`: the list of `(q, namesFree Ns)` of the packages `qs` with their metric names, and
  `wp_init_of_regResL`, the standard form whose precondition is `namesFree` of all the names.

(`ownInitRes`, the one-package form, is what this generalizes; it is left in `PkgInit.lean`,
unused since, because removing it would rebuild every module.)
-/
module

public import Proof.runtime.PkgInit
public import Proof.github_com.prometheus.client_golang.prometheus.Registry

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section names
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The rights to register the names `Ns`** with prometheus's default registry: `regFree` of
each (D16; prom-registry, 2026-11-22: until then the axiom `nameFree` of each). -/
def prometheus.namesFree (Ns : List GoString) : IProp GF :=
  iprop([∗list] n ∈ Ns, prometheus.regFree n)

end names

theorem pkgInitLe_initLe {σ0 σ : GMap GoString Bool} (h : pkgInitLe σ0 σ) : initLe σ0 σ := h

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- Each `(q, R)` of `L`: `R` unless the package `q` is initialized in `σ`. -/
def initResL (L : List (GoString × IProp GF)) (σ : GMap GoString Bool) : IProp GF :=
  iprop([∗list] e ∈ L, initRes e.1 e.2 σ)

/-- `ownInitializing g` with each resource of `L` held unless its package is initialized. -/
def ownInitResL (g : GoString → IProp GF) (L : List (GoString × IProp GF)) : IProp GF :=
  iprop(∃ σ, ownGoState σ ∗ □ initsOk g σ ∗ initResL L σ)

/-- The packages `qs` with their metric names, each with the rights to register its names. -/
def regResL (qs : List (GoString × List GoString)) : List (GoString × IProp GF) :=
  qs.map (fun e => (e.1, prometheus.namesFree e.2))

theorem initResL_mono (L : List (GoString × IProp GF)) {σ σ' : GMap GoString Bool}
    (h : initLe σ σ') : initResL L σ ⊢ initResL L σ' := by
  unfold initResL
  exact BigSepL.bigSepL_mono_of_forall (fun {_ e} => initRes_mono e.1 e.2 h)

theorem initResL_start (L : List (GoString × IProp GF)) {σ : GMap GoString Bool} {p : GoString}
    (hσ : (σ !! p).getD false = false) : initResL L σ ⊢ initResL L (<[p := false]> σ) := by
  unfold initResL
  exact BigSepL.bigSepL_mono_of_forall (fun {_ e} => initRes_start e.1 e.2 hσ)

theorem initResL_app (L1 L2 : List (GoString × IProp GF)) (σ : GMap GoString Bool) :
    initResL (L1 ++ L2) σ ⊣⊢ initResL L1 σ ∗ initResL L2 σ := by
  unfold initResL
  exact BigSepL.bigSepL_append

theorem initResL_perm {L1 L2 : List (GoString × IProp GF)} (hp : L1.Perm L2)
    (σ : GMap GoString Bool) : initResL L1 σ ⊣⊢ initResL L2 σ := by
  unfold initResL
  exact BigSepL.bigSepL_perm hp

/-- The entry of a package that is initialized holds nothing. -/
theorem initRes_inited (q : GoString) (R : IProp GF) {σ : GMap GoString Bool}
    (h : σ !! q = some true) : ⊢ initRes q R σ := by
  unfold initRes
  simp only [h, ↓reduceIte]
  iintro
  itrivial

/-- The entry of a package that is not initialized is its resource. -/
theorem initRes_not_inited (q : GoString) (R : IProp GF) {σ : GMap GoString Bool}
    (h : ¬ σ !! q = some true) : initRes q R σ ⊣⊢ R := by
  unfold initRes
  simp only [h, ↓reduceIte]
  exact .rfl

end defs

section package_init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- Perennial's `wp_package_init`, passing on the resources `L`: the body runs (if at all) from
`ownInitResL g L` and returns it. -/
theorem wp_package_init_resL (pkg_name : GoString) [PkgInfo pkg_name] (f x : Binder) (body : Expr)
    (get_is_pkg_init : GoString → IProp GF) (isPkgInit : IProp GF) (Φ : val → IProp GF)
    (L : List (GoString × IProp GF)) (heq : get_is_pkg_init pkg_name = isPkgInit) :
    let init_func := RecV f x body
    iprop(ownInitResL get_is_pkg_init L ∗
      (ownInitResL get_is_pkg_init L -∗
        WP (App (Val init_func) (Val #())) {{ v, ⌜v.isPanic = false⌝ ∗ □ isPkgInit ∗
          ownInitResL get_is_pkg_init L }}))
    ⊢ iprop((ownInitResL get_is_pkg_init L ∗ isPkgInit -∗ Φ #()) -∗
      WP (App (Val (package.init pkg_name)) (Val init_func)) {{ Φ }}) := by
  intro init_func
  have hinit : init_func.isPanic = false := rfl
  clear_value init_func
  subst heq
  rw [package.init_unseal]
  unfold ownInitResL initsOk
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
      · iapply (initResL_start L hσ) $$ HR
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
    · iapply (initResL_mono L (initLe_finish pkg_name (initLe_refl σ'))) $$ HR
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

/-- The initializer of a package whose own entry `(pkg_name, R)` is in the list
(`L = L1 ++ (pkg_name, R) :: L2`): its body runs (if at all) from `ownInitResL g L' ∗ R`
(`L' = L1 ++ L2`)
(the package is not initialized, so `R` is held) and spends `R`; afterwards the package is
initialized, and its entry holds nothing. -/
theorem wp_package_init_resL_self (pkg_name : GoString) [PkgInfo pkg_name] (f x : Binder)
    (body : Expr) (get_is_pkg_init : GoString → IProp GF) (isPkgInit : IProp GF)
    (Φ : val → IProp GF) (L L1 L2 L' : List (GoString × IProp GF)) (R : IProp GF)
    (hL : L = L1 ++ (pkg_name, R) :: L2) (hL' : L' = L1 ++ L2)
    (heq : get_is_pkg_init pkg_name = isPkgInit) :
    let init_func := RecV f x body
    iprop(ownInitResL get_is_pkg_init L ∗
      (ownInitResL get_is_pkg_init L' ∗ R -∗
        WP (App (Val init_func) (Val #())) {{ v, ⌜v.isPanic = false⌝ ∗ □ isPkgInit ∗
          ownInitResL get_is_pkg_init L' }}))
    ⊢ iprop((ownInitResL get_is_pkg_init L ∗ isPkgInit -∗ Φ #()) -∗
      WP (App (Val (package.init pkg_name)) (Val init_func)) {{ Φ }}) := by
  intro init_func
  have hinit : init_func.isPanic = false := rfl
  clear_value init_func
  subst heq hL hL'
  rw [package.init_unseal]
  unfold ownInitResL initsOk
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
    ihave ⟨H1, H2⟩ := (initResL_app L1 ((pkg_name, R) :: L2) σ).1 $$ HR
    iunfold initResL at H2
    icases H2 with ⟨Hp, H2⟩
    ihave Hp := (initRes_not_inited pkg_name R hn).1 $$ Hp
    ihave Hpre := Hpre $$ [Hg H1 H2 Hp]
    · iframe Hp
      iexists (<[pkg_name := false]> σ)
      iframe Hg
      isplitl []
      · imodintro
        iapply BigSepM.bigSepM_insert_elim $$ [] Hinit
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      · iapply (initResL_start (L1 ++ L2) hσ)
        iapply (initResL_app L1 L2 σ).2
        iframe H1
        iunfold initResL
        iexact H2
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
    · ihave HR := (initResL_mono (L1 ++ L2) (initLe_finish pkg_name (initLe_refl σ'))) $$ HR
      ihave ⟨H1, H2⟩ := (initResL_app L1 L2 _).1 $$ HR
      iapply (initResL_app L1 ((pkg_name, R) :: L2) _).2
      iframe H1
      iunfold initResL
      iunfold initResL at H2
      iapply BigSepL.bigSepL_cons.2
      isplitl []
      · iapply (initRes_inited pkg_name R (σ := <[pkg_name := true]> σ') (by simp))
      · iexact H2
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

/-- An import whose closure has none of the list's packages (its `_lb` form) passes the list on. -/
theorem initResL_carry (get_is_pkg_init : GoString → IProp GF) (L : List (GoString × IProp GF))
    (v : val) (Q : IProp GF)
    (H : ∀ σ0, {{ ownInitLb get_is_pkg_init σ0 }} (App (Val v) (Val #()))
      {{ RET #(); ownInitLb get_is_pkg_init σ0 ∗ Q }}) :
    {{ ownInitResL get_is_pkg_init L }} (App (Val v) (Val #()))
      {{ RET #(); ownInitResL get_is_pkg_init L ∗ Q }} := by
  iintro %Φ Hown HΦ
  unfold ownInitResL
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
  · iapply (initResL_mono L Hle) $$ HR

/-- An import whose closure has the packages of `Lx`, a sublist of `L`, passes on the others: what
it initializes, the packages initialized before stay initialized (`ownGoStateLb`). -/
theorem initResL_sub (get_is_pkg_init : GoString → IProp GF) (L Lx : List (GoString × IProp GF))
    (hs : Lx.Sublist L) (v : val) (Q : IProp GF)
    (H : {{ ownInitResL get_is_pkg_init Lx }} (App (Val v) (Val #()))
      {{ RET #(); ownInitResL get_is_pkg_init Lx ∗ Q }}) :
    {{ ownInitResL get_is_pkg_init L }} (App (Val v) (Val #()))
      {{ RET #(); ownInitResL get_is_pkg_init L ∗ Q }} := by
  obtain ⟨Lr, hp⟩ := hs.exists_perm_append
  iintro %Φ Hown HΦ
  unfold ownInitResL
  icases Hown with ⟨%σ, Hg, #Hi, HR⟩
  ihave ⟨Hg, #Hlb⟩ := ownGoState_get_lb σ $$ Hg
  ihave HR := (initResL_perm hp σ).1 $$ HR
  ihave ⟨Hx, Hr⟩ := (initResL_app Lx Lr σ).1 $$ HR
  iapply H $$ [Hg Hx]
  · iunfold ownInitResL
    iexists σ
    iframe Hg Hx
    imodintro; iexact Hi
  inext
  iintro ⟨Hown, HQ⟩
  iunfold ownInitResL at Hown
  icases Hown with ⟨%σ', Hg, #Hi', Hx⟩
  ihave %Hle := ownGoStateLb_le σ σ' $$ Hlb Hg
  iapply HΦ
  iframe HQ
  iexists σ'
  iframe Hg
  isplitl []
  · imodintro; iexact Hi'
  · iapply (initResL_perm hp σ').2
    iapply (initResL_app Lx Lr σ').2
    iframe Hx
    iapply (initResL_mono Lr (pkgInitLe_initLe Hle)) $$ Hr

/-- The standard form from the list form, its precondition `R` giving every resource of `L`. -/
theorem wp_init_of_resL (get_is_pkg_init : GoString → IProp GF) (L : List (GoString × IProp GF))
    (R : IProp GF) (hR : R ⊢ [∗list] e ∈ L, e.2) (v : val) (Q : IProp GF)
    (H : {{ ownInitResL get_is_pkg_init L }} (App (Val v) (Val #()))
      {{ RET #(); ownInitResL get_is_pkg_init L ∗ Q }}) :
    {{ ownInitializing get_is_pkg_init ∗ R }} (App (Val v) (Val #()))
      {{ RET #(); ownInitializing get_is_pkg_init ∗ Q }} := by
  iintro %Φ ⟨Hown, HR⟩ HΦ
  ihave HR := hR $$ HR
  rw [ownInitializing_unseal]
  unfold ownInitializingDef
  icases Hown with ⟨%σ, Hg, #Hi⟩
  iapply H $$ [Hg HR]
  · unfold ownInitResL initsOk
    iexists σ
    iframe Hg
    isplitl []
    · imodintro; iexact Hi
    · unfold initResL
      iapply BigSepL.bigSepL_mono_of_forall (fun {_ e} => ?_) $$ HR
      unfold initRes
      split
      · iintro -; itrivial
      · iintro H; iexact H
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  unfold ownInitResL initsOk
  icases Hown with ⟨%σ', Hg, #Hi', -⟩
  iexists σ'
  iframe Hg
  imodintro; iexact Hi'

/-- `namesFree` of the names of the packages `qs` gives each package's (`regResL qs`). -/
theorem namesFree_regResL (qs : List (GoString × List GoString)) :
    prometheus.namesFree (GF := GF) (qs.flatMap (·.2)) ⊢ [∗list] e ∈ regResL (GF := GF) qs, e.2 := by
  induction qs with
  | nil => unfold regResL; exact BigSepL.bigSepL_nil_intro
  | cons e qs ih =>
    unfold regResL prometheus.namesFree
    simp only [List.flatMap_cons, List.map_cons]
    iintro H
    ihave ⟨H1, H2⟩ := BigSepL.bigSepL_append.1 $$ H
    iapply BigSepL.bigSepL_cons.2
    iframe H1
    unfold regResL prometheus.namesFree at ih
    iapply ih $$ H2

/-- The standard form whose precondition is the rights to register every name of `qs`
(`etc/gen-init.py`'s `wp_initialize'` of a package with registering packages in its closure). -/
theorem wp_init_of_regResL (get_is_pkg_init : GoString → IProp GF)
    (qs : List (GoString × List GoString)) (v : val) (Q : IProp GF)
    (H : {{ ownInitResL get_is_pkg_init (regResL qs) }} (App (Val v) (Val #()))
      {{ RET #(); ownInitResL get_is_pkg_init (regResL qs) ∗ Q }}) :
    {{ ownInitializing get_is_pkg_init ∗ prometheus.namesFree (qs.flatMap (·.2)) }}
      (App (Val v) (Val #()))
      {{ RET #(); ownInitializing get_is_pkg_init ∗ Q }} :=
  wp_init_of_resL get_is_pkg_init _ _ (namesFree_regResL qs) v Q H

end package_init

end EtcdGrove
end Perennial
