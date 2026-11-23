/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/InitFirst.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
A package's initialization the first time it runs (change log C14, decision D9 (a')): a local
variant of Perennial's `wp_package_init` (Perennial/Golang/Theory/Pkg.lean) whose initializer
body may hand its caller a resource `Q` (not only the persistent post-init predicate).

"Not yet initialized" is said with the `get_is_pkg_init` map itself: `ownInitializing gA` with
`gA pkg ⊢ False` (the map of initialized packages keeps, for each initialized package, `gA` of
it: so `pkg` is not initialized). The body runs with `ownInitializing gB` for any `gB` weaker
than `gA` pointwise (`pkg` itself is "initializing", its entry `True`), and ends with
`ownInitializing gC`, `gC pkg` being the package's post-init predicate.
-/
module

public import Perennial.Golang.Theory.Pkg

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std

noncomputable section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- `ownInitializing` is monotone in the post-init map. -/
theorem ownInitializing_mono (g1 g2 : GoString → IProp GF) (h : ∀ p, g1 p ⊢ g2 p) :
    ownInitializing g1 ⊢ ownInitializing g2 := by
  rw [ownInitializing_unseal]
  unfold ownInitializingDef
  have hm : ∀ σ : GMap GoString Bool,
      ([∗map] pkg_name ↦ inited ∈ σ, if inited then g1 pkg_name else iprop(True)) ⊢
      ([∗map] pkg_name ↦ inited ∈ σ, if inited then g2 pkg_name else iprop(True)) := by
    intro σ
    refine BigSepM.bigSepM_mono_of_forall (fun {k b} => ?_)
    cases b
    · exact .rfl
    · exact h k
  iintro ⟨%σ, Hg, #Hinit⟩
  iexists σ
  iframe Hg
  imodintro
  iapply hm $$ Hinit

variable [GoSemanticsFunctions] [go.PreSemantics]

/-- **The first initialization of a package** (see the file header): its body may return a
resource `Q` to the caller. -/
theorem wp_package_init_first (pkg_name : GoString) [PkgInfo pkg_name] (f x : Binder)
    (body : Expr) (gA gB gC : GoString → IProp GF) (P Q : IProp GF) (Φ : val → IProp GF)
    (hA : gA pkg_name ⊢ iprop(False)) (hAB : ∀ p, gA p ⊢ gB p) (heq : gC pkg_name = P) :
    let init_func := RecV f x body
    iprop(ownInitializing gA ∗
      (ownInitializing gB -∗
        WP (App (Val init_func) (Val #())) {{ v, Q ∗ ⌜v.isPanic = false⌝ ∗ □ P ∗
          ownInitializing gC }}))
    ⊢ iprop((ownInitializing gC ∗ P ∗ Q -∗ Φ #()) -∗
      WP (App (Val (package.init pkg_name)) (Val init_func)) {{ Φ }}) := by
  intro init_func
  have hinit : init_func.isPanic = false := rfl
  clear_value init_func
  subst heq
  rw [ownInitializing_unseal, package.init_unseal]
  unfold ownInitializingDef
  iintro ⟨Hown, Hpre⟩ HΦ
  wp_call
  icases Hown with ⟨%σ, Hg, #Hinit⟩
  wp_apply_core wp_PackageInitCheck pkg_name σ $$ Hg
  iintro Hg
  cases hσ : (σ !! pkg_name).getD false
  · wp_pures
    wp_apply_core wp_PackageInitStart pkg_name σ $$ Hg
    iintro Hg
    wp_pures
    have hm : ([∗map] pkg_name ↦ inited ∈ σ, if inited then gA pkg_name else iprop(True)) ⊢
        ([∗map] pkg_name ↦ inited ∈ σ, if inited then gB pkg_name else iprop(True)) := by
      refine BigSepM.bigSepM_mono_of_forall (fun {k b} => ?_)
      cases b
      · exact .rfl
      · exact hAB k
    ihave Hpre := Hpre $$ [Hg]
    · iexists (<[pkg_name := false]> σ)
      iframe Hg
      imodintro
      iapply BigSepM.bigSepM_insert_elim $$ [] [Hinit]
      · simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      · iapply hm $$ Hinit
    wp_apply_core wp_wand $$ Hpre
    iintro %_ ⟨HQ, %Hnp, #Hinitd, Hown⟩
    icases Hown with ⟨%σ', Hg, #Hinit'⟩
    wp_pures
    wp_apply_core wp_PackageInitFinish pkg_name σ' $$ Hg
    iintro Hg
    iapply HΦ
    iframe Hinitd HQ
    iexists (<[pkg_name := true]> σ')
    iframe Hg
    imodintro
    iapply BigSepM.bigSepM_insert_elim $$ [] Hinit'
    simp only [↓reduceIte]
    iexact Hinitd
  · -- already initialized: `gA pkg_name` holds, which is `False`
    cases hl : σ !! pkg_name with
    | none => simp [hl] at hσ
    | some b =>
      simp [hl] at hσ
      subst hσ
      ihave Hx := BigSepM.bigSepM_lookup (Φ := fun k (b : Bool) =>
        if b then gA k else iprop(True)) hl $$ Hinit
      simp only [↓reduceIte]
      iexfalso
      iapply hA $$ Hx

end

end Perennial.github_com.imdea_software.swiftpaxos
