/- Lean-first (no Rocq counterpart).

# `prophkv`'s results

`wp_GetAny` (`Link.lean`): `GetAny`'s plain logically atomic spec (`Spec/.../prophkv/GetAny.lean`),
proved over a prophecy of its random choice that a **prophecy patch** adds to the Go code
(`etc/proph-patches/prophkv/01-getany-choice.patch`, applied before translation; the spec does not
mention it).

`goose_prophkv_safe`: the closed theorem about the program (the package's initialization, then `Test()`)
**as translated from the patched code**: in every real execution from a fresh state with one
thread, the result is `"a"` or `"b"`, no thread is stuck and none has an unrecovered panic. It
follows from Perennial's `goose_adequacy` alone: the program runs its prophecy operations like any
other step, so no erasure theorem and no premise about the Go model are needed. That it covers
the Go code without the patch is the patch's argument, checked by `etc/prophcheck` (the patch
only adds prophecy statements, which do nothing in Go; `notes/decisions.md`, "Prophecies as
patches of the Go code").

The package's initialization is proved here directly (`wp_initialize'_direct`: its one import,
`primitive`, by Perennial's `wp_initialize'`), not through the generated `Init.lean`, whose
`_lb` form goes through the trust-boundary axiom `EtcdGrove.initLb_of_spec`: the closed theorem
rests on the standard axioms only (`#print axioms` below).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Perennial.GooseLang.CrashLang

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace goose_prophkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.goose.prophkv

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

/-! ## The ghost-state bundle -/

/-- The functors: the universal camera (`AllG`) at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state; slot 7 also holds the map's abstract state (a
ghost variable of `GMap GoString GoString` comes from the universal camera). -/
def prophkvGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0. -/
def prophkvGF_allG : AllG prophkvGF := ⟨⟨0, rfl⟩⟩

instance prophkvGF_gooseGpreS : GooseGpreS prophkvGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨prophkvGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := prophkvGF_allG

/-! ## The program -/

section program
variable [go_gctx : GoGlobalContext]

/-- The program: initialize the package, then call `Test` (as goose calls a function). -/
def prog : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Test []))) (Val #())) (Val #()))

/-- What the program returns: `"a"` or `"b"`. -/
def resultOk (v : val) : Prop := v = #go!"a" ∨ v = #go!"b"

/-- The `get_is_pkg_init` of the program: the package and `primitive`. -/
def getIsPkgInit {GF : BundledGFunctors} [HeapGS .hasLC GF] (p : GoString) : IProp GF :=
  if p = pkg_id.github_com.mit_pdos.etcd_grove.examples.goose.prophkv then
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.goose.prophkv
  else if p = pkg_id.github_com.goose_lang.primitive then
    isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive
  else iprop(True)

section wp
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Assumptions]

/-- The package's initialization, from `primitive`'s (Perennial's `wp_initialize'`). -/
theorem wp_initialize'_direct (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.goose.prophkv
      get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.goose.prophkv }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hprim⟩
  iframe Hown
  is_pkg_init_finish

/-- **The program**: its result is `"a"` or `"b"`. -/
theorem wp_prog (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.goose.prophkv
      get_is_pkg_init) :
    ownInitializing get_is_pkg_init ⊢ WP prog {{ v, ⌜resultOk v⌝ }} := by
  iintro Hown
  unfold prog
  wp_apply wp_initialize'_direct _ Hinit $$ Hown as ⟨_, #Hpkg⟩
  wp_apply wp_Test as %r %Hg
  ipureintro
  rcases Hg with h | h <;> subst h <;> simp [resultOk]

end wp

/-! ## The closed theorem -/

/-- An execution of at most `n` steps from a single thread has fewer than `n + 2` live threads. -/
theorem realThreadsBelow_single {n : Nat} {ρ : List Expr × CfgState}
    (h1 : ρ.2.1.threads = 1) : RealThreadsBelow (n + 2) n ρ := by
  intro k κs ρ' hk h
  have := real_nsteps_threads h
  omega

/-- **The program's safety**: in every real execution of `prog` (translated from the
prophecy-patched code), from a state whose Go context satisfies the Go semantics and the
package's assumptions, with no package initialized and the main thread only, the program's result
is `"a"` or `"b"`, no thread is stuck and none has an unrecovered panic. -/
theorem goose_prophkv_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Assumptions]
    (σ : state) (g : GlobalState)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([prog], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → resultOk v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_adequacy (GF := prophkvGF) (n + 1) (n + 2) prog σ g resultOk ?_
    ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ?_ n κs t2 σ2 Hsteps (by omega) Hthreads
    (realThreadsBelow_single Hthreads)
  · intro p h
    rcases h with h | h <;> exact intoVal_ne_PanicV _ p h.symm
  · intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC prophkvGF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    have Hne : pkg_id.github_com.goose_lang.primitive ≠
        pkg_id.github_com.mit_pdos.etcd_grove.examples.goose.prophkv := by
      unfold pkg_id.github_com.goose_lang.primitive
        pkg_id.github_com.mit_pdos.etcd_grove.examples.goose.prophkv
      decide
    have Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.goose.prophkv
        (getIsPkgInit (GF := prophkvGF)) := by
      refine ⟨by simp [getIsPkgInit], ⟨by simp [getIsPkgInit, Hne], trivial⟩, trivial⟩
    rw [Hpkgs]
    iintro _ _ Hgs _
    imodintro
    iapply wp_prog getIsPkgInit Hinit
    rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro

end program

end goose_prophkv
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.goose_prophkv.wp_GetAny
#print axioms Perennial.EtcdGrove.goose_prophkv.goose_prophkv_safe
