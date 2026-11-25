/-
**Init-time invariants and hook cells** (dsv-retire-2, 2026-11-25; mit-pdos/etcd-grove#49 step 2):
the generic part of grpc's `internal` hook machinery (phase7-inits, 2026-11-25; the mechanism of
phase 7 S2 core's `FromOutRaw.lean`), which names no translation, so that every tree with a
translation of grpc's `internal` shares it: the main tree's (`cache/v3/Base.lean`'s `internalInit`,
`grpc/internal/Hooks.lean`'s `wp_store_hookAny`/`wp_store_hookFunc`) and the part `Dsverify/`'s
(`Dsverify/Proof/google_golang_org/grpc/internal/Base.lean`). Moved here from
`Proof/go_etcd_io/etcd/cache/v3/Base.lean` (`initInv`, `hookN`, `hookInv`, `hookCell`, `hookCells`)
and `Proof/google_golang_org/grpc/internal/Hooks.lean` (the laws), names and statements unchanged.

* `initInv R γI`: a resource `R` that only package initializers use, shared between packages.
* `hookCell V a`: a write-only cell `a` in an init-time invariant.
* `initInv_alloc`, `initInv_acc`: an init-time invariant, from its resource; with a package state,
  the resource out of the invariant, and back.
* `hookCell_alloc`, `hookCell_acc`, `hookCells_mem`: a freshly allocated cell gives its `hookCell`;
  with a package state, the cell out of the invariant, and back.
* `wp_store_hook`: a package initializer's store in a hook cell.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg
public import Proof.runtime.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.cache.v3

/-- **An init-time invariant** (phase7-inits, 2026-11-25; the mechanism of phase 7 S2 core's
`fromOutRawInv`): a resource `R` that only package initializers use, shared between packages (one
allocates it, others use it, and a package fact is persistent). Two states. *Held*: `R` and the whole of
the ghost variable `γI`. *Lent*: a package initializer's exclusive package state (`ownGoState σ`, the
program's half of the package map with the authority of the initialized packages) and half of `γI` at
`σ`. A package initializer, which holds its `ownGoState`, takes `R` out by lending its package state (so
no other holder of a package state can take it meanwhile: two `ownGoState`s conflict), uses it with plain
(non-atomic) steps, and puts it back, getting its own package state back (`γI`'s halves agree):
`initInv_acc`. -/
def initInv (R : IProp GF) (γI : GName) : IProp GF :=
  iprop((R ∗ ∃ x : GMap GoString Bool, ghost_var γI (DFrac.own 1) x) ∨
    (∃ σ : GMap GoString Bool, ownGoState σ ∗ ghost_var γI (DFrac.own (1 : Qp).half) σ))

namespace google_golang_org.grpc.internal

/-- The namespace of the hook cells' invariants. -/
def hookN : Namespace := nroot.@"grpcInternalHook"

/-- **A hook cell's invariant**: the cell `a`, with some value, in an init-time invariant (`initInv`).
The cell is another package's: `internal`'s initializer allocates it, the `init` of grpc, `codes`,
`metadata` or `health` writes it. -/
def hookInv (V : Type) [TypedPointsto (GF := GF) V] (a : Loc) (γI : GName) : IProp GF :=
  initInv iprop(∃ v : V, a ↦ v) γI

/-- A write-only hook cell: `a`'s invariant, at some ghost name. -/
def hookCell (V : Type) [TypedPointsto (GF := GF) V] (a : Loc) : IProp GF :=
  iprop(∃ γI : GName, inv hookN (hookInv V a γI))

/-- The hook cells of the variables `xs`, of Lean type `V`. -/
def hookCells (V : Type) [TypedPointsto (GF := GF) V] : List GoString → IProp GF
  | [] => iprop(True)
  | x :: xs => iprop(hookCell V (globalAddr x) ∗ hookCells V xs)

instance hookCells_persistent (V : Type) [TypedPointsto (GF := GF) V] (xs : List GoString) :
    Persistent (hookCells (GF := GF) V xs) := by
  induction xs with
  | nil => unfold hookCells; infer_instance
  | cons x xs ih => unfold hookCells hookCell; infer_instance

end google_golang_org.grpc.internal

end go_etcd_io.etcd.cache.v3

end defs

namespace EtcdGrove
namespace grpcInternal

open _root_.Perennial.go_etcd_io.etcd.cache.v3 (initInv)
open _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal
  (hookN hookInv hookCell hookCells)

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

instance hookCell_persistent {V : Type} [TypedPointsto (GF := GF) V] (a : Loc) :
    Persistent (hookCell (hG := hG) V a) := by
  unfold hookCell; infer_instance

/-- Two package states conflict (each holds the authority of the initialized packages). -/
theorem ownGoState_excl (σ σ' : GMap GoString Bool) :
    ⊢ ownGoState (GF := GF) σ -∗ ownGoState σ' -∗ False := by
  unfold ownGoState
  iintro ⟨-, Ha, -⟩ ⟨-, Ha', -⟩
  icases (letI := GoStateGS.package_mono_allG (GF := GF); ghostMapAuth_valid_2 (K := GoString) (V := Bool) _ _ _ _ _) $$ Ha Ha' with %H
  exfalso
  have Hq := H.1
  revert Hq
  rw [Qp.le_iff]; simp only [Qp.val_add, Qp.val_one]; grind

theorem half_add_half_own : (DFrac.own (1 : Qp)) = DFrac.own ((1 : Qp).half + (1 : Qp).half) := by
  rw [Qp.half_add_half]

/-- **A new init-time invariant**, from its resource. -/
theorem initInv_alloc (N : Namespace) (E : CoPset) (R : IProp GF) :
    ⊢ ▷ R ={E}=∗ ∃ γI : GName, inv N (initInv (hG := hG) R γI) := by
  iintro HR
  imod ghost_var_alloc (A := GMap GoString Bool) ∅ with ⟨%γI, HI⟩
  imod inv_alloc N E (initInv (hG := hG) R γI) $$ [HR HI] with #Hinv
  · inext
    unfold initInv
    ileft
    iframe HR
    iexists ∅
    iexact HI
  imodintro
  iexists γI
  iexact Hinv

/-- **Access to an init-time invariant's resource**, for a holder of a package state: `R`, until it
gives it back, which returns its package state. -/
theorem initInv_acc (N : Namespace) (E : CoPset) (hE : ↑N ⊆ E) (R : IProp GF) [Timeless R]
    (γI : GName) (σ : GMap GoString Bool) :
    ⊢ inv N (initInv (hG := hG) R γI) -∗ ownGoState σ ={E}=∗ R ∗ (R ={E}=∗ ownGoState σ) := by
  iintro #Hinv Hg
  -- take `R` out, lending the package state
  ihave Hhalf : |={E}=> R ∗ ghost_var γI (DFrac.own (1 : Qp).half) σ $$ [Hg]
  · iinv Hinv with Hi Hclose
    unfold initInv
    imod Hi with Hi
    icases Hi with (⟨HR, %x, HI⟩ | ⟨%σ', Hg', -⟩)
    · imod ghost_var_update σ γI x $$ HI with HI
      rw [half_add_half_own]
      ihave ⟨HI1, HI2⟩ := ghost_var_split γI σ _ _ $$ HI
      imod Hclose $$ [Hg HI1] with -
      · inext; iright; iexists σ; iframe Hg HI1
      imodintro
      iframe HR HI2
    · iexfalso
      iapply ownGoState_excl σ σ' $$ Hg Hg'
  imod Hhalf with ⟨HR, HI⟩
  imodintro
  iframe HR
  -- give it back, getting the package state back
  iintro HR
  iinv Hinv with Hi Hclose
  try unfold initInv
  imod Hi with Hi
  icases Hi with (⟨-, %x, HI0⟩ | ⟨%σ', Hg, HI'⟩)
  · icases ghost_var_valid_2 $$ HI0 HI with %H
    exfalso
    have := DFrac.valid_own_op H.1
    simp at this
  · icases ghost_var_agree $$ HI HI' with %Hσ
    subst Hσ
    icombine HI HI' as HI
    imod Hclose $$ [HR HI] with -
    · inext; ileft; iframe HR; iexists σ; iexact HI
    imodintro
    iexact Hg

/-- **A freshly allocated cell gives its hook cell.** -/
theorem hookCell_alloc {V : Type} [TypedPointsto (GF := GF) V] (E : CoPset) (a : Loc) (v : V) :
    ⊢ (a ↦ v : IProp GF) ={E}=∗ hookCell V a := by
  iintro Hc
  imod (initInv_alloc hookN E iprop(∃ v : V, (a ↦ v : IProp GF))) $$ [Hc] with ⟨%γI, #Hinv⟩
  · inext; iexists v; iexact Hc
  imodintro
  unfold hookCell hookInv
  iexists γI
  iexact Hinv

/-- **Access to a hook cell**, for a holder of a package state: the cell, until it gives it back,
which returns its package state. -/
theorem hookCell_acc {V : Type} [TypedPointsto (GF := GF) V] (E : CoPset) (hE : ↑hookN ⊆ E)
    (a : Loc) (σ : GMap GoString Bool) :
    ⊢ hookCell V a -∗ ownGoState σ ={E}=∗
      ∃ v : V, (a ↦ v : IProp GF) ∗ (∀ v' : V, (a ↦ v' : IProp GF) ={E}=∗ ownGoState σ) := by
  iintro Hcell Hg
  unfold hookCell hookInv
  icases Hcell with ⟨%γI, #Hinv⟩
  imod (initInv_acc hookN E hE iprop(∃ v : V, (a ↦ v : IProp GF)) γI σ) $$ Hinv Hg with ⟨⟨%v, Hc⟩, Hback⟩
  imodintro
  iexists v
  iframe Hc
  iintro %v' Hc
  iapply Hback
  iexists v'
  iexact Hc

/-- **A package initializer's store in a hook cell.** -/
theorem wp_store_hook {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
    [IntoValTyped (GF := GF) V t] (a : Loc) (w : V) (g : GoString → IProp GF) (σ0 : GMap GoString Bool) :
    {{ hookCell V a ∗ EtcdGrove.ownInitLb g σ0 }}
      (App (Val (GoInstruction (GoStore t))) (Val (PairV #a #w)))
    {{ RET #(); EtcdGrove.ownInitLb g σ0 }} := by
  wp_start as ⟨Hcell, Hown⟩
  unfold EtcdGrove.ownInitLb
  icases Hown with ⟨%σ, Hg, #Hok, %Hle⟩
  iapply fupd_wp
  imod (hookCell_acc ⊤ CoPset.subseteq_top a σ) $$ Hcell Hg with ⟨%v, Hc, Hback⟩
  imodintro
  iapply wp_fupd
  wp_apply (IntoValTyped.wp_store (V := V) (t := t) _ _ _) $$ Hc as Hc
  imod Hback $$ Hc with Hg
  imodintro
  iapply HΦ
  iexists σ; iframe Hg Hok; ipureintro; exact Hle

/-- The hook cell of a variable among `xs`. -/
theorem hookCells_mem {V : Type} [TypedPointsto (GF := GF) V] (xs : List GoString) (x : GoString)
    (h : x ∈ xs) : hookCells (GF := GF) V xs ⊢ hookCell V (globalAddr x) := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    unfold hookCells
    rcases List.mem_cons.mp h with rfl | h
    · iintro ⟨Hc, -⟩; iexact Hc
    · iintro ⟨-, Hs⟩; iapply (ih h) $$ Hs

end laws

end grpcInternal
end EtcdGrove
end Perennial
