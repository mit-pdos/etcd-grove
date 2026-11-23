/-
**grpc's `internal.FromOutgoingContextRaw`** (phase 7 S2 core, 2026-11-23, `notes/phase7-plan.md` §0a):
the laws of its invariant `fromOutRawInv` (`cache/v3/Base.lean`), which `internal`'s, `metadata`'s and
grpc's generated `Init.lean` use. Lean-first.

Go: `internal.FromOutgoingContextRaw` is a variable of type `any` (`internal.go`, no initializer);
`metadata`'s `init` stores `fromOutgoingContextRaw` in it, and grpc's package variable
`metadataFromOutgoingContextRaw` (`stream.go:53`) is its type assertion, run when grpc's initializer
runs (after `metadata`'s, which grpc imports). The cell is another package's: `internal`'s initializer
allocates it, `metadata`'s writes it, grpc's reads it, and a package fact is persistent. So the cell
lives in an invariant (`internalInit`), from which a package initializer, which holds its exclusive
package state `ownGoState σ`, takes it out for a plain load or store by lending that state
(`fromOutRaw_acc`); the counter `γS` past `0` (`metadataInit`) says the store happened.

* `fromOutRaw_alloc`: the freshly allocated cell (holding `nil`) gives `internalInit`.
* `fromOutRaw_acc`: with a package state, the cell (and the counter's authority) out of the
  invariant, and back.
* `wp_store_fromOutRaw` (`metadata`'s `init`): the store of `fromOutRawAny` gives `metadataInit`.
* `wp_load_fromOutRaw` (grpc's initializer): with `metadataInit`, the load returns `fromOutRawAny`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.runtime.PkgInit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace grpcInternal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal
  (fromOutRawN fromOutRawInv fromOutRawAny fromOutRawTy internalInit)
open _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.metadata (metadataInit)

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The cell. -/
local notation "cell" => globalAddr _root_.Perennial.google_golang_org.grpc.internal.FromOutgoingContextRaw

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

/-- **The freshly allocated cell gives `internal`'s fact.** -/
theorem fromOutRaw_alloc (E : CoPset) :
    ⊢ (cell ↦ (default : GoInterface) : IProp GF) ={E}=∗ internalInit (hG := hG) := by
  iintro Hc
  imod ghost_var_alloc (A := GMap GoString Bool) ∅ with ⟨%γI, HI⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γS, HS, -⟩
  imod inv_alloc fromOutRawN E (fromOutRawInv (hG := hG) γI γS) $$ [Hc HI HS] with #Hinv
  · inext
    unfold fromOutRawInv
    ileft
    iexists _, 0, ∅
    iframe Hc HI HS
    ipureintro; left; rfl
  imodintro
  unfold internalInit
  iexists γI, γS
  iexact Hinv

/-- **Access to the cell**, for a holder of a package state: the cell and the counter's authority,
until it gives them back (the counter past `0` only with `fromOutRawAny` in the cell), which returns
its package state. -/
theorem fromOutRaw_acc (E : CoPset) (hE : ↑fromOutRawN ⊆ E) (γI γS : GName) (σ : GMap GoString Bool) :
    ⊢ inv fromOutRawN (fromOutRawInv (hG := hG) γI γS) -∗ ownGoState σ ={E}=∗
      ∃ (v : GoInterface) (n : Nat), cell ↦ v ∗ monoNatAuthOwn γS 1 n ∗
        ⌜n = 0 ∨ v = fromOutRawAny (hG := hG)⌝ ∗
        (∀ (v' : GoInterface) (n' : Nat), cell ↦ v' -∗ monoNatAuthOwn γS 1 n' -∗
          ⌜n' = 0 ∨ v' = fromOutRawAny (hG := hG)⌝ ={E}=∗ ownGoState σ) := by
  iintro #Hinv Hg
  -- take the cell out, lending the package state
  ihave Hhalf : |={E}=> ∃ (v : GoInterface) (n : Nat), cell ↦ v ∗ monoNatAuthOwn γS 1 n ∗
      ⌜n = 0 ∨ v = fromOutRawAny (hG := hG)⌝ ∗ ghost_var γI (DFrac.own (1 : Qp).half) σ $$ [Hg]
  · iinv Hinv with Hi Hclose
    unfold fromOutRawInv
    icases Hi with (⟨%v, %n, %x, >Hc, >HI, >HS, >%Hv⟩ | ⟨%σ', >Hg', >-⟩)
    · imod ghost_var_update σ γI x $$ HI with HI
      rw [half_add_half_own]
      ihave ⟨HI1, HI2⟩ := ghost_var_split γI σ _ _ $$ HI
      imod Hclose $$ [Hg HI1] with -
      · inext; iright; iexists σ; iframe Hg HI1
      imodintro
      iexists v, n
      iframe Hc HS HI2
      ipureintro; exact Hv
    · iexfalso
      iapply ownGoState_excl σ σ' $$ Hg Hg'
  imod Hhalf with ⟨%v, %n, Hc, HS, %Hv, HI⟩
  imodintro
  iexists v, n
  iframe Hc HS
  isplitr
  · ipureintro; exact Hv
  -- give it back, getting the package state back
  iintro %v' %n' Hc HS %Hv'
  iinv Hinv with Hi Hclose
  try unfold fromOutRawInv
  icases Hi with (⟨%v0, %n0, %x, >Hc0, >HI0, >HS0, >-⟩ | ⟨%σ', >Hg, >HI'⟩)
  · icases ghost_var_valid_2 $$ HI0 HI with %H
    exfalso
    have := DFrac.valid_own_op H.1
    simp at this
  · icases ghost_var_agree $$ HI HI' with %Hσ
    subst Hσ
    icombine HI HI' as HI
    imod Hclose $$ [Hc HS HI] with -
    · inext; ileft; iexists v', n', σ; iframe Hc HS HI; ipureintro; exact Hv'
    imodintro
    iexact Hg

/-- **`metadata`'s `init`: the store** of `fromOutgoingContextRaw` (as `any`) in the cell, by a
package initializer: `metadata`'s fact. -/
theorem wp_store_fromOutRaw (g : GoString → IProp GF) (σ0 : GMap GoString Bool) :
    {{ internalInit (hG := hG) ∗ EtcdGrove.ownInitLb g σ0 }}
      (App (Val (GoInstruction (GoStore go.any))) (Val (PairV #cell #(fromOutRawAny (hG := hG)))))
    {{ RET #(); EtcdGrove.ownInitLb g σ0 ∗ metadataInit (hG := hG) }} := by
  wp_start as ⟨Hi, Hown⟩
  unfold internalInit
  icases Hi with ⟨%γI, %γS, #Hinv⟩
  unfold EtcdGrove.ownInitLb
  icases Hown with ⟨%σ, Hg, #Hok, %Hle⟩
  iapply fupd_wp
  imod (fromOutRaw_acc ⊤ CoPset.subseteq_top γI γS σ) $$ Hinv Hg with ⟨%v, %n, Hc, HS, %Hv, Hback⟩
  imodintro
  iapply wp_fupd
  wp_apply (IntoValTyped.wp_store (V := GoInterface) (t := go.any) _ _ _) $$ Hc as Hc
  imod mono_nat_own_update (GF := GF) (n + 1) (Nat.le_succ n) $$ HS with ⟨HS, #Hlb⟩
  imod Hback $$ Hc HS [] with Hg
  · ipureintro; right; rfl
  imodintro
  iapply HΦ
  isplitl [Hg]
  · iexists σ; iframe Hg Hok; ipureintro; exact Hle
  unfold metadataInit
  iexists γI, γS
  iframe Hinv
  iapply monoNatLbOwn_le 1 (by omega) $$ Hlb

/-- **grpc's `metadataFromOutgoingContextRaw`: the load** of the cell, by a package initializer,
after `metadata`'s `init`: `fromOutgoingContextRaw` (as `any`). -/
theorem wp_load_fromOutRaw (g : GoString → IProp GF) (σ0 : GMap GoString Bool) :
    {{ metadataInit (hG := hG) ∗ EtcdGrove.ownInitLb g σ0 }}
      (App (Val (GoInstruction (GoLoad go.any))) (Val #cell))
    {{ RET #(fromOutRawAny (hG := hG)); EtcdGrove.ownInitLb g σ0 }} := by
  wp_start as ⟨Hi, Hown⟩
  unfold metadataInit
  icases Hi with ⟨%γI, %γS, #Hinv, #Hlb⟩
  unfold EtcdGrove.ownInitLb
  icases Hown with ⟨%σ, Hg, #Hok, %Hle⟩
  iapply fupd_wp
  imod (fromOutRaw_acc ⊤ CoPset.subseteq_top γI γS σ) $$ Hinv Hg with ⟨%v, %n, Hc, HS, %Hv, Hback⟩
  icases monoNatLbOwn_valid γS 1 n 1 $$ HS Hlb with %Hn
  have hv : v = fromOutRawAny (hG := hG) := by
    rcases Hv with h | h
    · omega
    · exact h
  subst hv
  imodintro
  iapply wp_fupd
  wp_apply (IntoValTyped.wp_load (V := GoInterface) (t := go.any) _ _ _) $$ Hc as Hc
  imod Hback $$ Hc HS [] with Hg
  · ipureintro; right; rfl
  imodintro
  iapply HΦ
  iexists σ; iframe Hg Hok; ipureintro; exact Hle

end laws

end grpcInternal
end EtcdGrove
end Perennial
