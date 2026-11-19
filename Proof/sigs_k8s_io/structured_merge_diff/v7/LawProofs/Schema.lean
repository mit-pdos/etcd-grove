/-
**The root laws about schema literals, proved** (`v7/Laws.lean`): the pieces of a `freshSchema`
(`freshAtom_*`, `freshSchema_intro`), and `isSchema_intro` (each lazy index put under its once).

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Intro
import all Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open LawProofs

theorem freshAtom_scalar_law_holds : freshAtom_scalar.law (GF := GF) := fun a s h1 h2 => by
  rw [freshAtom, isAtom.eq_1]
  iintro #H
  iframe #
  ipureintro; exact ⟨h1, h2⟩

theorem freshAtom_list_law_holds : freshAtom_list.law (GF := GF) :=
  fun a v ksl e rel ks h1 h2 h3 h4 => by
  unfold freshAtom isAtom isListRep
  iintro #Hl #Hk #He
  isplitr
  · ipureintro; exact ⟨h1, h2⟩
  iexists v, ksl
  iframe #
  ipureintro; exact ⟨h3, h4⟩

theorem LawProofs.isFields_of_sepL : ∀ (sfs : List schema.StructField) (fs : List (GoString × TypeRef)),
    sfs.length = fs.length → (∀ sf ∈ sfs, sf.Default' = interface.nil) →
    sepL (fun sf => iprop(⌜sf.1.Name' = sf.2.1⌝ ∗ isTypeRef (GF := GF) sf.1.Type' sf.2.2))
      (sfs.zip fs) ⊢ isFields sfs fs
  | [], [], _, _ => by unfold isFields; iintro _; ipureintro; trivial
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | sf :: sfs, f :: fs, h, hd => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, LawProofs.sepL_cons]
      rw [isFields.eq_2]
      iintro ⟨⟨%hn, #Ht⟩, Hr⟩
      isplitl []
      · unfold isStructField
        isplitr
        · ipureintro; exact ⟨hn, hd sf List.mem_cons_self⟩
        · iexact Ht
      · iapply LawProofs.isFields_of_sepL sfs fs h (fun x hx => hd x (List.mem_cons_of_mem _ hx))
        iexact Hr

theorem freshAtom_map_law_holds : freshAtom_map.law (GF := GF) :=
  fun a fsl sfs fs etv e rel h1 h2 hnn h3 h4 => by
  unfold freshAtom isAtom mapRep lazyIndex
  simp only [↓reduceIte]
  iintro #Hf #Hs Hl #Hu #He He' #Hr Ho Hm
  ihave Hl := LawProofs.isFields_of_sepL sfs fs h3 h4 $$ Hl
  isplitr
  · ipureintro; exact ⟨h1, h2⟩
  isplitr
  · ipureintro; exact hnn
  iexists fsl, sfs, slice.nil, etv
  iframe
  iframe #
  isplitr
  · ipureintro; rfl
  cases e with
  | none =>
    unfold isTypeRefOpt atomZero
    icases He' with %h
    ipureintro
    exact ⟨h.1, ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩
  | some t =>
    unfold isTypeRefOpt
    iexact He'

theorem LawProofs.isTypeDefs_of_sepL : ∀ (tds : List schema.TypeDef) (ts : List (GoString × Atom)),
    tds.length = ts.length →
    sepL (fun ta => iprop(⌜ta.1.Name' = ta.2.1⌝ ∗ freshAtom (GF := GF) ta.1.Atom' ta.2.2))
      (tds.zip ts) ⊢ isTypeDefs true tds ts
  | [], [], _ => by unfold isTypeDefs; iintro _; ipureintro; trivial
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | td :: tds, (n, A) :: ts, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, LawProofs.sepL_cons]
      rw [isTypeDefs.eq_2]
      iintro ⟨⟨%hn, Ha⟩, Hr⟩
      isplitr
      · ipureintro; exact hn
      isplitl [Ha]
      · iapply (by unfold freshAtom; exact .rfl : freshAtom (GF := GF) td.Atom' A ⊢ isAtom true td.Atom' A)
        iexact Ha
      · iapply LawProofs.isTypeDefs_of_sepL tds ts h
        iexact Hr

theorem freshSchema_intro_law_holds : freshSchema_intro.law (GF := GF) := fun sc tys tds S h => by
  unfold freshSchema schemaRep lazyIndex
  simp only [↓reduceIte]
  iintro #Ht #Hs Hd Ho Hm
  ihave Hd := LawProofs.isTypeDefs_of_sepL tds S.types h $$ Hd
  iexists tys, tds
  iframe
  iframe #

/-! ## `isSchema_intro`: every lazy index under its once -/

/-- Perennial's `sync.init_Once`, without its `[sync.Assumptions]` argument (which its statement
does not need: it is an auto-included section variable there; the laws have no package
assumptions in scope). The same proof, with `init_Mutex` and `ownBool_halves` inlined. -/
theorem LawProofs.init_Once' (o : Loc) (P Q : IProp GF) (E : CoPset) [Persistent Q] :
    typedPointsto (GF := GF) o (zero_val sync.Once) (DFrac.own 1) ∗ P ⊢ |={E}=> sync.isOnce o P Q := by
  iintro ⟨Ho, HP⟩
  rw [sync.isOnce_unseal]; unfold sync.isOnceDef
  iStructNamed Ho
  have hz : (zero_val sync.atomic.Bool') =
      ({ «_#0'» := zero_val _, v' := sync.atomic.b32w false } : sync.atomic.Bool') := rfl
  have hh := (sync.atomic.ownBool_fractional (GF := GF)
    (structFieldRef sync.Once go!"done" o) false).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hh
  ihave Hd := hh.1 $$ [done]
  · simp only [sync.atomic.ownBool_unseal, sync.atomic.ownBoolDef]
    rw [← hz]; iexact done
  icases Hd with ⟨done1, done2⟩
  have hm : ⊢ typedPointsto (GF := GF) (structFieldRef sync.Once go!"m" o) (zero_val sync.Mutex)
      (DFrac.own 1) -∗ ▷ sync.OnceLockInv o P Q ={E}=∗
      sync.isMutex (structFieldRef sync.Once go!"m" o) (sync.OnceLockInv o P Q) := by
    simp only [sync.isMutex_unseal, sync.isMutexDef]
    exact init_lock _ E _
  imod hm $$ m [done2 HP] with #Hm
  · inext; unfold sync.OnceLockInv; iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]; iframe
  imod inv_alloc nroot E (sync.OnceInv o Q) $$ [done1] with #Hinv
  · inext; unfold sync.OnceInv; iexists false; iframe
    imodintro; iintro %h; cases h
  imodintro
  iframe #
  imodintro
  iintro #HQ
  imodintro
  iexact HQ

theorem LawProofs.lazyIndex_init {T : Type} [ZeroVal T] [TypedPointsto (GF := GF) T]
    (o u : Loc) (ok : GMap GoString T → Prop) :
    lazyIndex (GF := GF) (T := T) true o u ok ⊢ |={⊤}=> lazyIndex false o u ok := by
  unfold lazyIndex
  simp only [↓reduceIte, Bool.false_eq_true]
  iintro ⟨Ho, Hu⟩
  iapply LawProofs.init_Once'
  iframe

theorem LawProofs.mapRep_init (m : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
    (rel : ElemRel) :
    mapRep (GF := GF) true m fs e rel ⊢ |={⊤}=> mapRep false m fs e rel := by
  unfold mapRep
  iintro ⟨%hnn, %fsl, %sfs, %us, %etv, #Hf, #Hs, #Hd, #Hu, %hu, #He, #Het, #Hr, Hl⟩
  imod LawProofs.lazyIndex_init _ _ _ $$ Hl with #Hl
  imodintro
  isplitr
  · ipureintro; exact hnn
  iexists fsl, sfs, us, etv
  iframe #
  ipureintro; exact hu

theorem LawProofs.isAtom_init (a : schema.Atom) (A : Atom) :
    isAtom (GF := GF) true a A ⊢ |={⊤}=> isAtom false a A := by
  cases A with
  | scalar s => unfold isAtom; iintro H; imodintro; iexact H
  | list e rel ks => unfold isAtom; iintro H; imodintro; iexact H
  | map fs e rel =>
    rw [isAtom.eq_3, isAtom.eq_3]
    iintro ⟨%h, Hm⟩
    imod LawProofs.mapRep_init _ _ _ _ $$ Hm with Hm
    imodintro
    iframe
    ipureintro; exact h

theorem LawProofs.isTypeDefs_init : ∀ (tds : List schema.TypeDef) (ts : List (GoString × Atom)),
    isTypeDefs (GF := GF) true tds ts ⊢ |={⊤}=> isTypeDefs false tds ts
  | [], [] => by unfold isTypeDefs; iintro _; imodintro; ipureintro; trivial
  | [], _ :: _ => by unfold isTypeDefs; iintro %h; exact h.elim
  | _ :: _, [] => by unfold isTypeDefs; iintro %h; exact h.elim
  | td :: tds, (n, A) :: ts => by
      rw [isTypeDefs.eq_2, isTypeDefs.eq_2]
      iintro ⟨%hn, Ha, Hr⟩
      imod LawProofs.isAtom_init _ _ $$ Ha with Ha
      imod LawProofs.isTypeDefs_init tds ts $$ Hr with Hr
      imodintro
      iframe
      ipureintro; exact hn

theorem isSchema_intro_law_holds : isSchema_intro.law (GF := GF) := fun sc S => by
  unfold freshSchema isSchema schemaRep
  iintro ⟨%tys, %tds, #Ht, #Hs, Hd, Hl⟩
  imod LawProofs.isTypeDefs_init _ _ $$ Hd with Hd
  imod LawProofs.lazyIndex_init _ _ _ $$ Hl with Hl
  imodintro
  iexists tys, tds
  iframe
  iframe #

end laws
end smd
end EtcdGrove
end Perennial
