/-
The writer's heap and a transaction at a fraction (U5 of `notes/bbolt-proof-plan.md`):
`wtxHeap_fractional'`, `boltTxDef_fractional'` (the shared `Inv/WtxHeap.wtxHeap_fractional` and
`Inv/Tx.boltTxDef_fractional`, same statements).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section frac
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit hos in
open Iris.ProofMode in
/-- A map points-to is `DFractional` (Perennial has only its `Fractional` form,
`ownMap_fractional`; a general fact, to propose there). -/
instance ownMap_dfractional' {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V]
    [go.IntoValInj K] (mref : Loc) (m : GMap K V) :
    DFractional (fun dq => (ownMap (GF := GF) mref dq m : IProp GF)) where
  dfractional p q := by
    rw [ownMap_unseal]
    have hh := fun mv => (heapPointsto_dfractional (GF := GF) mref mv).dfractional p q
    constructor
    · iintro H
      unfold ownMapDef
      icases H with ⟨%mv, %ps, Hown, %Hrepr⟩
      icases (hh mv).1 $$ Hown with ⟨H1, H2⟩
      isplitl [H1]
      · iexists mv, ps; simp only [named]; iframe H1; ipureintro; exact Hrepr
      · iexists mv, ps; simp only [named]; iframe H2; ipureintro; exact Hrepr
    · iintro ⟨H1, H2⟩
      unfold ownMapDef
      icases H1 with ⟨%mv, %ps1, Hown1, %Hrepr1⟩
      icases H2 with ⟨%mv2, %ps2, Hown2, %Hrepr2⟩
      icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
      subst Hmv
      iexists mv, ps1
      simp only [named]
      isplitl [Hown1 Hown2]
      · iapply (hh mv).2; iframe
      ipureintro; exact Hrepr1
  dfractional_persistent := ownMap_discarded_persist mref m
  dfractional_persist dq := ownMap_persist mref dq m

omit hos in
instance ite_dfractional' {c : Prop} [Decidable c] (Φ Ψ : DFrac → IProp GF) [DFractional Φ]
    [DFractional Ψ] : DFractional (fun dq => if c then Φ dq else Ψ dq) := by
  by_cases h : c <;> simp only [h, ↓reduceIte] <;> infer_instance

omit hos in
private instance bytesPointsto_discard_persistent_f (l : Loc) (bs : List w8) :
    Persistent (bytesPointsto (GF := GF) l DFrac.discard bs) :=
  (bytesPointsto_dfractional (GF := GF) l bs).dfractional_persistent

instance pageOwn_persistent' (v : View) (B : BRec) : Persistent (pageOwn (GF := GF) v B) := by
  unfold pageOwn; split
  · infer_instance
  · split <;> (try split) <;> infer_instance

instance wOwn_persistent' (v : View) (live : Bool) (it : Inode) (w : WEntry) :
    Persistent (wOwn (GF := GF) v live it w) := by
  unfold wOwn; cases live <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- An object of the writer's heap is `DFractional` in its fraction. -/
instance objOwn_dfractional' (v : View) (l : Loc) (b : Bool) (o : WObj) :
    DFractional (fun dq => objOwn (GF := GF) v l dq b o) := by
  cases o <;> cases b <;> simp only [objOwn] <;> infer_instance

instance objOwn_fractional' (v : View) (l : Loc) (b : Bool) (o : WObj) :
    Fractional (fun q => objOwn (GF := GF) v l (DFrac.own q) b o) :=
  fractional_of_dfractional (fun dq => objOwn (GF := GF) v l dq b o)

omit hos in
instance (priority := low) fractional_own_of_dfractional' {Φ : DFrac → IProp GF} [DFractional Φ] :
    Fractional (fun q => Φ (DFrac.own q)) :=
  fractional_of_dfractional Φ

omit hos in
instance ownMap_fractional_i {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V]
    [go.IntoValInj K] (mref : Loc) (m : GMap K V) :
    Fractional (fun q : Qp => (ownMap (GF := GF) mref (DFrac.own q) m : IProp GF)) :=
  ownMap_fractional mref m

omit hos in
instance pure_fractional' (P : Prop) : Fractional (fun _ : Qp => (iprop(⌜P⌝) : IProp GF)) :=
  fractional_of_dfractional (fun _ => iprop(⌜P⌝))

omit hos in
open Iris.ProofMode in
/-- A buffer of the page cache (its bytes the recorded ones). -/
instance buf_fractional' (bufs : GMap w64 (List w8)) (id : w64) (pl : Loc) :
    Fractional (fun q : Qp => (iprop(∃ bs, ⌜bufs !! id = some bs⌝ ∗ bytesPointsto pl (DFrac.own q) bs) :
      IProp GF)) := by
  have hf := fun bs => (fractional_of_dfractional (h := bytesPointsto_dfractional (GF := GF) pl bs) _)
  refine ⟨fun p q => ⟨?_, ?_⟩⟩
  · iintro ⟨%bs, %Hb, H⟩
    icases ((hf bs).fractional p q).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists bs; iframe; ipureintro; exact Hb
    · iexists bs; iframe; ipureintro; exact Hb
  · iintro ⟨⟨%bs, %Hb, H1⟩, ⟨%bs', %Hb', H2⟩⟩
    rw [Hb] at Hb'; cases Hb'
    iexists bs
    isplitr
    · ipureintro; exact Hb
    iapply ((hf bs).fractional p q).2
    iframe

omit hos in
open Iris.ProofMode in
/-- The root bucket's `FillPercent`, at a fraction. -/
instance rootFill_fractional' (tx : Loc) : Fractional (fun q => rootFill (GF := GF) tx (DFrac.own q)) := by
  unfold rootFill
  have hf : ∀ f : w64, Fractional (fun q : Qp =>
      ((tx.[Tx, go!"root"]).[Bucket, go!"FillPercent"] ↦{DFrac.own q} f : IProp GF)) := fun f =>
    fractional_of_dfractional (h := inferInstance) _
  refine ⟨fun p q => ⟨?_, ?_⟩⟩
  · iintro ⟨%f, %Hn, Hp⟩
    icases ((hf f).fractional p q).1 $$ Hp with ⟨H1, H2⟩
    isplitl [H1]
    · iexists f; iframe; ipureintro; exact Hn
    · iexists f; iframe; ipureintro; exact Hn
  · iintro ⟨⟨%f, %Hn, H1⟩, ⟨%g, %Hg, H2⟩⟩
    icombine H1 H2 gives %He
    obtain ⟨-, rfl⟩ := He
    iexists f
    isplitr
    · ipureintro; exact Hn
    iapply ((hf f).fractional p q).2
    iframe

omit hos in
instance txFields_fractional' (tx : Loc) (X : WX) :
    Fractional (fun q => txFields (GF := GF) tx (DFrac.own q) X) := by
  unfold txFields; infer_instance

/-- **`wtxHeap_fractional`** (`Inv/WtxHeap`, same statement). -/
theorem wtxHeap_fractional' (tx : Loc) (X : WX) :
    Fractional (fun q => wtxHeap (GF := GF) tx (DFrac.own q) X) := by
  unfold wtxHeap; infer_instance

end frac

end bbolt
end EtcdGrove
end Perennial
