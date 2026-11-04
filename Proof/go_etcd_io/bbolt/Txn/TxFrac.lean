/-
A transaction at a fraction (U5 of `notes/bbolt-proof-plan.md`): `boltTxDef_fractional'`, the
shared `Inv/Tx.boltTxDef_fractional` (same statement). Splitting is component-wise; combining
agrees on the existentials (the registration and the agreed state by their ghost state, the
fields' values and the mapping's length by their points-tos) and adds the fractions (`txDbQ`,
`QpMul`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Tx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section txfrac
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

set_option linter.unusedSectionVars false

/-! ## Fractions -/

theorem QpMul_add_l (p q r : Qp) : QpMul (p + q) r = QpMul p r + QpMul q r :=
  Subtype.ext (by simp only [QpMul, Qp.val_add]; grind)

theorem txDbQ_add (p q : Qp) : txDbQ (p + q) = txDbQ p + txDbQ q := by
  unfold txDbQ
  rw [QpMul_add_l, QpMul_add_l]
  apply Subtype.ext
  simp only [Qp.val_add]; grind

/-- A fractional predicate at a fraction that adds. -/
theorem fractional_comp (Φ : Qp → IProp GF) [h : Fractional Φ] (f : Qp → Qp)
    (hf : ∀ p q, f (p + q) = f p + f q) : Fractional (fun q => Φ (f q)) :=
  ⟨fun p q => by rw [hf]; exact h.fractional _ _⟩

/-- An existential of fractional predicates whose witnesses can be made to agree. -/
theorem fractional_exists' {X : Type} (Φ : X → Qp → IProp GF) (hf : ∀ x, Fractional (Φ x))
    (hc : ∀ x y p q, Φ x p ∗ Φ y q ⊢ Φ x p ∗ Φ x q) :
    Fractional (fun q => iprop(∃ x, Φ x q)) := by
  refine ⟨fun p q => ⟨?_, ?_⟩⟩
  · iintro ⟨%x, H⟩
    icases ((hf x).fractional p q).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists x; iexact H1
    · iexists x; iexact H2
  · iintro ⟨⟨%x, H1⟩, ⟨%y, H2⟩⟩
    ihave H := hc x y p q $$ [H1 H2]
    · isplitl [H1]
      · iexact H1
      · iexact H2
    iexists x
    iapply ((hf x).fractional p q).2
    iexact H

instance pointsto_fractional_tf {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (l : Loc)
    (v : V) [DFractional (fun dq => (l ↦{dq} v : IProp GF))] :
    Fractional (fun q : Qp => (l ↦{DFrac.own q} v : IProp GF)) :=
  fractional_of_dfractional (fun dq => (l ↦{dq} v : IProp GF))

instance bytes_fractional_tf (l : Loc) (bs : List w8) :
    Fractional (fun q : Qp => bytesPointsto (GF := GF) l (DFrac.own q) bs) :=
  fractional_of_dfractional (h := bytesPointsto_dfractional (GF := GF) l bs) _

instance viewCells_fractional_tf (v : View) :
    Fractional (fun q : Qp => viewCells (GF := GF) q v) := by
  unfold viewCells; infer_instance

/-- A `w64` field at a fraction, its value existential under a fact. -/
theorem exField_fractional (l : Loc) (P : w64 → Prop) :
    Fractional (fun q : Qp => iprop(∃ v : w64, ⌜P v⌝ ∗ (l ↦{DFrac.own q} v : IProp GF))) := by
  refine fractional_exists' (fun v q => iprop(⌜P v⌝ ∗ (l ↦{DFrac.own q} v : IProp GF)))
    (fun v => inferInstance) (fun x y p q => ?_)
  iintro ⟨⟨%hx, H1⟩, ⟨%hy, H2⟩⟩
  icombine H1 H2 gives %h
  obtain ⟨-, rfl⟩ := h
  isplitl [H1]
  · iframe; ipureintro; exact hx
  · iframe; ipureintro; exact hx

theorem QpMul_frac (Φ : Qp → IProp GF) [Fractional Φ] (c : Qp) :
    Fractional (fun q => Φ (QpMul q c)) :=
  fractional_comp Φ (fun q => QpMul q c) (fun p q => QpMul_add_l p q c)

instance mapFields_some_fractional (db base : Loc) (l : Nat) :
    Fractional (fun q : Qp => mapFields (GF := GF) db (DFrac.own q) (some (base, l) : MapSt)) := by
  unfold mapFields; infer_instance

/-- Two mappings' fields at one base agree on the length. -/
theorem mapFields_some_agree (db base : Loc) (l1 l2 : Nat) (dq1 dq2 : DFrac) :
    mapFields (GF := GF) db dq1 (some (base, l1) : MapSt) ∗
      mapFields db dq2 (some (base, l2) : MapSt) ⊢ ⌜l1 = l2⌝ := by
  unfold mapFields
  iintro ⟨⟨Ha1, -, -, -, %hm1⟩, ⟨Ha2, -, -, -, %hm2⟩⟩
  icombine Ha1 Ha2 gives %he
  ipureintro
  have e := congrArg (fun s : GoSlice => s.len.toNat) he
  simp only at e
  rw [toNat_W64_of_lt _ (by omega), toNat_W64_of_lt _ (by omega)] at e
  exact e

/-- **A writer's part is fractional** (same registration, view and records). -/
theorem wtxFrac_fractional (B : BNs) (tx : Loc) (r : TxReg) (T : TxView) (X : WX) :
    Fractional (fun q => wtxFrac (GF := GF) B tx r q T X) := by
  have h1 := wtxHeap_fractional (GF := GF) tx X
  have h2 : Fractional (fun q : Qp => fills (GF := GF) X.handles (DFrac.own q)) := by
    unfold fills
    have : ∀ b : Loc, Fractional (fun q : Qp => iprop(∃ f : w64, ⌜¬ float64IsNaN f⌝ ∗
        (b.[Bucket, go!"FillPercent"] ↦{DFrac.own q} f : IProp GF))) :=
      fun b => exField_fractional _ _
    infer_instance
  have h3 := QpMul_frac (fun q => viewCells (GF := GF) q X.v) wq
  have h4 := QpMul_frac (fun q => ghostVar (GF := GF) B.st q T.base) (1 : Qp).half.half
  have h7 := fractional_comp (fun q => (tx.[Tx, go!"db"] ↦{DFrac.own q} r.db : IProp GF))
    txDbQ txDbQ_add
  have h8 : Fractional (fun q => iprop(∃ l : Nat,
      mapFields (GF := GF) r.db (DFrac.own (QpMul q (1 : Qp).half.half)) (some (X.v.base, l) : MapSt) ∗
      ⌜∀ id pg, X.v.pages !! id = some pg → (id + 1) * 4096 ≤ l⌝)) := by
    refine fractional_exists' _ (fun l => ?_) (fun l1 l2 p q => ?_)
    · have := QpMul_frac (fun q => mapFields (GF := GF) r.db (DFrac.own q) (some (X.v.base, l)))
        (1 : Qp).half.half
      infer_instance
    · iintro ⟨⟨H1, %h1⟩, ⟨H2, %h2⟩⟩
      icases (and_intro .rfl (mapFields_some_agree r.db X.v.base l1 l2 _ _) :
        mapFields (GF := GF) r.db (DFrac.own (QpMul p (1 : Qp).half.half)) (some (X.v.base, l1)) ∗
          mapFields r.db (DFrac.own (QpMul q (1 : Qp).half.half)) (some (X.v.base, l2)) ⊢ _ ∧ _)
        $$ [H1 H2] with ⟨⟨H1, H2⟩, %he⟩
      · isplitl [H1]
        · iexact H1
        · iexact H2
      subst he
      isplitl [H1]
      · iframe; ipureintro; exact h1
      · iframe; ipureintro; exact h1
  unfold wtxFrac viewOf
  infer_instance

private instance bytes_discard_persistent_tf (l : Loc) (bs : List w8) :
    Persistent (bytesPointsto (GF := GF) l DFrac.discard bs) :=
  (bytesPointsto_dfractional (GF := GF) l bs).dfractional_persistent

private instance ite_persistent_tf {c : Prop} [Decidable c] (P Q : IProp GF) [Persistent P]
    [Persistent Q] : Persistent (if c then P else Q) := by
  split <;> infer_instance

private instance reg_persistent_tf (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private instance isBoltP_persistent_tf (B : BNs) (N : Namespace) (db : Loc) (p : GoString)
    (sp : Loc) (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

/-- **A reader's bucket is fractional** (its header and page pointers agree). -/
theorem rBkt_fractional (v : View) (tx b : Loc) (bv : List w8) :
    Fractional (fun q : Qp => rBkt (GF := GF) v tx b (DFrac.own q) bv) := by
  unfold rBkt locOwn
  refine fractional_exists' _ (fun ibp => ?_) (fun i1 i2 p q => ?_)
  · refine fractional_exists' _ (fun pp => ?_) (fun p1 p2 p q => ?_)
    · infer_instance
    · iintro ⟨⟨A1, B1, C1, D1, E1, F1, G1, H1⟩, ⟨A2, B2, C2, D2, E2, F2, G2, H2⟩⟩
      icombine D1 D2 gives %h
      obtain ⟨-, rfl⟩ := h
      isplitl [A1 B1 C1 D1 E1 F1 G1 H1]
      · iframe
      · iframe
  · iintro ⟨⟨%pp1, A1, B1, C1, D1, E1, F1, G1, H1⟩, ⟨%pp2, A2, B2, C2, D2, E2, F2, G2, H2⟩⟩
    icombine A1 A2 gives %h
    obtain ⟨-, rfl⟩ := h
    icombine D1 D2 gives %h'
    obtain ⟨-, rfl⟩ := h'
    isplitl [A1 B1 C1 D1 E1 F1 G1 H1]
    · iexists pp1; iframe
    · iexists pp1; iframe

/-- **A reader's part is fractional** (same registration, view and meta copy). -/
theorem rtxFrac_fractional (B : BNs) (tx : Loc) (r : TxReg) (T : TxView) (v : View) (mv : Meta) :
    Fractional (fun q => rtxFrac (GF := GF) B tx r q T v mv) := by
  have h1 := rBkt_fractional (GF := GF) v tx (txRoot (GF := GF) tx) (rootVal v)
  have h2 : Fractional (fun q : Qp => iprop(∃ f : w64,
      ((txRoot (GF := GF) tx).[Bucket, go!"FillPercent"] ↦{DFrac.own q} f : IProp GF))) := by
    refine fractional_exists' _ (fun f => inferInstance) (fun x y p q => ?_)
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %h
    obtain ⟨-, rfl⟩ := h
    iframe
  have h3 := QpMul_frac (fun q => viewCells (GF := GF) q v) rq
  have h7 := fractional_comp (fun q => (tx.[Tx, go!"db"] ↦{DFrac.own q} r.db : IProp GF))
    txDbQ txDbQ_add
  have hq4 : ∀ p q : Qp, (QpMul (p + q) sync.rfrac).half.half =
      (QpMul p sync.rfrac).half.half + (QpMul q sync.rfrac).half.half := by
    intro p q; rw [QpMul_add_l, Qp_half_add, Qp_half_add]
  have hq2 : ∀ p q : Qp, (QpMul (p + q) sync.rfrac).half =
      (QpMul p sync.rfrac).half + (QpMul q sync.rfrac).half := by
    intro p q; rw [QpMul_add_l, Qp_half_add]
  have h8 : Fractional (fun q => iprop(∃ l : Nat,
      ghostVar (GF := GF) B.map (QpMul q sync.rfrac).half.half (some (v.base, l) : MapSt) ∗
      mapFields r.db (DFrac.own (QpMul q sync.rfrac).half) (some (v.base, l) : MapSt) ∗
      ⌜∀ id pg, v.pages !! id = some pg → (id + 1) * 4096 ≤ l⌝)) := by
    refine fractional_exists' _ (fun l => ?_) (fun l1 l2 p q => ?_)
    · have := fractional_comp (fun q => ghostVar (GF := GF) B.map q (some (v.base, l) : MapSt))
        (fun q => (QpMul q sync.rfrac).half.half) hq4
      have := fractional_comp (fun q => mapFields (GF := GF) r.db (DFrac.own q)
        (some (v.base, l) : MapSt)) (fun q => (QpMul q sync.rfrac).half) hq2
      infer_instance
    · iintro ⟨⟨G1, M1, %h1⟩, ⟨G2, M2, %h2⟩⟩
      icombine G1 G2 gives %h
      obtain ⟨-, he⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      isplitl [G1 M1]
      · iframe; ipureintro; exact h1
      · iframe; ipureintro; exact h1
  unfold rtxFrac viewOf
  refine fractional_exists' _ (fun t => ?_) (fun t1 t2 p q => ?_)
  · infer_instance
  · iintro ⟨⟨A1, B1, C1, D1, E1, F1, G1, H1, I1, J1, K1, L1, M1, %P1⟩,
      ⟨A2, B2, C2, D2, E2, F2, G2, H2, I2, J2, K2, L2, M2, %P2⟩⟩
    icombine B1 B2 gives %e1
    icombine C1 C2 gives %e2
    icombine F1 F2 gives %e3
    icombine G1 G2 gives %e4
    icombine H1 H2 gives %e5
    replace e1 := by first | exact e1.2 | exact e1
    replace e2 := by first | exact e2.2 | exact e2
    replace e3 := by first | exact e3.2 | exact e3
    replace e4 := by first | exact e4.2 | exact e4
    replace e5 := by first | exact e5.2 | exact e5
    rw [e1, e2, e3, e4, e5]
    isplitl [A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1 M1]
    · iframe; ipureintro; rw [← e1, ← e3]; exact P1
    · iframe; ipureintro; exact P2

/-- **A reader over the core with a pool loan is fractional.** -/
theorem rdTx_fractional (B : BNs) (N : Namespace) (tx : Loc) (T : TxView) :
    Fractional (fun q => rdTx (GF := GF) B N tx .loan q T) := by
  unfold rdTx
  simp only [↓reduceIte]
  refine ⟨fun p q => ⟨?_, ?_⟩⟩
  · iintro ⟨%db, %pa, %sp, %t0, %r, %c, %v, %mv, %k, %Hc, #Hreg, #Hb, Hv, Hex, Hw, #Hp⟩
    rw [Qp_half_add]
    icases ((ghostVar_fractional r.n.v (c, TxX.rd v mv k)).fractional _ _).1 $$ Hv with ⟨Hv1, Hv2⟩
    icases ((ghostVar_fractional r.n.ex ()).fractional p q).1 $$ Hex with ⟨He1, He2⟩
    icases ((rtxFrac_fractional B tx r T v mv).fractional p q).1 $$ Hw with ⟨Hw1, Hw2⟩
    isplitl [Hv1 He1 Hw1]
    · iexists db, pa, sp, t0, r, c, v, mv, k; iframe; iframe #; ipureintro; exact Hc
    · iexists db, pa, sp, t0, r, c, v, mv, k; iframe; iframe #; ipureintro; exact Hc
  · iintro ⟨⟨%db, %pa, %sp, %t0, %r, %c, %v, %mv, %k, %Hc, #Hreg, #Hb, Hv, Hex, Hw, #Hp⟩,
      ⟨%db2, %pa2, %sp2, %t02, %r2, %c2, %v2, %mv2, %k2, %Hc2, #Hreg2, -, Hv2, Hex2, Hw2, -⟩⟩
    iunfold reg at Hreg Hreg2
    icombine Hreg Hreg2 gives %hr
    obtain ⟨-, rfl⟩ := hr
    icombine Hv Hv2 gives %hv
    obtain ⟨-, hv⟩ := hv
    simp only [Prod.mk.injEq, TxX.rd.injEq] at hv
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hv
    iexists db, pa, sp, t0, r, c, v, mv, k
    isplitr
    · ipureintro; exact Hc
    iframe Hb Hp
    isplitr
    · iunfold reg; iexact Hreg
    rw [Qp_half_add]
    isplitl [Hv Hv2]
    · iapply ((ghostVar_fractional r.n.v (c, TxX.rd v mv k)).fractional _ _).2; iframe
    isplitl [Hex Hex2]
    · iapply ((ghostVar_fractional r.n.ex ()).fractional p q).2; iframe
    iapply ((rtxFrac_fractional B tx r T v mv).fractional p q).2; iframe

/-- **`boltTxDef_fractional`** (`Inv/Tx`, same statement). -/
theorem boltTxDef_fractional' (B : BNs) (N : Namespace) (tx : Loc) (T : TxView) :
    Fractional (fun q => boltTxDef (GF := GF) B N tx q T) := by
  unfold boltTxDef
  by_cases hrw : T.rw = true
  · simp only [hrw, ↓reduceIte]
    refine ⟨fun p q => ⟨?_, ?_⟩⟩
    · iintro ⟨%db, %pa, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #Hb, Hv, Hex, Hw⟩
      rw [Qp_half_add]
      icases ((ghostVar_fractional r.n.v (c, TxX.wr X)).fractional _ _).1 $$ Hv with ⟨Hv1, Hv2⟩
      icases ((ghostVar_fractional r.n.ex ()).fractional p q).1 $$ Hex with ⟨He1, He2⟩
      icases ((wtxFrac_fractional B tx r T X).fractional p q).1 $$ Hw with ⟨Hw1, Hw2⟩
      isplitl [Hv1 He1 Hw1]
      · iexists db, pa, sp, t0, r, c, X; iframe; iframe #; ipureintro; exact Hc
      · iexists db, pa, sp, t0, r, c, X; iframe; iframe #; ipureintro; exact Hc
    · iintro ⟨⟨%db, %pa, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #Hb, Hv, Hex, Hw⟩,
        ⟨%db2, %pa2, %sp2, %t02, %r2, %c2, %X2, %Hc2, #Hreg2, -, Hv2, Hex2, Hw2⟩⟩
      iunfold reg at Hreg Hreg2
      icombine Hreg Hreg2 gives %hr
      obtain ⟨-, rfl⟩ := hr
      icombine Hv Hv2 gives %hv
      obtain ⟨-, hv⟩ := hv
      simp only [Prod.mk.injEq, TxX.wr.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      iexists db, pa, sp, t0, r, c, X
      isplitr
      · ipureintro; exact Hc
      isplitr
      · iunfold reg; iexact Hreg
      iframe Hb
      rw [Qp_half_add]
      isplitl [Hv Hv2]
      · iapply ((ghostVar_fractional r.n.v (c, TxX.wr X)).fractional _ _).2; iframe
      isplitl [Hex Hex2]
      · iapply ((ghostVar_fractional r.n.ex ()).fractional p q).2; iframe
      iapply ((wtxFrac_fractional B tx r T X).fractional p q).2; iframe
  · have hrw' : T.rw = false := by simpa using hrw
    simp only [hrw', Bool.false_eq_true, ↓reduceIte]
    refine fractional_exists' _ (fun db => ?_) (fun d1 d2 p q => ?_)
    rotate_left
    · iintro ⟨⟨H1, #D1⟩, ⟨H2, -⟩⟩
      isplitl [H1]
      · iframe; iframe #
      · iframe; iframe #
    have := rdTx_fractional (GF := GF) B N tx T
    infer_instance

end txfrac

end bbolt
end EtcdGrove
end Perennial
