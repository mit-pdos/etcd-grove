/-
`Visit` over a tree's entries (nomode X-a2, 2026-11-27): `intervalTree.Visit_gen.spec` is stated on
the exact tree (`ownIvtT`, the visited entries a prefix of `RbT.visitL`, for any query); its
form over the entries (`ownIvtK`, a sublist of the overlapping ones, and their prefix for a query
that is not empty-and-finite) follows (`Visit_gen_L`), for `Stab`, `Union` and the string-affine
`Visit`, which state no more. Likewise `Insert` over the entries (`Insert_gen_L`, for `Union`).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Visit_gen
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Insert_gen

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- A visitor told it is called on the overlapping entries (`stab`, a prefix of them for a query
that is not empty-and-finite) is one told it is called on a prefix of `visitL`. -/
theorem adt.ivVisitorOkK_visitL (K : adt.KeyRep (GF := GF)) (dq : DFrac) (T : adt.RbT adt.Entry)
    (b e : GoString) (hs : adt.IvSorted T.inorder) (ivv : GoFunc)
    (I J : List (Loc × adt.Entry) → IProp GF) :
    adt.ivVisitorOkK K dq (adt.stab (b, e) T.inorder) (b = go!"" ∨ adt.affLt b e) ivv I J ⊢
      adt.ivVisitorOkK K dq (T.visitL (b, e)) True ivv I J := by
  unfold adt.ivVisitorOkK
  iintro #H
  imodintro
  iintro %pv %z %acc %Φ'
  imodintro
  iintro ⟨%hpre, HIa, Hpv⟩ HΦ'
  have hp : acc.map Prod.snd ++ [z] <+: T.visitL (b, e) := hpre.2 trivial
  iapply H $$ %pv %z %acc %Φ' [HIa Hpv]
  · iframe
    ipureintro
    refine ⟨hp.sublist.trans (adt.visitL_sublist _ T), fun hq => ?_⟩
    rw [← adt.visit_stab (b, e) hq T hs]; exact hp
  iexact HΦ'

/-- **`Visit` over the entries** (`ownIvtK`): `Visit_gen.spec`'s former statement. -/
theorem adt.Visit_gen_L (h : adt.intervalTree.Visit_gen.spec (GF := GF) (hG := hG)) :
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t : Loc) (L : List adt.Entry) (vb ve : val) (db de : DFrac) (b e : GoString) (dq : DFrac)
    (ivv : GoFunc) (I J : List (Loc × adt.Entry) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvtK K t L dq ∗
      K.keyAt db vb b ∗ K.keyAt de ve e ∗
      adt.ivVisitorOkK K dq (adt.stab (b, e) L) (b = go!"" ∨ adt.affLt b e) ivv I J ∗ I [] }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Visit"))
      (Val #(K.ivl vb ve))) (Val #ivv))
  {{ RET #(); K.keyAt db vb b ∗ K.keyAt de ve e ∗
      ∃ (ps : List Loc) (es : List adt.Entry) (r : Bool),
      ⌜List.Sublist es (adt.stab (b, e) L) ∧ ps.length = es.length ∧
        ((b = go!"" ∨ adt.affLt b e) →
          if r then es = adt.stab (b, e) L else es <+: adt.stab (b, e) L ∧ es ≠ [])⌝ ∗
      (if r then I else J) (ps.zip es) ∗
      (([∗list] x ∈ ps.zip es, K.ivAt x.1 dq x.2) -∗ adt.ownIvtK K t L dq) }} := by
  intro K hK t L vb ve db de b e dq ivv I J
  wp_start_folded as ⟨Ht, Hkb, Hke, #Hivv, HI⟩
  ihave %hs := adt.ownIvtK_sorted K _ _ _ $$ Ht
  icases adt.ownIvtK_T K t L dq $$ Ht with ⟨%T, Ht, %hTL⟩
  subst hTL
  ihave #Hivv' := adt.ivVisitorOkK_visitL K dq T b e hs ivv I J $$ Hivv
  wp_apply (h K hK t T vb ve db de b e dq ivv I J) $$ [Ht Hkb Hke HI]
    as ⟨Hkb, Hke, %ps, %es, %r, %Hp, HIJ, Hw⟩
  · iframe
    iexact Hivv'
  iapply HΦ
  iframe Hkb Hke
  iexists ps, es, r
  iframe HIJ
  isplitl []
  · ipureintro
    obtain ⟨hlen, hr⟩ := Hp
    have hes : List.Sublist es (T.visitL (b, e)) := by
      cases r
      · exact hr.1.sublist
      · simp only [↓reduceIte] at hr; rw [hr]; exact List.Sublist.refl _
    refine ⟨hes.trans (adt.visitL_sublist _ T), hlen, fun hq => ?_⟩
    rw [← adt.visit_stab (b, e) hq T hs]; exact hr
  iintro Hl
  iapply (adt.ownIvtT_K _ _ _ _)
  iapply Hw $$ Hl

/-- **`Insert` over the entries** (`ownIvtK`): `Insert_gen.spec`'s former statement. -/
theorem adt.Insert_gen_L (h : adt.intervalTree.Insert_gen.spec (GF := GF) (hG := hG)) :
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t : Loc) (L : List adt.Entry) (vb ve : val) (b e : GoString) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      adt.ownIvtK K t L (DFrac.own 1) ∗ K.keyAt .discard vb b ∗ K.keyAt .discard ve e ∗
      ⌜L.length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Insert"))
      (Val #(K.ivl vb ve))) (Val #v))
  {{ RET #(); adt.ownIvtK K t (adt.ivtInsert ((b, e), v) L) (DFrac.own 1) }} := by
  intro K hK t L vb ve b e v
  wp_start_folded as ⟨Ht, #Hkb, #Hke, %hlen⟩
  icases adt.ownIvtK_T K t L _ $$ Ht with ⟨%T, Ht, %hTL⟩
  subst hTL
  wp_apply (h K hK t T vb ve b e v) $$ [Ht] as ⟨Ht, %hin⟩
  · iframe Ht
    iframe #
    ipureintro; exact hlen
  iapply HΦ
  rw [← hin]
  iapply adt.ownIvtT_K _ _ _ _ $$ Ht

end lemmas

end EtcdGrove
end Perennial
