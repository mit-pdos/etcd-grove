/-
`intervalTree.Visit` (`interval_tree.go`) over string-affine keys, for a visitor that goes on: the
generic proof (`intervalTree__Visit_gen.lean`) instantiated for `strKey` (the auth plan's S2b).
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Visit
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Visit_gen
public import Proof.go_etcd_io.etcd.pkg.v3.adt.StrKey

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalTree.Visit.wp_proof
    (h_Visit_gen : adt.intervalTree.Visit_gen.spec (GF := GF) (hG := hG))
    (h_StringAffineComparable_Compare :
      adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Visit.spec (GF := GF) (hG := hG) := by
  intro t L b e q ivv I hq
  unfold adt.ownIvt
  rw [adt.affIvl_eq (GF := GF)]
  wp_start_folded as ⟨Ht, #Hivv, HI⟩
  wp_apply (h_Visit_gen adt.strKey (adt.strKey_ok h_StringAffineComparable_Compare) t L #b #e
    .discard .discard b e (DFrac.own q) ivv I (fun _ => iprop(False))) $$ [Ht HI]
    as ⟨-, -, %ps, %es, %r, %hpl, HI, Hwand⟩
  · simp only [adt.strKey_keyAt]
    iframe Ht HI
    all_goals (try (isplitl []; · ipureintro; trivial))
    all_goals (try (isplitl []; · ipureintro; trivial))
    -- the visitor that goes on, as one that may stop
    iunfold adt.ivVisitorOkK
    imodintro
    iintro %pv %z %acc %Φ'
    imodintro
    iintro ⟨%hpre, HIa, Hiv⟩ HΦ'
    icases (adt.strKey_ivAt _ _ _).1 $$ Hiv with Hiv
    ihave Hivv' := Hivv
    iunfold adt.ivVisitorOk at Hivv'
    ispecialize Hivv' $$ %pv %z %acc
    -- `wp_apply` of the hypothesis admits silently here (its post is `RET #true`, the
    -- continuation's is over any Boolean): applied by hand
    iapply Hivv' $$ [HIa Hiv]
    · iframe; ipureintro; exact hpre.2 hq
    inext
    iintro HIa
    (try wp_auto)
    ispecialize HΦ' $$ %true
    iapply HΦ'
    simp only [↓reduceIte]
    iexact HIa
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso; iexact HI
  | true =>
    simp only [↓reduceIte]
    obtain ⟨-, hpl, hes⟩ := hpl
    rw [hes hq] at hpl ⊢
    ispecialize HΦ $$ %ps
    iapply HΦ
    iframe HI
    isplitl []
    · ipureintro; exact hpl
    iintro Hlent
    iapply Hwand
    iapply (adt.strKey_bigSep_ivAt _ _).2 $$ Hlent

end proof

end EtcdGrove
end Perennial
