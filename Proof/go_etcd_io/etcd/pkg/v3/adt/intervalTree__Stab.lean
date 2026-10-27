/-
`intervalTree.Stab` (`interval_tree.go`) over string-affine keys: the generic proof
(`intervalTree__Stab_gen.lean`) instantiated for `strKey` (the auth plan's S2b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Stab
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Stab_gen
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

theorem adt.intervalTree.Stab.wp_proof
    (h_Stab_gen : adt.intervalTree.Stab_gen.spec (GF := GF) (hG := hG))
    (h_StringAffineComparable_Compare :
      adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Stab.spec (GF := GF) (hG := hG) := by
  intro t L b e q
  unfold adt.ownIvt
  rw [adt.affIvl_eq (GF := GF)]
  wp_start_folded as ⟨Ht, %hq⟩
  wp_apply (h_Stab_gen adt.strKey (adt.strKey_ok h_StringAffineComparable_Compare) t L #b #e
    .discard .discard b e (DFrac.own q)) $$ [Ht] as %ivs %ps ⟨-, -, Hivs, Hcap, %hpl, Hacc, Hwand⟩
  · simp only [adt.strKey_keyAt]
    iframe Ht
    all_goals (try (isplitl []; · ipureintro; trivial))
    all_goals (try (isplitl []; · ipureintro; trivial))
    all_goals (try (ipureintro; exact hq))
  ispecialize HΦ $$ %ivs %ps
  iapply HΦ
  iframe Hivs Hcap
  isplitl []
  · ipureintro; exact hpl
  isplitl [Hacc]
  · iapply adt.strKey_bigSep_ivAt_nn $$ Hacc
  iintro Hlent
  iapply Hwand
  iapply (adt.strKey_bigSep_ivAt _ _).2 $$ Hlent

end proof

end EtcdGrove
end Perennial
