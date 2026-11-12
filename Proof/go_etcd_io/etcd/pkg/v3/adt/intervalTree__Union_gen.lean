/-
`intervalTree.Union` (`interval_tree.go`) over a comparator: the proof of
`Spec/.../adt/intervalTree__Union_gen.lean` (unit 4, generalized in the auth plan's S2b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Union_gen
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Visit_gen
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Insert_gen

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

theorem adt.intervalTree.Union_gen.wp_proof
    (h_Visit_gen : adt.intervalTree.Visit_gen.spec (GF := GF) (hG := hG))
    (h_Insert_gen : adt.intervalTree.Insert_gen.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Union_gen.spec (GF := GF) (hG := hG) := by
  intro K hK t t' L L' q' vb ve db de b e
  wp_start as ⟨Ht, Ht', Hkb, Hke, %hlen, %hq⟩
  wp_auto
  ipersist ivt
  have hS : (adt.stab (b, e) L').length ≤ L'.length := List.length_filter_le _ _
  let I : List (Loc × adt.Entry) → IProp GF := fun acc =>
    iprop(adt.ownIvtK K t ((acc.map Prod.snd).foldl (fun a z => adt.ivtInsert z a) L) (DFrac.own 1) ∗
      [∗list] x ∈ acc, K.ivAt x.1 q' x.2)
  wp_apply (h_Visit_gen K hK t' L' vb ve db de b e q' _ I (fun _ => iprop(False))) $$ [Ht Ht' Hkb Hke]
    as ⟨Hkb, Hke, %ps, %es, %r, %hpl, HI, Hwand⟩
  · iframe Ht' Hkb Hke
    isplitr [Ht]
    · iunfold adt.ivVisitorOkK
      imodintro
      iintro %pv %z %acc %Φ'
      imodintro
      iintro ⟨%hpre, ⟨HIt, Hacc⟩, Hpv⟩ HΦ'
      icases K.ivAt_open_ivl_val _ _ _ $$ Hpv with ⟨%zb, %ze, Hivl, Hv, #Hkzb, #Hkze, Hpvb⟩
      wp_auto
      have hacc : acc.length + 1 ≤ L'.length := by
        have := hpre.1.length_le
        simp only [List.length_append, List.length_map, List.length_singleton] at this
        omega
      wp_apply (h_Insert_gen K hK t _ zb ze z.1.1 z.1.2 z.2) $$ [HIt] as HIt
      · iframe HIt
        iframe #
        ipureintro
        rw [adt.length_foldl_ivtInsert, List.length_map]
        omega
      ispecialize HΦ' $$ %true
      iapply HΦ'
      simp only [I, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
        List.foldl_cons, List.foldl_nil, Prod.eta, ↓reduceIte]
      iframe HIt
      iapply BigSepL.bigSepL_snoc.2
      iframe Hacc
      iapply Hpvb
      iframe
    simp only [I, List.map_nil, List.foldl_nil]
    iframe Ht
    iapply BigSepL.bigSepL_nil.2; itrivial
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso
    iexact HI
  | true =>
    simp only [↓reduceIte]
    obtain ⟨-, hpl, hes⟩ := hpl
    rw [hes hq] at hpl ⊢
    icases HI with ⟨HIt, Hacc⟩
    rw [List.map_snd_zip (by omega)]
    iapply HΦ
    iframe Hkb Hke
    iexists adt.stab (b, e) L'
    iframe HIt
    isplitl []
    · ipureintro; exact List.Perm.refl _
    iapply Hwand
    iexact Hacc


end proof

end EtcdGrove
end Perennial
