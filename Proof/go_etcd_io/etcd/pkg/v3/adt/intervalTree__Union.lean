module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Union
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Visit
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Insert

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalTree.Union.wp_proof
    (h_Visit : adt.intervalTree.Visit.spec (GF := GF) (hG := hG))
    (h_Insert : adt.intervalTree.Insert.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Union.spec (GF := GF) (hG := hG) := by
  intro t t' L L' q' b e
  wp_start as ⟨Ht, Ht', %hlen, %hq⟩
  wp_auto
  ipersist ivt
  have hS : (adt.stab (b, e) L').length ≤ L'.length := List.length_filter_le _ _
  let I : List (Loc × adt.Entry) → IProp GF := fun acc =>
    iprop(adt.ownIvt t ((acc.map Prod.snd).foldl (fun a z => adt.ivtInsert z a) L) 1 ∗
      [∗list] x ∈ acc,
        x.1 ↦{DFrac.own q'} ({ Ivl' := adt.affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue))
  wp_apply (h_Visit t' L' b e q' _ I hq) $$ [Ht Ht'] as %ps ⟨%hpl, HI, Hwand⟩
  · iframe Ht'
    isplitr [Ht]
    · iunfold adt.ivVisitorOk
      imodintro
      iintro %pv %z %acc %Φ'
      imodintro
      iintro ⟨%hpre, ⟨HIt, Hacc⟩, Hpv⟩ HΦ'
      ihave %Hpvn := typedPointsto_not_null _ _ _ $$ Hpv
      icases typedPointsto_split _ _ _ $$ Hpv with Hpv
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Hpv
      wp_auto
      have hacc : acc.length + 1 ≤ L'.length := by
        have := hpre.length_le
        simp only [List.length_append, List.length_map, List.length_singleton] at this
        omega
      wp_apply (h_Insert t _ z.1.1 z.1.2 z.2) $$ [HIt] as HIt
      · iframe HIt
        ipureintro
        rw [adt.length_foldl_ivtInsert, List.length_map]
        omega
      iapply HΦ'
      simp only [I, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
        List.foldl_cons, List.foldl_nil, Prod.eta]
      iframe HIt
      iapply BigSepL.bigSepL_snoc.2
      iframe Hacc
      iapply typedPointsto_combine _ _ _ Hpvn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    simp only [I, List.map_nil, List.foldl_nil]
    iframe Ht
    iapply BigSepL.bigSepL_nil.2; itrivial
  icases HI with ⟨HIt, Hacc⟩
  rw [List.map_snd_zip (by omega)]
  iapply HΦ
  iexists adt.stab (b, e) L'
  iframe HIt
  isplitl []
  · ipureintro; exact List.Perm.refl _
  iapply Hwand
  iexact Hacc

end proof

end EtcdGrove
end Perennial
