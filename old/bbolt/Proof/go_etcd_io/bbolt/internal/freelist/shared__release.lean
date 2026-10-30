module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__release

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.release.wp_proof : shared.release.spec (GF := GF) (hG := hG) := by
  intro I s sv c σ txid hMS
  wp_start as ⟨#Hhdl, Hsh, %Hok, Hown⟩
  unfold ownSharedC
  iNamed Hsh
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_auto
  wp_apply (wp_slice_make2 (V := w64) (W64 0)) as %ml ⟨Hm, Hmcap⟩
  · ipureintro; word
  try wp_auto
  rw [show List.replicate 0 (zero_val w64) = [] from rfl]
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_mut_keys (fun (keys : List w64) (i : Nat) (pp' : GMap w64 Loc) =>
      iprop(∃ (tp : Loc) (tidv : w64) (ml : GoSlice),
        "txp" ∷ txp_ptr ↦ tp ∗ "tid" ∷ tid_ptr ↦ tidv ∗ "m" ∷ m_ptr ↦ ml ∗
        "Hm" ∷ ml ↦* (((keys.take i).filter (fun t => decide (uint.Z t ≤ uint.Z txid))).flatMap
          (fun t => (σ.pendingOf t).ids)) ∗
        "Hmcap" ∷ ownSliceCap w64 ml (DFrac.own 1) ∗
        "Hs" ∷ s ↦ sv ∗ "t" ∷ t_ptr ↦ s ∗ "txid" ∷ txid_ptr ↦ txid ∗
        "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp';dropUpTo (keys.take i) txid σ.pending, ownPending p pd) ∗
        "%Hpp" ∷ ⌜pp' = dropUpTo (keys.take i) txid pp⌝)) $$ Hpending
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [txp tid m Hm Hmcap Hs t txid Hpds]
  · iexists _, _, ml
    simp only [List.take_zero, List.filter_nil, List.flatMap_nil, dropUpTo_nil]
    iframe
  isplitr
  · imodintro
    iintro %i %key %v %pp' ⟨%Hkey, %Hv, %Hagree⟩ HP Hmap
    iNamed HP
    have Hnot : key ∉ keys.take i := by
      intro hm
      obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hm
      simp only [List.length_take, List.getElem_take] at hj e
      have := list_nodup_getElem?_inj keys Hknodup j i key
        (by rw [List.getElem?_eq_getElem (by omega), e]) Hkey
      omega
    have Htake : keys.take (i + 1) = keys.take i ++ [key] := by
      rw [List.take_add_one, Hkey]; rfl
    obtain ⟨pd, hpd⟩ := Option.isSome_iff_exists.1
      ((Hdom key).1 (by simp only [show Std.get? pp key = some v from Hv, Option.isSome_some]))
    try wp_auto
    wp_if_destruct
    · have h1 : Std.get? pp' key = some v := by
        show pp' !! key = some v; rw [Hpp, dropUpTo_notvis _ _ Hnot]; exact Hv
      have h2 : Std.get? (dropUpTo (keys.take i) txid σ.pending) key = some pd := by
        show (dropUpTo (keys.take i) txid σ.pending) !! key = some pd
        rw [dropUpTo_notvis _ _ Hnot]; exact hpd
      icases (BigSepM2.bigSepM2_delete h1 h2).1 $$ Hpds with ⟨Hpo, Hpds⟩
      iunfold ownPending at Hpo
      iunfold named at Hpo
      icases Hpo with ⟨%tv, Htp, Hids, -, -, -, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [Hm Hmcap Hids] as %ml2 ⟨Hm, Hmcap, -⟩
      · iframe
      try wp_auto
      wp_apply wp_mapDelete $$ [Hmap] as Hmap
      · iexact Hmap
      try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists (GMap.delete key pp')
      iframe Hmap
      have Hpo : σ.pendingOf key = pd := by
        simp [FLState.pendingOf, show σ.pending !! key = some pd from hpd]
      isplitl
      · iexists _, _, ml2
        rw [Htake, List.filter_append, List.flatMap_append, dropUpTo_le _ Hif]
        simp only [List.filter_cons, List.filter_nil, decide_eq_true Hif, ite_true,
          List.flatMap_singleton, Hpo]
        iframe
        ipureintro
        rw [Hpp, dropUpTo_le _ Hif]
      · ipureintro
        intro k hk
        exact GMap.lookup_delete_ne _ (Ne.symm hk)
    · try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists pp'
      iframe Hmap
      isplitl
      · iexists _, _, _
        rw [Htake, List.filter_append, List.flatMap_append, dropUpTo_gt _ Hif]
        simp only [List.filter_cons, List.filter_nil, decide_eq_false Hif, List.flatMap_nil,
          List.append_nil, Bool.false_eq_true, ite_false]
        iframe
        ipureintro
        rw [Hpp, dropUpTo_gt _ Hif]
      · ipureintro
        intro k _; rfl
  iintro %pp' HP Hmap
  iNamed HP
  try wp_auto
  rw [List.take_length] at Hpp ⊢
  have Hpp' : pp' = pp.filter (fun t _ => !decide (uint.Z t ≤ uint.Z txid)) := by
    rw [Hpp, dropUpTo_all]; intro k hk; exact (Hkset k).2 hk
  have Hgh : dropUpTo keys txid σ.pending =
      σ.pending.filter (fun t _ => !decide (uint.Z t ≤ uint.Z txid)) := by
    apply dropUpTo_all; intro k hk
    exact (Hkset k).2 ((Hdom k).2 hk)
  rw [Hgh]
  have HL : ((keys.filter (fun t => decide (uint.Z t ≤ uint.Z txid))).flatMap
      (fun t => (σ.pendingOf t).ids)).Perm
      (flatIds (σ.pending.filter (fun t _ => decide (uint.Z t ≤ uint.Z txid)))) := by
    have := flatIds_keys (σ.pending.filter (fun t _ => decide (uint.Z t ≤ uint.Z txid)))
      (keys.filter (fun t => decide (uint.Z t ≤ uint.Z txid)))
      (fun k => by
        rw [List.mem_filter, lookup_filter, Hkset k]
        have := Hdom k
        simp only [show Std.get? pp k = pp !! k from rfl,
          show Std.get? σ.pending k = σ.pending !! k from rfl] at this
        rw [this]
        cases σ.pending !! k <;> simp [Option.filter])
      (Hknodup.sublist List.filter_sublist)
    refine List.Perm.trans (List.Perm.of_eq (flatMap_congr_mem fun t ht => ?_)) this
    rw [List.mem_filter] at ht
    unfold FLState.pendingOf
    rw [lookup_filter]
    cases σ.pending !! t with
    | none => rfl
    | some v => simp only [Option.filter, ht.2, ite_true, if_true, Option.getD_some]
  obtain ⟨-, Hnd, Hge, Hlen⟩ := release_pre Hok.2 HL
  wp_method_call
  wp_call
  try wp_auto
  rw [Hiface]
  unfold FLImpl.iface
  try wp_auto
  wp_bind (App (Val #(methods I.ity go!"mergeSpans" I.iv)) (Val #ml))
  iapply (hMS s σ.free ml _ Hnd Hge Hlen) $$ [Hown Hm Hmcap]
  · iframe; iexact Hpkg
  inext
  iintro %free' ⟨%Hfr, Hown⟩
  try wp_auto
  obtain ⟨Hwf', Hc', He⟩ := release_ok (free' := free') Hok.2 HL Hfr.2 Hfr.1
  ispecialize HΦ $$ %(σ.releasedState txid free')
  iapply HΦ
  isplitr
  · ipureintro; exact ⟨He, rfl⟩
  unfold FLState.releasedState at Hwf' Hc' ⊢
  iframe
  isplitr
  · ipureintro; first | exact Hiface | rfl
  ipureintro
  exact ⟨fun x => (Hok.1 x).trans (Hc' x).symm, Hwf'⟩

end proof

end bbolt
end EtcdGrove
end Perennial
