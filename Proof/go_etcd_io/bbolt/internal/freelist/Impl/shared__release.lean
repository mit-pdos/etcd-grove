/-
`shared.release(txid)` (U2 internal): the pages pending for transactions up to `txid` merged
into the free ids (`mergeSpans` through the interface).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Release

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

abbrev shared.release.spec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg) (txid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownSh s I.iface fl ∗ I.own fl.free }}
    (App (Val #(methods (go.GoType.PointerType shared.ty) go!"release" #s)) (Val #txid))
  {{ RET #(); ownSh s I.iface (fl.release txid) ∗ I.own (fl.release txid).free }}

theorem shared.release.wp_proof (I : FLImpl (GF := GF)) (hMS : I.MergeSpansSpec) :
    shared.release.spec I := by
  intro s fl txid
  wp_start as ⟨Hsh, Hown⟩
  iunfold ownSh at Hsh
  icases Hsh with ⟨%c, Hsh, %Hok⟩
  iunfold ownShC at Hsh
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
        "Hm" ∷ ml ↦* (((keys.take i).filter (fun t => decide (t.toNat ≤ txid.toNat))).flatMap
          (fun t => (fl.pendingOf t).ids)) ∗
        "Hmcap" ∷ ownSliceCap w64 ml (DFrac.own 1) ∗
        "Hpe" ∷ structFieldRef shared go!"pending" s ↦ pe ∗ "t" ∷ t_ptr ↦ s ∗
        "txid" ∷ txid_ptr ↦ txid ∗
        "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp';dropUpTo (keys.take i) txid fl.pending, ownPend p pd) ∗
        "%Hpp" ∷ ⌜pp' = dropUpTo (keys.take i) txid pp⌝)) $$ Hpending
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [txp tid m Hm Hmcap Hpe t txid Hpds]
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
    · have Hif' : key.toNat ≤ txid.toNat := by word
      have h1 : Std.get? pp' key = some v := by
        show pp' !! key = some v; rw [Hpp, dropUpTo_notvis _ _ Hnot]; exact Hv
      have h2 : Std.get? (dropUpTo (keys.take i) txid fl.pending) key = some pd := by
        show (dropUpTo (keys.take i) txid fl.pending) !! key = some pd
        rw [dropUpTo_notvis _ _ Hnot]; exact hpd
      icases (BigSepM2.bigSepM2_delete h1 h2).1 $$ Hpds with ⟨Hpo, Hpds⟩
      iunfold ownPend at Hpo
      icases Hpo with ⟨-, Hpo⟩
      iunfold ownPending at Hpo
      icases Hpo with ⟨%ids, %atx, Hidsf, Hids, -, -, -, -, -⟩
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
      have Hpo : fl.pendingOf key = pd := by
        simp [FLPg.pendingOf, show fl.pending !! key = some pd from hpd]
      isplitl
      · iexists _, _, ml2
        rw [Htake, List.filter_append, List.flatMap_append, dropUpTo_le _ Hif']
        simp only [List.filter_cons, List.filter_nil, decide_eq_true Hif', ite_true,
          List.flatMap_singleton, Hpo]
        iframe
        ipureintro
        rw [Hpp, dropUpTo_le _ Hif']
      · ipureintro
        intro k hk
        exact GMap.lookup_delete_ne _ (Ne.symm hk)
    · have Hif' : ¬ key.toNat ≤ txid.toNat := by word
      try wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists pp'
      iframe Hmap
      isplitl
      · iexists _, _, _
        rw [Htake, List.filter_append, List.flatMap_append, dropUpTo_gt _ Hif']
        simp only [List.filter_cons, List.filter_nil, decide_eq_false Hif', List.flatMap_nil,
          List.append_nil, Bool.false_eq_true, ite_false]
        iframe
        ipureintro
        rw [Hpp, dropUpTo_gt _ Hif']
      · ipureintro
        intro k _; rfl
  iintro %pp' HP Hmap
  iNamed HP
  try wp_auto
  rw [List.take_length] at Hpp ⊢
  have Hpp' : pp' = pp.filter (fun t _ => decide (txid.toNat < t.toNat)) := by
    rw [Hpp, dropUpTo_all]; intro k hk; exact (Hkset k).2 hk
  have Hgh : dropUpTo keys txid fl.pending =
      fl.pending.filter (fun t _ => decide (txid.toNat < t.toNat)) := by
    apply dropUpTo_all; intro k hk
    exact (Hkset k).2 ((Hdom k).2 hk)
  rw [Hgh]
  have HL := flatIds_keys_filter fl.pending keys txid (fun k => (Hkset k).trans (Hdom k)) Hknodup
  obtain ⟨Hnd, Hge, Hlen, Hfree, Hpend, Halloc, Hwf', Hc'⟩ := release_ok Hok.2 HL
  wp_method_call
  wp_call
  try wp_auto
  unfold FLImpl.iface
  try wp_auto
  wp_apply (hMS fl.free ml _ Hok.2.2.2.1 Hnd (fun x hx => Hok.2.2.1 x (List.mem_append_left _ hx))
      Hge Hlen) $$ [Hown Hm Hmcap] as Hown
  · iframe
  iapply HΦ
  rw [Hfree]
  iframe Hown
  iunfold ownSh
  iexists c
  isplitl
  · iunfold ownShC
    iexists al, ca, pe, pp'
    rw [Hpend, Halloc, Hpp']
    iframe
  · ipureintro
    exact ⟨fun x => (Hok.1 x).trans (Hc' x).symm, Hwf'⟩
end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
