module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__releaseRange
public import Proof.go_etcd_io.bbolt.internal.freelist.ReleaseLemmas

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

theorem shared.releaseRange.wp_proof : shared.releaseRange.spec (GF := GF) (hG := hG) := by
  intro I s sv c σ b e hMS
  wp_start as ⟨#Hhdl, Hsh, %Hok, Hown⟩
  unfold ownSharedC
  iNamed Hsh
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_auto
  irename : (begin_ptr ↦ b : IProp GF) => Hbeg
  irename : (end_ptr ↦ e : IProp GF) => Hend
  have Hequiv_refl : ∀ τ : FLState, τ.equiv τ := fun τ =>
    ⟨List.Perm.refl _, List.Perm.refl _, rfl, fun _ => Iff.rfl, fun t p q hp hq => by
      rw [hp] at hq; cases hq; exact Pending.equiv_refl p⟩
  wp_if_destruct
  · iapply HΦ
    isplitr
    · ipureintro
      unfold FLState.releaseRange; rw [if_pos Hif]; exact ⟨Hequiv_refl σ, rfl⟩
    iframe
    isplitr
    · ipureintro; exact Hiface
    ipureintro; exact Hok
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %ml0 ⟨Hm0, Hmcap0⟩
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_mut_keys (fun (keys : List w64) (i : Nat) (pp' : GMap w64 Loc) =>
      iprop(∃ (tp : Loc) (tidv : w64) (ml : GoSlice) (L : List w64) (G : GMap w64 Pending),
        "txp" ∷ txp_ptr ↦ tp ∗ "tid" ∷ tid_ptr ↦ tidv ∗ "m" ∷ m_ptr ↦ ml ∗
        "Hm" ∷ ml ↦* L ∗ "Hmcap" ∷ ownSliceCap w64 ml (DFrac.own 1) ∗
        "Hs" ∷ s ↦ sv ∗ "t" ∷ t_ptr ↦ s ∗ "Hbeg" ∷ begin_ptr ↦ b ∗ "Hend" ∷ end_ptr ↦ e ∗
        "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp';G, ownPending p pd) ∗
        "%HL" ∷ ⌜L.Perm (rrRelKeys σ b e (keys.take i)) ∧
          (∀ k ∈ keys.take i, rrGood σ b e k (G !! k)) ∧
          (∀ k, k ∉ keys.take i → G !! k = σ.pending !! k)⌝)) $$ Hpending
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [txp tid m Hm0 Hmcap0 Hs t Hbeg Hend Hpds]
  · iexists _, _, _, [], σ.pending
    iframe
    isplitl
    · iExactEq Hm0; rfl
    ipureintro
    simp [rrRelKeys]
  isplitr
  · imodintro
    iintro %i %key %v %pp' ⟨%Hkey, %Hv, %Hagree⟩ HP Hmap
    iNamed HP
    have Hnot : key ∉ keys.take i := by
      intro hm
      obtain ⟨j, hj, e'⟩ := List.mem_iff_getElem.1 hm
      simp only [List.length_take, List.getElem_take] at hj e'
      have := list_nodup_getElem?_inj keys Hknodup j i key
        (by rw [List.getElem?_eq_getElem (by omega), e']) Hkey
      omega
    have Htake : keys.take (i + 1) = keys.take i ++ [key] := by
      rw [List.take_add_one, Hkey]; rfl
    obtain ⟨pd, hpd0⟩ := Option.isSome_iff_exists.1
      ((Hdom key).1 (by simp only [show Std.get? pp key = some v from Hv, Option.isSome_some]))
    have hpd : σ.pending !! key = some pd := hpd0
    have Hppk : pp' !! key = some v := by
      rw [Hagree i key (Nat.le_refl _) Hkey]; exact Hv
    have HGk : G !! key = some pd := by rw [HL.2.2 key Hnot]; exact hpd
    -- the entry is not looked at: nothing changes
    have Hskip : rrTouched b e key pd = false →
        L.Perm (rrRelKeys σ b e (keys.take (i + 1))) ∧
        (∀ k ∈ keys.take (i + 1), rrGood σ b e k (G !! k)) ∧
        (∀ k, k ∉ keys.take (i + 1) → G !! k = σ.pending !! k) := by
      intro ht
      refine ⟨?_, fun k hk => ?_, fun k hk => HL.2.2 k (fun h => hk (by rw [Htake]; exact List.mem_append_left _ h))⟩
      · rw [Htake]; unfold rrRelKeys
        simp only [List.flatMap_append, List.flatMap_singleton, hpd, Option.map_some, Option.getD_some]
        unfold rrRelOpt; rw [if_neg (by simp [ht]), List.append_nil]; exact HL.1
      · rw [Htake, List.mem_append, List.mem_singleton] at hk
        rcases hk with hk | rfl
        · exact HL.2.1 k hk
        · unfold rrGood; rw [hpd]; simp only; rw [if_neg (by simp [ht])]; exact HGk
    have hnt_lt : uint.Z key < uint.Z b → rrTouched b e key pd = false := fun h => by
      unfold rrTouched inTxRange; rw [decide_eq_false (by omega), Bool.false_and]
    have hnt_gt : uint.Z e < uint.Z key → rrTouched b e key pd = false := fun h => by
      unfold rrTouched inTxRange; rw [decide_eq_false (by omega), Bool.false_and]
    have hnt_lrb : pd.lastReleaseBegin = b → rrTouched b e key pd = false := fun h => by
      unfold rrTouched; rw [h]; simp
    try wp_auto
    wp_if_destruct
    · try wp_auto
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists pp'
      iframe Hmap
      isplitl
      · iexists _, _, _, L, G
        iframe
        ipureintro; exact Hskip (hnt_lt Hif)
      · ipureintro; intro k _; rfl
    · have hkb : ¬ uint.Z key < uint.Z b := Hif
      wp_if_destruct
      · try wp_auto
        unfold forMapPostcondition
        ileft
        isplitr
        · ipureintro; rfl
        iexists pp'
        iframe Hmap
        isplitl
        · iexists _, _, _, L, G
          iframe
          ipureintro; exact Hskip (hnt_gt Hif)
        · ipureintro; intro k _; rfl
      · have hke : ¬ uint.Z e < uint.Z key := Hif
        have h1 : Std.get? pp' key = some v := Hppk
        have h2 : Std.get? G key = some pd := HGk
        icases (BigSepM2.bigSepM2_delete h1 h2).1 $$ Hpds with ⟨Hpo, Hpds⟩
        iunfold ownPending at Hpo
        iunfold named at Hpo
        icases Hpo with ⟨%tv, Htp, Hids, Hids_cap, Hatx, Hatx_cap, %Hlrb⟩
        try wp_auto
        wp_if_destruct
        · ihave Hpds := (BigSepM2.bigSepM2_delete h1 h2).2 $$ [Htp Hids Hids_cap Hatx Hatx_cap Hpds]
          · iframe; unfold ownPending; iexists tv; iframe; ipureintro; exact Hlrb
          try wp_auto
          unfold forMapPostcondition
          ileft
          isplitr
          · ipureintro; rfl
          iexists pp'
          iframe Hmap
          isplitl
          · iexists _, _, _, L, G
            iframe
            ipureintro; exact Hskip (hnt_lrb Hlrb.symm)
          · ipureintro; intro k _; rfl
        · have hlrb : pd.lastReleaseBegin ≠ b := fun h => Hif (Hlrb.trans h)
          have ht : rrTouched b e key pd = true := by
            unfold rrTouched inTxRange
            rw [decide_eq_true (by omega)]
            simp [hlrb]
          have Hpl : pd.ids.length = pd.alloctx.length := Hok.2.2.2.2.2 key pd hpd
          try wp_auto
          ihave IH : iprop(∃ (j : w64) (Q R : List (w64 × w64)) (tv' : txPending) (ml' : GoSlice),
              "i" ∷ i_ptr ↦ j ∗ "Htp" ∷ v ↦ tv' ∗
              "Hids" ∷ tv'.ids' ↦* Q.map Prod.fst ∗ "Hids_cap" ∷ ownSliceCap w64 tv'.ids' (DFrac.own 1) ∗
              "Hatx" ∷ tv'.alloctx' ↦* Q.map Prod.snd ∗
              "Hatx_cap" ∷ ownSliceCap w64 tv'.alloctx' (DFrac.own 1) ∗
              "m" ∷ m_ptr ↦ ml' ∗ "Hm" ∷ ml' ↦* (L ++ R.map Prod.fst) ∗
              "Hmcap" ∷ ownSliceCap w64 ml' (DFrac.own 1) ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (Q.length : Int) ∧
                (∀ x ∈ Q.take (sint.nat j), inTxRange b e x.2 = false) ∧
                (∀ x ∈ R, inTxRange b e x.2 = true) ∧ (Q ++ R).Perm pd.pairs ∧
                tv'.lastReleaseBegin' = pd.lastReleaseBegin⌝)
              $$ [i Htp Hids Hids_cap Hatx Hatx_cap m Hm Hmcap]
          · iexists W64 0, pd.pairs, [], tv, ml
            rw [pairs_fst Hpl, pairs_snd Hpl]
            simp only [List.map_nil, List.append_nil]
            iframe
            ipureintro
            refine ⟨by word, by word, fun x hx => ?_, fun x hx => by simp at hx, by simp, Hlrb⟩
            rw [show sint.nat (W64 0) = 0 from rfl] at hx; simp at hx
          wp_for IH
          have HQle : Q.length ≤ pd.pairs.length := by
            have := Hj.2.2.2.2.1.length_eq; simp only [List.length_append] at this; omega
          have Hql : pd.pairs.length = pd.ids.length := by
            simp only [Pending.pairs, List.length_zip, Hpl, Nat.min_self]
          have Hidb : pd.ids.length < 2 ^ 63 := by
            have : pd.ids.length ≤ σ.pendingIds.length := by
              rw [pendingIds_eq]
              have := (flatIds_lookup hpd).length_eq
              simp only [List.length_append] at this; omega
            have h4 := Hok.2.2.2.2.1
            unfold FLState.allIds at h4; rw [List.length_append] at h4; omega
          ihave %HQs := ownSlice_len _ _ _ $$ Hids
          ihave %HAs := ownSlice_len _ _ _ $$ Hatx
          simp only [List.length_map] at HQs HAs
          wp_if_destruct
          · have Hb : sint.nat j < Q.length := by word
            list_elem Q (sint.nat j) as x
            have Hxs : (Q.map Prod.snd)[sint.nat j]? = some x.2 := by simp [Hx_lookup]
            have Hxf : (Q.map Prod.fst)[sint.nat j]? = some x.1 := by simp [Hx_lookup]
            rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
            wp_apply wp_load_slice_index _ (sint.Z j) _ _ x.2 Hj.1 $$ [Hatx] with Hatx
            · iframe; ipureintro; exact Hxs
            try wp_auto
            wp_if_destruct
            · try wp_auto
              wp_for_post
              iframe
              iexists j + W64 1, Q, R, tv', ml'
              iframe
              ipureintro
              have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
              rw [hj1, List.take_add_one, Hx_lookup]
              refine ⟨by word, by word, fun z hz => ?_, Hj.2.2.2.1, Hj.2.2.2.2.1, Hj.2.2.2.2.2⟩
              simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hz
              rcases hz with hz | rfl
              · exact Hj.2.2.1 z hz
              · unfold inTxRange; exact decide_eq_false (by omega)
            · have hxb : ¬ uint.Z x.2 < uint.Z b := Hif
              wp_if_destruct
              · try wp_auto
                wp_for_post
                iframe
                iexists j + W64 1, Q, R, tv', ml'
                iframe
                ipureintro
                have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
                rw [hj1, List.take_add_one, Hx_lookup]
                refine ⟨by word, by word, fun z hz => ?_, Hj.2.2.2.1, Hj.2.2.2.2.1, Hj.2.2.2.2.2⟩
                simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hz
                rcases hz with hz | rfl
                · exact Hj.2.2.1 z hz
                · unfold inTxRange; exact decide_eq_false (by omega)
              · have hin : inTxRange b e x.2 = true := by
                  unfold inTxRange; exact decide_eq_true (by omega)
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
                wp_apply wp_load_slice_index _ (sint.Z j) _ _ x.1 Hj.1 $$ [Hids] with Hids
                · iframe; ipureintro; exact Hxf
                try wp_auto
                wp_apply wp_slice_literal
                isplitr
                · ipureintro; rfl
                iintro %sl ⟨Hsl, -⟩
                wp_apply wp_slice_append $$ [Hm Hmcap Hsl] as %ml2 ⟨Hm, Hmcap, -⟩
                · iframe
                try wp_auto
                ihave %HQw := ownSlice_wf _ _ _ $$ Hids
                ihave %HAw := ownSlice_wf _ _ _ $$ Hatx
                have Hql1 : Q.length - 1 < Q.length := by omega
                list_elem Q (Q.length - 1) as y
                have hli : sint.Z (tv'.ids'.len - W64 1) = ((Q.length - 1 : Nat) : Int) := by word
                have hla : sint.Z (tv'.alloctx'.len - W64 1) = ((Q.length - 1 : Nat) : Int) := by word
                rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
                wp_apply wp_load_slice_index _ (sint.Z (tv'.ids'.len - W64 1)) _ _ y.1 (by word) $$ [Hids]
                  with Hids
                · iframe; ipureintro; rw [hli]; simp [Hy_lookup]
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
                wp_apply wp_store_slice_index _ (sint.Z j) _ y.1 $$ [Hids] as Hids
                · iframe; ipureintro; exact ⟨Hj.1, by simp only [List.length_map]; word⟩
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
                icases (ownSlice_split_all (tv'.ids'.len - W64 1) _ _ _ ⟨by word, by word⟩).1 $$ Hids
                  with ⟨Hids, Hids2⟩
                ihave Hids_cap := ownSlice_slice_absorb_capacity _ _ (W64 0) (tv'.ids'.len - W64 1)
                  ⟨by decide, by word, by word⟩ $$ [Hids2 Hids_cap]
                · iframe
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
                wp_apply wp_load_slice_index _ (sint.Z (tv'.alloctx'.len - W64 1)) _ _ y.2 (by word)
                  $$ [Hatx] with Hatx
                · iframe; ipureintro; rw [hla]; simp [Hy_lookup]
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
                wp_apply wp_store_slice_index _ (sint.Z j) _ y.2 $$ [Hatx] as Hatx
                · iframe; ipureintro; exact ⟨Hj.1, by simp only [List.length_map]; word⟩
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
                icases (ownSlice_split_all (tv'.alloctx'.len - W64 1) _ _ _ ⟨by word, by word⟩).1 $$ Hatx
                  with ⟨Hatx, Hatx2⟩
                ihave Hatx_cap := ownSlice_slice_absorb_capacity _ _ (W64 0) (tv'.alloctx'.len - W64 1)
                  ⟨by decide, by word, by word⟩ $$ [Hatx2 Hatx_cap]
                · iframe
                try wp_auto
                wp_for_post
                have hQf : ((Q.map Prod.fst).set (sint.Z j).toNat y.1).take (sint.nat (tv'.ids'.len - W64 1)) =
                    ((Q.set (sint.nat j) y).take (Q.length - 1)).map Prod.fst := by
                  rw [List.map_take, List.map_set, show sint.nat (tv'.ids'.len - W64 1) = Q.length - 1 by word]
                have hQs : ((Q.map Prod.snd).set (sint.Z j).toNat y.2).take
                    (sint.nat (tv'.alloctx'.len - W64 1)) =
                    ((Q.set (sint.nat j) y).take (Q.length - 1)).map Prod.snd := by
                  rw [List.map_take, List.map_set,
                    show sint.nat (tv'.alloctx'.len - W64 1) = Q.length - 1 by word]
                rw [hQf, hQs]
                iframe
                iexists (j - W64 1 + W64 1), (Q.set (sint.nat j) y).take (Q.length - 1), R ++ [x], _, ml2
                iframe
                isplitl [Hm]
                · iExactEq Hm; simp
                ipureintro
                have hj' : sint.nat (j - W64 1 + W64 1) = sint.nat j := by word
                have hy := (List.getElem?_eq_some_iff.1 Hy_lookup).2
                have hx := (List.getElem?_eq_some_iff.1 Hx_lookup).2
                have hsw := swap_take_perm Q (sint.nat j) Hb
                rw [hy, hx] at hsw
                rw [hj']
                refine ⟨by word, by simp only [List.length_take, List.length_set]; word, ?_, ?_, ?_, ?_⟩
                · rw [List.take_take, Nat.min_eq_left (by omega), List.take_set_of_le (Nat.le_refl _)]
                  exact Hj.2.2.1
                · intro z hz
                  rcases List.mem_append.1 hz with hz | hz
                  · exact Hj.2.2.2.1 z hz
                  · rw [List.mem_singleton] at hz; subst hz; exact hin
                · have : ((Q.set (sint.nat j) y).take (Q.length - 1) ++ (R ++ [x])).Perm
                      (((Q.set (sint.nat j) y).take (Q.length - 1) ++ [x]) ++ R) := by
                    rw [List.append_assoc]; exact List.Perm.append_left _ List.perm_append_comm
                  exact this.trans ((hsw.append_right R).trans Hj.2.2.2.2.1)
                · exact Hj.2.2.2.2.2
          · have Hjq : sint.nat j = Q.length := by word
            rw [Hjq, List.take_length] at Hj
            obtain ⟨-, -, Hout, Hin, Hperm, Hlrb'⟩ := Hj
            obtain ⟨HQk, HRr⟩ := part_perm (p := fun x => inTxRange b e x.2) Hout Hin Hperm
            have HLn : (L ++ R.map Prod.fst).Perm (rrRelKeys σ b e (keys.take (i + 1))) := by
              rw [Htake]; unfold rrRelKeys
              rw [List.flatMap_append]
              refine List.Perm.append HL.1 ?_
              simp only [List.flatMap_singleton, hpd, Option.map_some, Option.getD_some]
              unfold rrRelOpt; rw [if_pos ht]
              unfold rrRel; exact HRr.map _
            have Hrest : ∀ (G' : GMap w64 Pending), (∀ k, k ≠ key → G' !! k = G !! k) →
                (∀ k ∈ keys.take i, rrGood σ b e k (G' !! k)) ∧
                (∀ k, k ∉ keys.take (i + 1) → G' !! k = σ.pending !! k) := by
              intro G' hG'
              refine ⟨fun k hk => ?_, fun k hk => ?_⟩
              · have hne : k ≠ key := fun h => Hnot (h ▸ hk)
                rw [hG' k hne]; exact HL.2.1 k hk
              · have hne : k ≠ key := fun h => hk (by rw [Htake, h]; simp)
                rw [hG' k hne]
                exact HL.2.2 k (fun h => hk (by rw [Htake]; exact List.mem_append_left _ h))
            try wp_auto
            have HkeepP : (rrKeep b e pd).pairs.Perm Q := by rw [rrKeep_pairs]; exact HQk.symm
            wp_if_destruct
            · -- nothing left: the entry goes
              have HQ0 : Q = [] := List.eq_nil_of_length_eq_zero (by word)
              subst HQ0
              have Hk0 : (rrKeep b e pd).ids = [] := by
                have := HkeepP.length_eq
                simp only [List.length_nil] at this
                have h2 := rrKeep_len b e pd
                have h3 : (rrKeep b e pd).pairs.length = (rrKeep b e pd).ids.length := by
                  simp [Pending.pairs, h2]
                exact List.eq_nil_of_length_eq_zero (by omega)
              try wp_auto
              wp_apply wp_mapDelete $$ [Hmap] as Hmap
              · iexact Hmap
              unfold forMapPostcondition
              iright; ileft
              isplitr
              · ipureintro; rfl
              iexists (GMap.delete key pp')
              iframe Hmap
              obtain ⟨Hr1, Hr2⟩ := Hrest (GMap.delete key G) (fun k hk => GMap.lookup_delete_ne _ (Ne.symm hk))
              isplitl
              · iexists _, _, _, (L ++ R.map Prod.fst), (GMap.delete key G)
                iframe
                ipureintro
                refine ⟨HLn, fun k hk => ?_, Hr2⟩
                rw [Htake, List.mem_append, List.mem_singleton] at hk
                rcases hk with hk | rfl
                · exact Hr1 k hk
                · unfold rrGood; rw [hpd]; simp only; rw [if_pos ht, GMap.lookup_delete]; exact Hk0
              · ipureintro; intro k hk; exact GMap.lookup_delete_ne _ (Ne.symm hk)
            · -- the entry stays, with what is left
              have HQne : Q ≠ [] := by
                intro h; subst h; apply Hif; simp only [List.length_nil] at HQs; word
              try wp_auto
              unfold forMapPostcondition
              iright; ileft
              isplitr
              · ipureintro; rfl
              iexists pp'
              iframe Hmap
              have hq : Pending.equiv ⟨Q.map Prod.fst, Q.map Prod.snd, b⟩ (rrKeep b e pd) := by
                refine ⟨?_, rfl⟩
                rw [pairs_of_list]; exact HkeepP.symm
              obtain ⟨Hr1, Hr2⟩ := Hrest (<[key := ⟨Q.map Prod.fst, Q.map Prod.snd, b⟩]> G)
                (fun k hk => GMap.lookup_insert_ne _ _ (Ne.symm hk))
              isplitl
              · iexists _, _, _, (L ++ R.map Prod.fst), (<[key := ⟨Q.map Prod.fst, Q.map Prod.snd, b⟩]> G)
                iframe
                isplitl
                · rw [← GMap.insert_id pp' key v Hppk]
                  iapply (BigSepM2.bigSepM2_insert_delete).2
                  isplitl [Htp Hids Hids_cap Hatx Hatx_cap]
                  · unfold ownPending
                    iexists _
                    simp only [named]
                    iframe
                    ipureintro; rfl
                  rw [GMap.insert_id pp' key v Hppk]
                  iframe
                ipureintro
                refine ⟨HLn, fun k hk => ?_, Hr2⟩
                rw [Htake, List.mem_append, List.mem_singleton] at hk
                rcases hk with hk | rfl
                · exact Hr1 k hk
                · unfold rrGood; rw [hpd]; simp only; rw [if_pos ht, GMap.lookup_insert]
                  exact ⟨hq, by simpa using HQne, by simp⟩
              · ipureintro; intro k _; rfl
  iintro %pp' HP Hmap
  iNamed HP
  rw [List.take_length] at HL
  have hkσ : ∀ k, k ∈ keys ↔ (σ.pending !! k).isSome := fun k => (Hkset k).trans (Hdom k)
  have HG : ∀ k, rrGood σ b e k (G !! k) := by
    intro k
    by_cases hk : k ∈ keys
    · exact HL.2.1 k hk
    · have h1 := HL.2.2 k hk
      have h2 : σ.pending !! k = none := by
        cases h : σ.pending !! k
        · rfl
        · exact absurd ((hkσ k).2 (by simp [h])) hk
      unfold rrGood; rw [h2]; simp only; rw [h1, h2]
  obtain ⟨-, ⟨Hnd, Hge, Hlen⟩, Hfin⟩ := releaseRange_ok (free' := σ.free) Hok.2 Hif hkσ Hknodup HG HL.1
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  rw [Hiface]
  unfold FLImpl.iface
  try wp_auto
  wp_bind (App (Val #(methods I.ity go!"mergeSpans" I.iv)) (Val #ml))
  iapply (hMS s σ.free ml L Hnd Hge Hlen) $$ [Hown Hm Hmcap]
  · iframe; iexact Hpkg
  inext
  iintro %free' ⟨%Hfr, Hown⟩
  try wp_auto
  obtain ⟨-, -, Hfin'⟩ := releaseRange_ok (free' := free') Hok.2 Hif hkσ Hknodup HG HL.1
  obtain ⟨Hwf', Hc', He⟩ := Hfin' Hfr.2 Hfr.1
  ispecialize HΦ $$ %({ σ with free := free', pending := G } : FLState)
  iapply HΦ
  isplitr
  · ipureintro; exact ⟨He, rfl⟩
  iframe
  isplitr
  · ipureintro; first | exact Hiface | rfl
  ipureintro
  exact ⟨fun x => (Hok.1 x).trans (Hc' x).symm, Hwf'⟩

end proof

end bbolt
end EtcdGrove
end Perennial
