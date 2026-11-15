/-
`shared.releaseRange(begin, end)` (U2 internal), over the code's model `FLPg.releaseRangeGo`
(`Lemmas/ReleaseGo.lean`: the kept pairs in the order the code's swap-removal leaves them).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.ReleaseGo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

/-- Two lists, one of elements failing `p` and one of elements satisfying it, together a
permutation of `L`: each is `L`'s part, up to order. -/
theorem part_perm {α : Type} {p : α → Bool} {l₁ l₂ L : List α} (h₁ : ∀ x ∈ l₁, p x = false)
    (h₂ : ∀ x ∈ l₂, p x = true) (h : (l₁ ++ l₂).Perm L) :
    l₁.Perm (L.filter (fun x => !p x)) ∧ l₂.Perm (L.filter p) := by
  have a := h.filter (fun x => !p x)
  have b := h.filter p
  rw [List.filter_append, List.filter_eq_self.2 (by simpa using h₁),
    List.filter_eq_nil_iff.2 (by simpa using h₂), List.append_nil] at a
  rw [List.filter_append, List.filter_eq_nil_iff.2 (by simpa using h₁),
    List.filter_eq_self.2 (by simpa using h₂), List.nil_append] at b
  exact ⟨a, b⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

abbrev shared.releaseRange.spec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg) (b e : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownSh s I.iface fl ∗ I.own fl.free }}
    (App (App (Val #(methods (go.GoType.PointerType shared.ty) go!"releaseRange" #s)) (Val #b))
      (Val #e))
  {{ RET #(); ownSh s I.iface (fl.releaseRangeGo b e) ∗ I.own (fl.releaseRangeGo b e).free }}

theorem shared.releaseRange.wp_proof (I : FLImpl (GF := GF)) (hMS : I.MergeSpansSpec) :
    shared.releaseRange.spec I := by
  intro s fl b e
  wp_start as ⟨Hsh, Hown⟩
  iunfold ownSh at Hsh
  icases Hsh with ⟨%c, Hsh, %Hok⟩
  iunfold ownShC at Hsh
  iNamed Hsh
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_auto
  irename : (begin_ptr ↦ b : IProp GF) => Hbeg
  irename : (end_ptr ↦ e : IProp GF) => Hend
  wp_if_destruct
  · have Hlt : e.toNat < b.toNat := by word
    rw [releaseRangeGo_empty Hlt]
    iapply HΦ
    iframe
    iunfold ownSh
    iexists c
    isplitl
    · iunfold ownShC; iexists al, ca, pe, pp; iframe
    · ipureintro; exact Hok
  have Hbe : ¬ e.toNat < b.toNat := by word
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
        "Hpe" ∷ structFieldRef shared go!"pending" s ↦ pe ∗
        "t" ∷ t_ptr ↦ s ∗ "Hbeg" ∷ begin_ptr ↦ b ∗ "Hend" ∷ end_ptr ↦ e ∗
        "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp';G, ownPend p pd) ∗
        "%HL" ∷ ⌜L.Perm ((keys.take i).flatMap fun t =>
            ((fl.pending !! t).map (rrRelGo b e t)).getD []) ∧
          (∀ k ∈ keys.take i, G !! k = (fl.pending !! k).bind (rrEntryGo b e k)) ∧
          (∀ k, k ∉ keys.take i → G !! k = fl.pending !! k)⌝)) $$ Hpending
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [txp tid m Hm0 Hmcap0 Hpe t Hbeg Hend Hpds]
  · iexists _, _, _, [], fl.pending
    iframe
    isplitl
    · iExactEq Hm0; rfl
    ipureintro
    simp
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
    have hpd : fl.pending !! key = some pd := hpd0
    have Hppk : pp' !! key = some v := by
      rw [Hagree i key (Nat.le_refl _) Hkey]; exact Hv
    have HGk : G !! key = some pd := by rw [HL.2.2 key Hnot]; exact hpd
    have Hskip : rrSel b e key pd = false →
        L.Perm ((keys.take (i + 1)).flatMap fun t =>
            ((fl.pending !! t).map (rrRelGo b e t)).getD []) ∧
        (∀ k ∈ keys.take (i + 1), G !! k = (fl.pending !! k).bind (rrEntryGo b e k)) ∧
        (∀ k, k ∉ keys.take (i + 1) → G !! k = fl.pending !! k) := by
      intro ht
      refine ⟨?_, fun k hk => ?_,
        fun k hk => HL.2.2 k (fun h => hk (by rw [Htake]; exact List.mem_append_left _ h))⟩
      · rw [Htake, List.flatMap_append]
        simp only [List.flatMap_singleton, hpd, Option.map_some, Option.getD_some]
        unfold rrRelGo; rw [if_neg (by simp [ht]), List.append_nil]; exact HL.1
      · rw [Htake, List.mem_append, List.mem_singleton] at hk
        rcases hk with hk | rfl
        · exact HL.2.1 k hk
        · rw [HGk, hpd]; simp only [Option.bind_some]; unfold rrEntryGo
          rw [if_neg (by simp [ht])]
    have hnt_lt : key.toNat < b.toNat → rrSel b e key pd = false := fun h => by
      unfold rrSel; exact decide_eq_false (by omega)
    have hnt_gt : e.toNat < key.toNat → rrSel b e key pd = false := fun h => by
      unfold rrSel; exact decide_eq_false (by omega)
    have hnt_lrb : pd.lastReleaseBegin = b → rrSel b e key pd = false := fun h => by
      unfold rrSel; exact decide_eq_false (fun h' => h'.2.2 h)
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
        ipureintro; exact Hskip (hnt_lt (by word))
      · ipureintro; intro k _; rfl
    · have hkb : ¬ key.toNat < b.toNat := by word
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
          ipureintro; exact Hskip (hnt_gt (by word))
        · ipureintro; intro k _; rfl
      · have hke : ¬ e.toNat < key.toNat := by word
        have h1 : Std.get? pp' key = some v := Hppk
        have h2 : Std.get? G key = some pd := HGk
        icases (BigSepM2.bigSepM2_delete h1 h2).1 $$ Hpds with ⟨Hpo, Hpds⟩
        iunfold ownPend at Hpo
        icases Hpo with ⟨%Hvnn, Hpo⟩
        iunfold ownPending at Hpo
        icases Hpo with ⟨%ids, %atx, Hidsf, Hids, Hids_cap, Hatxf, Hatx, Hatx_cap, Hlrb⟩
        try wp_auto
        wp_if_destruct
        · ihave Hpds := (BigSepM2.bigSepM2_delete h1 h2).2
            $$ [Hidsf Hids Hids_cap Hatxf Hatx Hatx_cap Hlrb Hpds]
          · iframe
            iunfold ownPend
            isplitr
            · ipureintro; exact Hvnn
            iunfold ownPending; iexists ids, atx; iframe
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
            ipureintro; first | exact Hskip (hnt_lrb rfl) | exact Hskip (hnt_lrb ‹_›)
          · ipureintro; intro k _; rfl
        · have hlrb : pd.lastReleaseBegin ≠ b := ‹_›
          have ht : rrSel b e key pd = true := by
            unfold rrSel; exact decide_eq_true ⟨by omega, by omega, hlrb⟩
          have Hpl : pd.ids.length = pd.alloctx.length := Hok.2.2.2.2.2 key pd hpd
          have Hfst : (pd.ids.zip pd.alloctx).map Prod.fst = pd.ids := List.map_fst_zip (by omega)
          have Hsnd : (pd.ids.zip pd.alloctx).map Prod.snd = pd.alloctx :=
            List.map_snd_zip (by omega)
          try wp_auto
          ihave IH : iprop(∃ (j : w64) (Q R : List (w64 × w64)) (ids' atx' : GoSlice)
                (ml' : GoSlice),
              "i" ∷ i_ptr ↦ j ∗
              "Hidsf" ∷ structFieldRef txPending go!"ids" v ↦ ids' ∗
              "Hids" ∷ ids' ↦* Q.map Prod.fst ∗ "Hids_cap" ∷ ownSliceCap w64 ids' (DFrac.own 1) ∗
              "Hatxf" ∷ structFieldRef txPending go!"alloctx" v ↦ atx' ∗
              "Hatx" ∷ atx' ↦* Q.map Prod.snd ∗
              "Hatx_cap" ∷ ownSliceCap w64 atx' (DFrac.own 1) ∗
              "m" ∷ m_ptr ↦ ml' ∗ "Hm" ∷ ml' ↦* (L ++ R.map Prod.fst) ∗
              "Hmcap" ∷ ownSliceCap w64 ml' (DFrac.own 1) ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (Q.length : Int) ∧
                srLoop b e (sint.nat j) Q = srLoop b e 0 (pd.ids.zip pd.alloctx) ∧
                (∀ x ∈ R, inRR b e x = true) ∧ (Q ++ R).Perm (pd.ids.zip pd.alloctx)⌝)
              $$ [i Hidsf Hids Hids_cap Hatxf Hatx Hatx_cap m Hm Hmcap]
          · iexists W64 0, (pd.ids.zip pd.alloctx), [], ids, atx, ml
            rw [Hfst, Hsnd]
            simp only [List.map_nil, List.append_nil]
            iframe
            ipureintro
            refine ⟨by word, by word, rfl, fun x hx => by simp at hx, by simp⟩
          wp_for IH
          ihave %HQs := ownSlice_len _ _ _ $$ Hids
          ihave %HAs := ownSlice_len _ _ _ $$ Hatx
          simp only [List.length_map] at HQs HAs
          wp_if_destruct
          · have Hb : sint.nat j < Q.length := by
              have h0 := Hj.1; have h1 := HQs.1; word
            list_elem Q (sint.nat j) as x
            have Hxs : (Q.map Prod.snd)[sint.nat j]? = some x.2 := by simp [Hx_lookup]
            have Hxf : (Q.map Prod.fst)[sint.nat j]? = some x.1 := by simp [Hx_lookup]
            have Hxg : Q[sint.nat j] = x := (List.getElem?_eq_some_iff.1 Hx_lookup).2
            rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
            wp_apply wp_load_slice_index _ (sint.Z j) _ _ x.2 Hj.1 $$ [Hatx] with Hatx
            · iframe; ipureintro; exact Hxs
            try wp_auto
            wp_if_destruct
            · have hout : inRR b e x = false := by unfold inRR; exact decide_eq_false (by word)
              try wp_auto
              wp_for_post
              iframe
              iexists j + W64 1, Q, R, ids', atx', ml'
              iframe
              ipureintro
              have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
              rw [hj1]
              refine ⟨by word, by word, ?_, Hj.2.2.2.1, Hj.2.2.2.2⟩
              rw [← Hj.2.2.1, srLoop_skip Hb (by rw [Hxg]; exact hout)]
            · have hxb : ¬ x.2.toNat < b.toNat := by word
              wp_if_destruct
              · have hout : inRR b e x = false := by unfold inRR; exact decide_eq_false (by word)
                try wp_auto
                wp_for_post
                iframe
                iexists j + W64 1, Q, R, ids', atx', ml'
                iframe
                ipureintro
                have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
                rw [hj1]
                refine ⟨by word, by word, ?_, Hj.2.2.2.1, Hj.2.2.2.2⟩
                rw [← Hj.2.2.1, srLoop_skip Hb (by rw [Hxg]; exact hout)]
              · have hin : inRR b e x = true := by
                  unfold inRR; exact decide_eq_true ⟨by omega, by word⟩
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
                have hli : sint.Z (ids'.len - W64 1) = ((Q.length - 1 : Nat) : Int) := by word
                have hla : sint.Z (atx'.len - W64 1) = ((Q.length - 1 : Nat) : Int) := by word
                rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
                wp_apply wp_load_slice_index _ (sint.Z (ids'.len - W64 1)) _ _ y.1 (by word)
                  $$ [Hids] with Hids
                · iframe; ipureintro; rw [hli]; simp [Hy_lookup]
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
                wp_apply wp_store_slice_index _ (sint.Z j) _ y.1 $$ [Hids] as Hids
                · iframe; ipureintro; exact ⟨Hj.1, by simp only [List.length_map]; word⟩
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
                icases (ownSlice_split_all (ids'.len - W64 1) _ _ _ ⟨by word, by word⟩).1 $$ Hids
                  with ⟨Hids, Hids2⟩
                ihave Hids_cap := ownSlice_slice_absorb_capacity _ _ (W64 0) (ids'.len - W64 1)
                  ⟨by decide, by word, by word⟩ $$ [Hids2 Hids_cap]
                · iframe
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
                wp_apply wp_load_slice_index _ (sint.Z (atx'.len - W64 1)) _ _ y.2 (by word)
                  $$ [Hatx] with Hatx
                · iframe; ipureintro; rw [hla]; simp [Hy_lookup]
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
                wp_apply wp_store_slice_index _ (sint.Z j) _ y.2 $$ [Hatx] as Hatx
                · iframe; ipureintro; exact ⟨Hj.1, by simp only [List.length_map]; word⟩
                try wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
                icases (ownSlice_split_all (atx'.len - W64 1) _ _ _ ⟨by word, by word⟩).1 $$ Hatx
                  with ⟨Hatx, Hatx2⟩
                ihave Hatx_cap := ownSlice_slice_absorb_capacity _ _ (W64 0) (atx'.len - W64 1)
                  ⟨by decide, by word, by word⟩ $$ [Hatx2 Hatx_cap]
                · iframe
                try wp_auto
                wp_for_post
                have hQf : ((Q.map Prod.fst).set (sint.Z j).toNat y.1).take
                    (sint.nat (ids'.len - W64 1)) =
                    ((Q.set (sint.nat j) y).take (Q.length - 1)).map Prod.fst := by
                  rw [List.map_take, List.map_set,
                    show sint.nat (ids'.len - W64 1) = Q.length - 1 by word]
                have hQs : ((Q.map Prod.snd).set (sint.Z j).toNat y.2).take
                    (sint.nat (atx'.len - W64 1)) =
                    ((Q.set (sint.nat j) y).take (Q.length - 1)).map Prod.snd := by
                  rw [List.map_take, List.map_set,
                    show sint.nat (atx'.len - W64 1) = Q.length - 1 by word]
                rw [hQf, hQs]
                iframe
                iexists (j - W64 1 + W64 1), (Q.set (sint.nat j) y).take (Q.length - 1), R ++ [x],
                  slice.slice ids' w64 (W64 0) (ids'.len - W64 1),
                  slice.slice atx' w64 (W64 0) (atx'.len - W64 1), ml2
                iframe
                isplitl [Hm]
                · iExactEq Hm; simp
                ipureintro
                have hj' : sint.nat (j - W64 1 + W64 1) = sint.nat j := by word
                have hy := (List.getElem?_eq_some_iff.1 Hy_lookup).2
                have hsw := swap_take_perm Q (sint.nat j) Hb
                rw [hy, Hxg] at hsw
                rw [hj']
                refine ⟨by word, by simp only [List.length_take, List.length_set]; word, ?_, ?_, ?_⟩
                · rw [← Hj.2.2.1, srLoop_rm Hb (by rw [Hxg]; exact hin), hy]
                · intro z hz
                  rcases List.mem_append.1 hz with hz | hz
                  · exact Hj.2.2.2.1 z hz
                  · rw [List.mem_singleton] at hz; subst hz; exact hin
                · have : ((Q.set (sint.nat j) y).take (Q.length - 1) ++ (R ++ [x])).Perm
                      (((Q.set (sint.nat j) y).take (Q.length - 1) ++ [x]) ++ R) := by
                    rw [List.append_assoc]; exact List.Perm.append_left _ List.perm_append_comm
                  exact this.trans ((hsw.append_right R).trans Hj.2.2.2.2)
          · have Hjq : ¬ sint.nat j < Q.length := by
              intro h; have h0 := Hj.1; have h1 := HQs.1; apply Hif; word
            obtain ⟨-, -, HQK, Hin, Hperm⟩ := Hj
            rw [srLoop_end Hjq] at HQK
            have HKp := srLoop_perm b e _ 0 (pd.ids.zip pd.alloctx) (Nat.le_refl _) (by simp)
            rw [← HQK] at HKp
            have Hout : ∀ x ∈ Q, inRR b e x = false := fun x hx => by
              have := (List.mem_filter.1 (HKp.mem_iff.1 hx)).2; simpa using this
            obtain ⟨-, HRr⟩ := part_perm (p := inRR b e) Hout Hin Hperm
            have HLn : (L ++ R.map Prod.fst).Perm ((keys.take (i + 1)).flatMap fun t =>
                ((fl.pending !! t).map (rrRelGo b e t)).getD []) := by
              rw [Htake, List.flatMap_append]
              refine List.Perm.append HL.1 ?_
              simp only [List.flatMap_singleton, hpd, Option.map_some, Option.getD_some]
              unfold rrRelGo releaseRangeOneGo; rw [if_pos ht]
              exact HRr.map _
            have Hrest : ∀ (G' : GMap w64 Pending), (∀ k, k ≠ key → G' !! k = G !! k) →
                (∀ k ∈ keys.take i, G' !! k = (fl.pending !! k).bind (rrEntryGo b e k)) ∧
                (∀ k, k ∉ keys.take (i + 1) → G' !! k = fl.pending !! k) := by
              intro G' hG'
              refine ⟨fun k hk => ?_, fun k hk => ?_⟩
              · have hne : k ≠ key := fun h => Hnot (h ▸ hk)
                rw [hG' k hne]; exact HL.2.1 k hk
              · have hne : k ≠ key := fun h => hk (by rw [Htake, h]; simp)
                rw [hG' k hne]
                exact HL.2.2 k (fun h => hk (by rw [Htake]; exact List.mem_append_left _ h))
            have Hent : rrEntryGo b e key pd =
                if Q.map Prod.fst = [] then none
                else some ⟨Q.map Prod.fst, Q.map Prod.snd, b⟩ := by
              unfold rrEntryGo releaseRangeOneGo; rw [if_pos ht]; simp only [HQK]
            try wp_auto
            wp_if_destruct
            · have HQ0 : Q = [] := List.eq_nil_of_length_eq_zero (by word)
              subst HQ0
              try wp_auto
              wp_apply wp_mapDelete $$ [Hmap] as Hmap
              · iexact Hmap
              unfold forMapPostcondition
              iright; ileft
              isplitr
              · ipureintro; rfl
              iexists (GMap.delete key pp')
              iframe Hmap
              obtain ⟨Hr1, Hr2⟩ := Hrest (GMap.delete key G)
                (fun k hk => GMap.lookup_delete_ne _ (Ne.symm hk))
              isplitl
              · iexists _, _, _, (L ++ R.map Prod.fst), (GMap.delete key G)
                iframe
                ipureintro
                refine ⟨HLn, fun k hk => ?_, Hr2⟩
                rw [Htake, List.mem_append, List.mem_singleton] at hk
                rcases hk with hk | rfl
                · exact Hr1 k hk
                · rw [GMap.lookup_delete, hpd]; simp only [Option.bind_some, Hent]; simp
              · ipureintro; intro k hk; exact GMap.lookup_delete_ne _ (Ne.symm hk)
            · have HQne : Q ≠ [] := by
                intro h; subst h; simp only [List.length_nil] at HQs
                exact ‹¬ _› (by word)
              try wp_auto
              unfold forMapPostcondition
              iright; ileft
              isplitr
              · ipureintro; rfl
              iexists pp'
              iframe Hmap
              obtain ⟨Hr1, Hr2⟩ := Hrest (<[key := ⟨Q.map Prod.fst, Q.map Prod.snd, b⟩]> G)
                (fun k hk => GMap.lookup_insert_ne _ _ (Ne.symm hk))
              isplitl
              · iexists _, _, _, (L ++ R.map Prod.fst),
                  (<[key := ⟨Q.map Prod.fst, Q.map Prod.snd, b⟩]> G)
                iframe
                isplitl
                · rw [← GMap.insert_id pp' key v Hppk]
                  iapply (BigSepM2.bigSepM2_insert_delete).2
                  isplitl [Hidsf Hids Hids_cap Hatxf Hatx Hatx_cap Hlrb]
                  · iunfold ownPend
                    isplitr
                    · ipureintro; exact Hvnn
                    iunfold ownPending
                    iexists ids', atx'
                    iframe
                  rw [GMap.insert_id pp' key v Hppk]
                  iframe
                ipureintro
                refine ⟨HLn, fun k hk => ?_, Hr2⟩
                rw [Htake, List.mem_append, List.mem_singleton] at hk
                rcases hk with hk | rfl
                · exact Hr1 k hk
                · rw [GMap.lookup_insert, hpd]; simp only [Option.bind_some, Hent]
                  rw [if_neg (by simpa using HQne)]
              · ipureintro; intro k _; rfl
  iintro %pp' HP Hmap
  iNamed HP
  rw [List.take_length] at HL
  have hkσ : ∀ k, k ∈ keys ↔ (fl.pending !! k).isSome := fun k => (Hkset k).trans (Hdom k)
  have HG : ∀ k, G !! k = (fl.pending !! k).bind (rrEntryGo b e k) := by
    intro k
    by_cases hk : k ∈ keys
    · exact HL.2.1 k hk
    · have h1 := HL.2.2 k hk
      have h2 : fl.pending !! k = none := by
        cases h : fl.pending !! k
        · rfl
        · exact absurd ((hkσ k).2 (by simp [h])) hk
      rw [h1, h2]; rfl
  obtain ⟨Hnd, Hge, Hlen, Hfree, Hpend, Halloc, Hwf', Hc'⟩ :=
    releaseRangeGo_ok Hok.2 Hbe hkσ Hknodup HG HL.1
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  unfold FLImpl.iface
  try wp_auto
  wp_apply (hMS fl.free ml L Hok.2.2.2.1 Hnd
      (fun x hx => Hok.2.2.1 x (List.mem_append_left _ hx)) Hge Hlen) $$ [Hown Hm Hmcap] as Hown
  · iframe
  iapply HΦ
  rw [Hfree]
  iframe Hown
  iunfold ownSh
  iexists c
  isplitl
  · iunfold ownShC
    iexists al, ca, pe, pp'
    rw [Hpend, Halloc]
    iframe
  · ipureintro
    exact ⟨fun x => (Hok.1 x).trans (Hc' x).symm, Hwf'⟩

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
