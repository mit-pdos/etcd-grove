/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restartN/startMembers.lean`
(`notes/restartN-plan.md`). Lean-first (no Rocq counterpart). `etcdstart.StartMembers.wp_proof`'s two
loops: the first builds the initial cluster's map; the second starts the members in order, each with
`build` (its fresh bundle without its peer address) and `newMember` (the peer address's listen right and
protocol, out of the fresh bundle, `memberFreshRes_peer`), the thread token taken back out of the started
member's `memberUp` (`memberUp_tok`); after `j` members, the two slices hold their servers and records,
and zeros.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.startMembers
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.build
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open etcd_restart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

set_option maxHeartbeats 1000000 in
theorem startMembers.wp_proof (wp_build : build.spec (GF := GF) (hG := hG))
    (wp_newMember : newMember.spec (GF := GF) (hG := hG)) :
    startMembers.spec (GF := GF) (hG := hG) := by
  intro N msl lg xs ps bootLog ctxs dir Φs γn ThB RcB RcN HwbN Hbl Hγnd Hdok Hbc
    Hnd Hutf HnL HaF Hx Haf Hbuq Hdbo
  wp_start as ⟨#Hlg, Htok, #Hms, #Hcc, Hpre⟩
  ihave %Hmsl := ownSlice_len $$ Hms
  (try wp_auto)
  wp_apply wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.client.pkg.v3.types.URLs) as %pm Hpm
  (try wp_auto)
  -- the first loop: the initial cluster's map
  ihave HI : (∃ (j : w64) (mv : GMember) (M : GMap GoString GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "m" ∷ m_ptr ↦ mv ∗ "Hpm" ∷ pm ↦$ M ∗
      "#Hsls" ∷ □ ([∗map] k ↦ sl ∈ M, sl ↦*□ iuOf (xs.map (·.1)) k) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z msl.len ∧
        ∀ n, (M.lookup n).isSome ↔ n ∈ ((xs.map (·.1)).take (sint.nat j)).map (·.Name')⌝ : IProp GF)
      $$ [i m Hpm]
  · iexists W64 0, _, ∅
    iframe
    isplitl
    · iintro !>
      iapply BigSepM.bigSepM_empty.2; itrivial
    ipureintro
    refine ⟨by word, by word, fun n => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp
  wp_for HI
  split
  · rename_i Hif
    have Hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z msl.len := ⟨Hj.1, of_decide_eq_true Hif⟩
    (try wp_auto)
    simp only [Hb, _root_.and_self, ↓reduceIte]
    list_elem (xs.map (·.1)) (sint.nat j) as mj
    -- the member is not in the map yet (the names are distinct)
    have hmem : mj ∈ xs.map (·.1) := List.mem_of_getElem? Hmj_lookup
    have hnew : (M.lookup mj.Name').isSome = false := by
      rw [Bool.eq_false_iff]; intro h
      have h' := (Hj.2.2 _).1 h
      exact name_not_mem_take _ (by rw [List.map_map]; exact Hnd) _ _ Hmj_lookup h'
    wp_apply wp_load_slice_index _ (sint.Z j) (xs.map (·.1)) _ mj Hj.1 $$ [] as -
    · iframe #; ipureintro; exact Hmj_lookup
    (try wp_auto)
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %peer ⟨Hpeer, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    imod ownSlice_persist _ _ _ $$ Hpeer with #Hpeer
    (try wp_auto)
    wp_apply wp_mapInsert $$ Hpm as Hpm
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, mj, _
    iframe
    isplitl
    · iintro !>
      iapply (BigSepM.bigSepM_insert (by
        rw [gmap_get?_eq]; cases hl : M.lookup mj.Name' <;> simp_all)).2
      isplitr
      · iExactEq Hpeer
        rw [iuOf_mem _ (by rw [List.map_map]; exact Hnd) mj hmem]
        rfl
      iexact Hsls
    ipureintro
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    refine ⟨by word, by word, fun n => ?_⟩
    rw [hj1, take_succ_names _ _ _ Hmj_lookup, GMap.lookup_insert_is_Some, ← Hj.2.2 n]
    constructor
    · rintro (rfl | ⟨-, h⟩)
      · exact Or.inr rfl
      · exact Or.inl h
    · rintro (h | rfl)
      · by_cases he : mj.Name' = n
        · exact Or.inl he
        · exact Or.inr ⟨he, h⟩
      · exact Or.inl rfl
  · rename_i Hif
    have Hif' : ¬ sint.Z j < sint.Z msl.len := fun h => Hif (decide_eq_true h)
    have hmsl : (xs.map (·.1)).length = sint.nat msl.len := Hmsl.1
    have Hdom : ∀ n, (M.lookup n).isSome ↔ n ∈ (xs.map (·.1)).map (·.Name') := by
      intro n
      rw [Hj.2.2 n, List.take_of_length_le (by rw [hmsl]; word)]
    (try wp_auto)
    imod ownMap_persist _ _ _ $$ Hpm with #Hpm
    wp_apply (wp_slice_make2 (V := Loc) msl.len) as %ssl ⟨Hssl, -⟩
    · ipureintro; word
    (try wp_auto)
    wp_apply (wp_slice_make2 (V := Loc) msl.len) as %msl2 ⟨Hmsl2, -⟩
    · ipureintro; word
    (try wp_auto)
    have hutf : ∀ n, (M.lookup n).isSome → utf8Valid n := by
      intro n hn
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ((Hdom n).1 hn)
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
      exact Hutf x hx
    -- the second loop: the members started in order
    ihave HJ : (∃ (j : w64) (mv : GMember) (jv : w64) (zs : List (Loc × Loc)),
        "i" ∷ i_ptr ↦ j ∗ "m" ∷ m_ptr ↦ mv ∗ "j" ∷ j_ptr ↦ jv ∗
        "Hssl" ∷ ssl ↦* (zs.map (·.1) ++ List.replicate (sint.nat msl.len - zs.length) (zero_val Loc)) ∗
        "Hmsl2" ∷ msl2 ↦* (zs.map (·.2) ++ List.replicate (sint.nat msl.len - zs.length) (zero_val Loc)) ∗
        "Hups" ∷ ([∗list] z; x ∈ zs; xs.take (sint.nat j), memberStarted lg γn z x) ∗
        "Hpre" ∷ ([∗list] x ∈ xs.drop (sint.nat j),
          memberPre N token (xs.map (·.1)) ps bootLog ctxs dir Φs γn .none x) ∗
        "Htok" ∷ threadTok ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z msl.len ∧ zs.length = sint.nat j⌝ : IProp GF)
        $$ [i m j Hssl Hmsl2 Hpre Htok]
    · iexists W64 0, _, _, []
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, List.nil_append,
        List.length_nil, Nat.sub_zero]
      iframe
      try (isplitr; (iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro))
      ipureintro; refine ⟨by word, by word, by first | rfl | trivial⟩
    wp_for HJ
    split
    · rename_i Hif
      have Hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z msl.len := ⟨Hj.1, of_decide_eq_true Hif⟩
      (try wp_auto)
      simp only [Hb, _root_.and_self, ↓reduceIte]
      list_elem xs (sint.nat j) as xj
      have Hmj : (xs.map (·.1))[sint.nat j]? = some xj.1 := by simp [Hxj_lookup]
      have hxj : xj ∈ xs := List.mem_of_getElem? Hxj_lookup
      wp_apply wp_load_slice_index _ (sint.Z j) (xs.map (·.1)) _ xj.1 Hj.1 $$ [] as -
      · iframe #; ipureintro; exact Hmj
      (try wp_auto)
      -- the member's peer URLs, out of the map
      obtain ⟨sl, hsl⟩ : ∃ sl, M.lookup xj.1.Name' = some sl := Option.isSome_iff_exists.1
        ((Hdom _).2 (List.mem_map_of_mem (List.mem_map_of_mem hxj)))
      have hsl' : (M !! xj.1.Name') = some sl := hsl
      ihave #Hpeer := (BigSepM.bigSepM_lookup (Φ := fun k sl => iprop(sl ↦*□ iuOf (xs.map (·.1)) k))
        hsl') $$ Hsls
      rw [iuOf_mem _ (by rw [List.map_map]; exact Hnd) _ (List.mem_map_of_mem hxj)] at *
      wp_apply (wp_map_lookup1 go.string go_etcd_io.etcd.client.pkg.v3.types.URLs.ty pm M xj.1.Name'
        DFrac.discard) $$ Hpm as -
      simp only [hsl', Option.getD_some]
      (try wp_auto)
      -- the member's resources
      isimp only [drop_cons_of_getElem? xs _ xj Hxj_lookup] at Hpre
      ihave Hpre := BigSepL.bigSepL_cons.1 $$ Hpre
      icases Hpre with ⟨Hx1, Hpre⟩
      iunfold memberPre at Hx1
      icases Hx1 with ⟨#Hbp, Hmb, #Hnet, Hfr⟩
      icases memberFreshRes_peer _ _ _ _ rfl $$ Hfr with ⟨⟨Ha, Ho⟩, Hfr⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := Hx xj hxj
      have hown : (netRh γn).owner xj.1.Peer' = xj.2.id := by
        rw [netRh_owner]
        exact netOwner_of_mem γn.dir (by rw [Hγnd]; exact Hdok.2.1) _ _ (by rw [Hγnd]; exact h5)
      -- `build(m.Name, cluster[m.Name], m.Client, cluster, lg)`
      wp_apply (wp_build N xj.1.Name' xj.1.Peer' xj.1.Client' sl pm lg M
          (iuOf (xs.map (·.1))) (urlsN (xs.map (·.1)) xj.1) ps bootLog ctxs dir xj.2.id xj.2.γ
          xj.2.ρ xj.2.E Φs γn HwbN h1 h2 h3 Hbl h4 Hγnd Hdok h5 Hbc
          ⟨rfl, rfl, Hdom, rfl⟩ (HaF xj hxj).1 (HaF xj hxj).2 hutf (HnL xj hxj) Haf Hbuq Hdbo) $$ [Htok Hmb Hfr] as %s %err Hr
      · iframe; iframe #
      icases Hr with (⟨%Herr, Htok⟩ | ⟨%Herr, Htok, Hmb, #Hdd⟩)
      · cases err with
        | nil => exact absurd rfl Herr
        | ok ei => ?_
        (try wp_auto)
        wp_for_post
        iapply HΦ
        iframe
        ileft; ipureintro; exact Herr
      subst Herr
      (try wp_auto)
      -- `newMember(s, m.Name, cluster[m.Name], m.Peer, m.Client)`
      wp_apply (wp_map_lookup1 go.string go_etcd_io.etcd.client.pkg.v3.types.URLs.ty pm M xj.1.Name'
        DFrac.discard) $$ Hpm as -
      simp only [hsl', Option.getD_some]
      (try wp_auto)
      wp_apply (wp_newMember N s xj.1.Name' xj.1.Peer' xj.1.Client' sl xj.2.ρ xj.2.E lg γn xj.2.id
          hown) $$ [Htok Hmb Ha Ho] as %mm %err Hr
      · iframe; iframe #
      icases Hr with (⟨%Herr, Htok⟩ | ⟨%Herr, %γS, Hup, Hrec⟩)
      · cases err with
        | nil => exact absurd rfl Herr
        | ok ei => ?_
        (try wp_auto)
        wp_for_post
        iapply HΦ
        iframe
        ileft; ipureintro; exact Herr
      subst Herr
      (try wp_auto)
      icases memberUp_tok _ _ _ _ _ _ _ $$ Hup with ⟨Htok, Hup⟩
      ihave %Hsll := ownSlice_len $$ Hssl
      ihave %Hmll := ownSlice_len $$ Hmsl2
      have hssn : zs.length < sint.nat msl.len := by rw [Hj.2.2]; word
      have hlen' : (zs.map (·.1) ++ List.replicate (sint.nat msl.len - zs.length) (zero_val Loc)).length =
          sint.nat msl.len := by simp; omega
      have hlen2 : (zs.map (·.2) ++ List.replicate (sint.nat msl.len - zs.length) (zero_val Loc)).length =
          sint.nat msl.len := by simp; omega
      rw [hlen'] at Hsll
      rw [hlen2] at Hmll
      have Hb2 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ssl.len := by
        obtain ⟨h1, h2⟩ := Hsll; constructor <;> word
      have Hb3 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z msl2.len := by
        obtain ⟨h1, h2⟩ := Hmll; constructor <;> word
      simp only [Hb2, _root_.and_self, ↓reduceIte]
      wp_apply (wp_store_slice_index ssl (sint.Z j) _ s) $$ [Hssl] as Hssl
      · iframe Hssl; ipureintro; rw [hlen']; constructor <;> word
      (try wp_auto)
      simp only [Hb3, _root_.and_self, ↓reduceIte]
      wp_apply (wp_store_slice_index msl2 (sint.Z j) _ mm) $$ [Hmsl2] as Hmsl2
      · iframe Hmsl2; ipureintro; rw [hlen2]; constructor <;> word
      ihave Hups := (BigSepL2.bigSepL2_snoc (Φ := fun _ (z : Loc × Loc) (x : GMember × MemberG GF) =>
        memberStarted lg γn z x) (x := (s, mm)) (y := xj)).2 $$ [Hups Hup Hrec]
      · iframe Hups
        iunfold memberStarted
        isplitl [Hup]
        · iexact Hup
        isplitl [Hrec]
        · iexists γS; iexact Hrec
        iexact Hdd
      wp_for_post
      iframe
      iexists j + W64 1, xj.1, j, zs ++ [(s, mm)]
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have hjz : (sint.Z j).toNat = zs.length := by rw [Hj.2.2]
      have e1 : (zs.map (·.1) ++ List.replicate (sint.nat msl.len - zs.length) (zero_val Loc)).set
          (sint.Z j).toNat s = (zs ++ [(s, mm)]).map (·.1) ++
            List.replicate (sint.nat msl.len - (zs ++ [(s, mm)]).length) (zero_val Loc) := by
        have := set_replicate_snoc (zs.map (·.1)) (sint.nat msl.len) (zero_val Loc) s (by simpa using hssn)
        simp only [List.length_map] at this
        rw [hjz, this]; simp
      have e2 : (zs.map (·.2) ++ List.replicate (sint.nat msl.len - zs.length) (zero_val Loc)).set
          (sint.Z j).toNat mm = (zs ++ [(s, mm)]).map (·.2) ++
            List.replicate (sint.nat msl.len - (zs ++ [(s, mm)]).length) (zero_val Loc) := by
        have := set_replicate_snoc (zs.map (·.2)) (sint.nat msl.len) (zero_val Loc) mm (by simpa using hssn)
        simp only [List.length_map] at this
        rw [hjz, this]; simp
      rw [e1, e2, hj1, List.take_add_one, Hxj_lookup]
      simp only [Option.toList_some]
      iframe
      ipureintro
      refine ⟨by word, by word, by simp [Hj.2.2]⟩
    · rename_i Hif
      have Hif' : ¬ sint.Z j < sint.Z msl.len := fun h => Hif (decide_eq_true h)
      have hjn : sint.nat j = xs.length := by rw [← List.length_map (f := (·.1)), hmsl]; word
      (try wp_auto)
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; rfl
      iexists zs, M
      rw [Hj.2.2, hjn, ← hmsl, List.length_map, Nat.sub_self, List.replicate_zero,
        List.append_nil, List.append_nil, List.take_of_length_le (Nat.le_refl _)]
      iframe
      iframe #
      ipureintro
      intro n; rw [Hdom n, List.map_map]; rfl

end proof

end etcd_restartN
end EtcdGrove
end Perennial
