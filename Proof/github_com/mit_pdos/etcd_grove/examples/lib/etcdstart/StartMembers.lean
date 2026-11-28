/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/StartMembers.lean` (the clusterN
Scope, 2026-11-15, its stage S4). Lean-first (no Rocq counterpart).

Two loops over the members. The first builds the initial cluster's map: after `j` members, its keys
are their names, each slice the member's one peer URL (`iuOf`; the names are distinct). The map is
read-only from then on. The second starts the members in order: after `j` members, the servers'
slice holds their servers (each with its `memberUp`, the thread token lent out) and zeros, and the
members still to start keep their `memberPre`; each iteration looks the member's peer URLs up in the
map and calls `NewMember` (at the given snapshot settings) and `Start` with the thread token, taken back out of the started member's
`memberUp` (`memberUp_tok`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMembers
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Start

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

theorem StartMembers.wp_proof (wp_NewMember : NewMember.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG)) :
    StartMembers.spec (GF := GF) (hG := hG) := by
  intro N token snapCount catchUp msl lg xs ps bootLog ctxs dir Φs γn lm cmp Htb Hrb48 HrbN HwbN Hbl Hγnd Hdok Hbc
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
    have hutf : ∀ n, (M.lookup n).isSome → utf8Valid n := by
      intro n hn
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ((Hdom n).1 hn)
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
      exact Hutf x hx
    -- the second loop: the members started in order
    ihave HJ : (∃ (j : w64) (mv : GMember) (jv : w64) (ss : List Loc),
        "i" ∷ i_ptr ↦ j ∗ "m" ∷ m_ptr ↦ mv ∗ "j" ∷ j_ptr ↦ jv ∗
        "Hssl" ∷ ssl ↦* (ss ++ List.replicate (sint.nat msl.len - ss.length) (zero_val Loc)) ∗
        "Hups" ∷ ([∗list] s; x ∈ ss; xs.take (sint.nat j),
          (threadTok -∗ memberUp s x.2.ρ x.2.E lg γn x.2.id lm)) ∗
        "Hpre" ∷ ([∗list] x ∈ xs.drop (sint.nat j),
          memberPre N token (xs.map (·.1)) ps bootLog ctxs dir Φs γn lm x cmp) ∗
        "Htok" ∷ threadTok ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z msl.len ∧ ss.length = sint.nat j⌝ : IProp GF)
        $$ [i m j Hssl Hpre Htok]
    · iexists W64 0, _, _, []
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iframe
      try (isplitr; (iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro))
      ipureintro; refine ⟨by word, by word, rfl⟩
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
      obtain ⟨h1, h2, h3, h4, h5⟩ := Hx xj hxj
      -- `NewMember(m.Name, cluster[m.Name], m.Peer, m.Client, cluster, token, snapCount, catchUp,
      -- lg)`
      wp_apply (wp_NewMember N xj.1.Name' xj.1.Peer' xj.1.Client' token snapCount catchUp sl pm lg M
          (iuOf (xs.map (·.1))) (urlsN (xs.map (·.1)) xj.1) ps bootLog ctxs dir xj.2.id xj.2.γ
          xj.2.ρ xj.2.E Φs γn cmp lm Htb Hrb48 HrbN HwbN h1 h2 h3 Hbl h4 Hγnd Hdok h5 Hbc
          ⟨rfl, rfl, Hdom, rfl⟩ (HaF xj hxj).1 (HaF xj hxj).2 hutf (HnL xj hxj) Haf Hbuq Hdbo) $$ [Htok Hmb Hfr] as %s %err Hr
      · iframe; iframe #
      icases Hr with (⟨%Herr, Htok⟩ | ⟨%Herr, Htok, Hmb⟩)
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
      -- `s.Start()`
      wp_apply (wp_Start_built wp_Start s xj.2.ρ xj.2.E lg γn xj.2.id N _ HrbN lm Hrb48)
        $$ [Hmb Htok] as Hup
      · iframe
      (try wp_auto)
      icases memberUp_tok _ _ _ _ _ _ _ $$ Hup with ⟨Htok, Hup⟩
      ihave %Hsll := ownSlice_len $$ Hssl
      have hssn : ss.length < sint.nat msl.len := by rw [Hj.2.2]; word
      have hlen' : (ss ++ List.replicate (sint.nat msl.len - ss.length) (zero_val Loc)).length =
          sint.nat msl.len := by simp; omega
      rw [hlen'] at Hsll
      have Hb2 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ssl.len := by
        obtain ⟨h1, h2⟩ := Hsll; constructor <;> word
      simp only [Hb2, _root_.and_self, ↓reduceIte]
      wp_apply (wp_store_slice_index ssl (sint.Z j) _ s) $$ [Hssl] as Hssl
      · iframe Hssl; ipureintro; rw [hlen']; constructor <;> word
      ihave Hups := (BigSepL2.bigSepL2_snoc (Φ := fun _ (s : Loc) (x : GMember × MemberG GF) =>
        iprop(threadTok -∗ memberUp s x.2.ρ x.2.E lg γn x.2.id lm))).2 $$ [Hups Hup]
      · iframe
      wp_for_post
      iframe
      iexists j + W64 1, xj.1, j, ss ++ [s]
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have hjz : (sint.Z j).toNat = ss.length := by rw [Hj.2.2]
      rw [hjz, set_replicate_snoc _ _ _ _ hssn, hj1, List.take_succ, Hxj_lookup]
      have hl1 : (ss ++ [s]).length = ss.length + 1 := by simp
      simp only [Option.toList_some, hl1]
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
      iexists ss
      rw [Hj.2.2, hjn, ← hmsl, List.length_map, Nat.sub_self, List.replicate_zero,
        List.append_nil, List.take_of_length_le (Nat.le_refl _)]
      iframe

end proof

end etcdstart
end EtcdGrove
end Perennial
