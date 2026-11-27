/-
**`permSlice` is a sorter** (the auth plan's S4d, 2026-10-24; nomode X-a1, 2026-11-27). Lean-first
(no Rocq counterpart). `RoleGrantPermission` sorts a role's permissions:
`sort.Sort(permSlice(role.KeyPermission))`, `permSlice.Less` comparing the keys with
`bytes.Compare`, then, on equal keys, the range ends (the fork's `goose-lean-permsort`). Over the
pairs (message, wire permission) the slice holds (`permsOwn`: the slice of the messages, each
message read-only with its wire permission, `ownPermS`), the three methods meet Perennial's
`isSorter` for that order (`permWLt`, `GrantPermLemmas.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.GrantPermLemmas
public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.bytes.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- The slice `s` of permission messages, as the pairs `l`: the slice of the messages, and each
message read-only, holding its wire permission. -/
def auth.permsOwn (s : GoSlice) (l : List (Loc × PermW)) : IProp GF :=
  iprop(s ↦* l.map Prod.fst ∗ □ (∀ x : Loc × PermW, ⌜x ∈ l⌝ → ownPermS x.1 x.2))

/-- **`permSlice(s)` is a sorter** of `permsOwn s` by (key, range end) (`permWLt`). -/
theorem auth.permSlice_isSorter (s : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ⊢
      sort.isSorter (interface.mk permSlice.ty #s) (auth.permsOwn s) permWLt := by
  iintro #Hpkg
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  unfold sort.isSorter
  isplitr
  · iintro !> %l %Φ !> Hown HΦ
    iunfold auth.permsOwn at Hown
    icases Hown with ⟨Hs, #Hm⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    rw [method_unfold (t := permSlice.ty)]
    wp_auto
    have hlen : s.len = W64 l.length := by
      simp only [List.length_map] at Hl; word
    rw [hlen]
    iapply HΦ
    iunfold auth.permsOwn
    iframe Hs Hm
  isplitr
  · iintro !> %l %i %j %a %b %Hij %Φ !> Hown HΦ
    iunfold auth.permsOwn at Hown
    icases Hown with ⟨Hs, #Hm⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    obtain ⟨Hi0, Hj0, Ha, Hb⟩ := Hij
    have hia : (l.map Prod.fst)[(sint.Z i).toNat]? = some a.1 := by
      rw [List.getElem?_map]; rw [show (sint.Z i).toNat = sint.nat i by rfl, Ha]; rfl
    have hjb : (l.map Prod.fst)[(sint.Z j).toNat]? = some b.1 := by
      rw [List.getElem?_map]; rw [show (sint.Z j).toNat = sint.nat j by rfl, Hb]; rfl
    have hib : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := by
      refine ⟨Hi0, ?_⟩
      have := (List.getElem?_eq_some_iff.mp hia).1; simp only [List.length_map] at this Hl; word
    have hjb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := by
      refine ⟨Hj0, ?_⟩
      have := (List.getElem?_eq_some_iff.mp hjb).1; simp only [List.length_map] at this Hl; word
    ihave #Ha := Hm $$ %a
    ihave #Hb := Hm $$ %b
    ihave #Ha' := Ha $$ [] ; · ipureintro; exact List.mem_of_getElem? Ha
    ihave #Hb' := Hb $$ [] ; · ipureintro; exact List.mem_of_getElem? Hb
    iclear Ha Hb
    iunfold ownPermS at Ha' Hb'
    icases Ha' with ⟨%Hann, %ak, %are, -, #HaKey, #HaRe, -, -, #Hak, #Hare⟩
    icases Hb' with ⟨%Hbnn, %bk, %bre, -, #HbKey, #HbRe, -, -, #Hbk, #Hbre⟩
    rw [method_unfold (t := permSlice.ty)]
    wp_auto
    simp only [hib, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z i) (l.map Prod.fst) (DFrac.own 1) a.1 Hi0 $$ [$Hs] as Hs
    · ipureintro; exact hia
    (try wp_auto)
    simp only [hjb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z j) (l.map Prod.fst) (DFrac.own 1) b.1 Hj0 $$ [$Hs] as Hs
    · ipureintro; exact hjb
    (try wp_auto)
    wp_apply (_root_.Perennial.bytes.wp_Compare ak bk DFrac.discard DFrac.discard a.2.key b.2.key)
      $$ [$Hak $Hbk] as ⟨-, -⟩
    (try wp_auto)
    by_cases hk : a.2.key = b.2.key
    · have h0 : bytes.compareResult a.2.key b.2.key = W64 0 := by
        unfold bytes.compareResult; rw [hk, if_neg (go.goStringLt_irrefl _), if_pos rfl]
      simp only [h0]
      (try wp_auto)
      (try simp only [hib, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index s (sint.Z i) (l.map Prod.fst) (DFrac.own 1) a.1 Hi0 $$ [$Hs] as Hs
      · ipureintro; exact hia
      (try wp_auto)
      (try simp only [hjb', _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index s (sint.Z j) (l.map Prod.fst) (DFrac.own 1) b.1 Hj0 $$ [$Hs] as Hs
      · ipureintro; exact hjb
      (try wp_auto)
      wp_apply (_root_.Perennial.bytes.wp_Compare are bre DFrac.discard DFrac.discard a.2.rangeEnd
        b.2.rangeEnd) $$ [$Hare $Hbre] as ⟨-, -⟩
      (try wp_auto)
      iapply HΦ
      iunfold auth.permsOwn
      iframe Hs Hm
      ipureintro
      unfold permWLt rangeLt bytes.compareResult
      have hnk : ¬ go.GoStringLt a.2.key b.2.key := by rw [hk]; exact go.goStringLt_irrefl _
      by_cases h1 : go.GoStringLt a.2.rangeEnd b.2.rangeEnd
      · rw [if_pos h1]
        exact ⟨fun _ => Or.inr ⟨hk, h1⟩, fun _ => by decide⟩
      · rw [if_neg h1]
        constructor
        · intro h
          exfalso
          by_cases h2 : a.2.rangeEnd = b.2.rangeEnd
          · rw [if_pos h2] at h; exact absurd h (by decide)
          · rw [if_neg h2] at h; exact absurd h (by decide)
        · rintro (h | ⟨-, h⟩)
          · exact absurd h hnk
          · exact absurd h h1
    · have h0 : bytes.compareResult a.2.key b.2.key ≠ W64 0 := by
        unfold bytes.compareResult
        by_cases h1 : go.GoStringLt a.2.key b.2.key
        · rw [if_pos h1]; decide
        · rw [if_neg h1, if_neg hk]; decide
      simp only [h0, not_false_eq_true, _root_.decide_true, decide_false, Bool.not_false,
        Bool.not_true, ↓reduceIte]
      (try wp_auto)
      iapply HΦ
      iunfold auth.permsOwn
      iframe Hs Hm
      ipureintro
      unfold permWLt rangeLt bytes.compareResult
      by_cases h1 : go.GoStringLt a.2.key b.2.key
      · rw [if_pos h1]
        exact ⟨fun _ => Or.inl h1, fun _ => by decide⟩
      · rw [if_neg h1, if_neg hk]
        constructor
        · intro h; exact absurd h (by decide)
        · rintro (h | ⟨h, -⟩)
          · exact absurd h h1
          · exact absurd h hk
  · iintro !> %l %i %j %a %b %Hij %Φ !> Hown HΦ
    iunfold auth.permsOwn at Hown
    icases Hown with ⟨Hs, #Hm⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    obtain ⟨Hi0, Hj0, Ha, Hb⟩ := Hij
    have hia : (l.map Prod.fst)[(sint.Z i).toNat]? = some a.1 := by
      rw [List.getElem?_map]; rw [show (sint.Z i).toNat = sint.nat i by rfl, Ha]; rfl
    have hjb : (l.map Prod.fst)[(sint.Z j).toNat]? = some b.1 := by
      rw [List.getElem?_map]; rw [show (sint.Z j).toNat = sint.nat j by rfl, Hb]; rfl
    have hib : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := by
      refine ⟨Hi0, ?_⟩
      have := (List.getElem?_eq_some_iff.mp hia).1; simp only [List.length_map] at this Hl; word
    have hjb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := by
      refine ⟨Hj0, ?_⟩
      have := (List.getElem?_eq_some_iff.mp hjb).1; simp only [List.length_map] at this Hl; word
    rw [method_unfold (t := permSlice.ty)]
    wp_auto
    (try simp only [hib, hjb', _root_.and_self, ↓reduceIte])
    (try wp_auto)
    (try simp only [hib, hjb', _root_.and_self, ↓reduceIte])
    (try wp_auto)
    (try simp only [hib, hjb', _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index s (sint.Z j) (l.map Prod.fst) (DFrac.own 1) b.1 Hj0 $$ [$Hs] as Hs
    · ipureintro; exact hjb
    (try wp_auto)
    (try simp only [hib, hjb', _root_.and_self, ↓reduceIte])
    (try wp_auto)
    (try simp only [hib, hjb', _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index s (sint.Z i) (l.map Prod.fst) (DFrac.own 1) a.1 Hi0 $$ [$Hs] as Hs
    · ipureintro; exact hia
    (try wp_auto)
    wp_apply wp_store_slice_index s (sint.Z i) (l.map Prod.fst) b.1 $$ [$Hs] as Hs
    · ipureintro; simp only [List.length_map] at Hl ⊢; word
    (try wp_auto)
    wp_apply wp_store_slice_index s (sint.Z j) ((l.map Prod.fst).set (sint.Z i).toNat b.1) a.1
      $$ [$Hs] as Hs
    · ipureintro; simp only [List.length_set, List.length_map] at Hl ⊢; word
    (try wp_auto)
    iapply HΦ
    iunfold auth.permsOwn
    isplitl [Hs]
    · iExactEq Hs
      simp only [List.map_set]
    iintro !> %x %Hx
    iapply Hm
    ipureintro
    rcases List.mem_or_eq_of_mem_set Hx with h | h
    · rcases List.mem_or_eq_of_mem_set h with h' | h'
      · exact h'
      · subst h'; exact List.mem_of_getElem? Hb
    · subst h; exact List.mem_of_getElem? Ha

end proof

end EtcdGrove
end Perennial
