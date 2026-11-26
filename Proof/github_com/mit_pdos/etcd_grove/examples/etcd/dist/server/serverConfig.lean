/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/server/serverConfig.lean`. Lean-first (no Rocq
counterpart); etcd-dist N5 (`notes/etcd-dist-plan.md` §19). The initial cluster's map is built by the range over
`c.Cluster` (read-only), with the whole context as the loop's invariant (`wp_for`): after `j` iterations its keys
are the names of the first `j` entries, each slice (persisted) the one peer URL of its entry, which is `iuP`'s since
the names are distinct (`iuP_at`, `name_fresh`); then `mode`, the two URL slice literals, the feature gate, the
`ServerConfig` literal and the `if c.Auth` field stores, whose value is `memberCfg`'s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.serverConfig
public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

/-! ## The initial cluster's names: pure facts -/

section pure
variable [GooseExts]

/-- With distinct names, an entry's name maps to its own peer URL. -/
theorem iuP_at : ∀ (pl : List server.Peer) (j : Nat) (x : server.Peer),
    (pl.map (·.Name')).Nodup → pl[j]? = some x → iuP pl x.Name' = [httpURL x.Addr']
  | [], _, _, _, hx => by simp at hx
  | p :: ps, 0, x, _, hx => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    simp [iuP]
  | p :: ps, j + 1, x, hnd, hx => by
    simp only [List.getElem?_cons_succ] at hx
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hne : p.Name' ≠ x.Name' := by
      intro he; apply hnd.1; rw [he]; exact List.mem_map_of_mem (List.mem_of_getElem? hx)
    have ih := iuP_at ps j x hnd.2 hx
    unfold iuP at ih ⊢
    rw [List.find?_cons]
    simp only [hne, decide_false]
    exact ih

/-- With distinct names, entry `j`'s name is none of the names before it. -/
theorem name_fresh : ∀ (pl : List server.Peer) (j : Nat) (x : server.Peer),
    (pl.map (·.Name')).Nodup → pl[j]? = some x → x.Name' ∉ (pl.take j).map (·.Name')
  | [], _, _, _, hx => by simp at hx
  | p :: ps, 0, x, _, _ => by simp
  | p :: ps, j + 1, x, hnd, hx => by
    simp only [List.getElem?_cons_succ] at hx
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hne : p.Name' ≠ x.Name' := by
      intro he; apply hnd.1; rw [he]; exact List.mem_map_of_mem (List.mem_of_getElem? hx)
    have ih := name_fresh ps j x hnd.2 hx
    simp only [List.take_succ_cons, List.map_cons, List.mem_cons, not_or]
    exact ⟨Ne.symm hne, ih⟩

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]

theorem serverConfig.wp_proof
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG)) :
    serverConfig.spec (GF := GF) (hG := hG) := by
  intro cv pl lg Hnd
  wp_start as #Hcl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hcl
  ihave #Pfeat : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features $$ []
  · iPkgInit
  (try wp_auto)
  -- the initial cluster's map
  wp_apply wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.client.pkg.v3.types.URLs) as %pm Hpm
  (try wp_auto)
  ihave HI : (∃ (j : Nat) (pv : server.Peer) (M : GMap GoString GoSlice),
      "i" ∷ i_ptr ↦ W64 j ∗ "p" ∷ p_ptr ↦ pv ∗ "Hpm" ∷ pm ↦$ M ∗
      "#Hsls" ∷ □ ([∗map] n ↦ sl ∈ M, sl ↦*□ iuP pl n) ∗
      "%Hk" ∷ ⌜j ≤ pl.length ∧ ∀ n, (M.lookup n).isSome ↔ n ∈ (pl.take j).map (·.Name')⌝ : IProp GF)
      $$ [i p Hpm]
  · iexists 0, _, ∅
    iframe
    isplitl
    · iintro !>
      iapply BigSepM.bigSepM_empty.2; itrivial
    ipureintro
    refine ⟨by omega, fun n => ?_⟩
    simp
  wp_for HI
  by_cases hj : j < pl.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z cv.Cluster'.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    (try wp_auto)
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, _root_.and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, pl[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index cv.Cluster' (sint.Z (W64 (j : Int))) pl DFrac.discard x h0) $$ [] as -
    · iframe #; ipureintro; rw [hsj]; exact hx
    (try wp_auto)
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %usl ⟨Husl, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    imod ownSlice_persist _ _ _ $$ Husl with #Husl
    (try wp_auto)
    wp_apply wp_mapInsert $$ Hpm as Hpm
    (try wp_auto)
    wp_for_post
    iframe
    iexists (j + 1), x, _
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    iframe
    have hnew : (M.lookup x.Name').isSome = false := by
      rw [Bool.eq_false_iff]; intro h
      exact name_fresh pl j x Hnd hx ((Hk.2 _).1 h)
    isplitl
    · iintro !>
      iapply (BigSepM.bigSepM_insert (by
        rw [gmap_get?_eq]; cases hl : M.lookup x.Name' <;> simp_all)).2
      isplitr
      · iExactEq Husl
        rw [iuP_at pl j x Hnd hx]
        rfl
      iexact Hsls
    ipureintro
    refine ⟨by omega, fun n => ?_⟩
    rw [List.take_add_one, hx, GMap.lookup_insert_is_Some]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton]
    rw [← Hk.2 n]
    constructor
    · rintro (rfl | ⟨-, h⟩)
      · exact Or.inr rfl
      · exact Or.inl h
    · rintro (h | rfl)
      · by_cases he : x.Name' = n
        · exact Or.inl he
        · exact Or.inr ⟨he, h⟩
      · exact Or.inl rfl
  -- the map built: every entry's name, its one peer URL
  have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z cv.Cluster'.len := by word
  simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
  have hjl : j = pl.length := by omega
  subst hjl
  have Hdom : ∀ n, (M.lookup n).isSome ↔ n ∈ pl.map (·.Name') := by
    intro n; rw [Hk.2 n, List.take_of_length_le (Nat.le_refl _)]
  imod ownMap_persist _ _ _ $$ Hpm with #Hpm
  (try wp_auto)
  -- `mode`
  rcases Classical.em (cv.Retention' = W64 0) with hr | hr
  all_goals first | rw [decide_eq_true hr] | rw [decide_eq_false hr]
  all_goals (
    (try wp_auto)
    -- the URL slices
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %pu ⟨Hpu, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    imod ownSlice_persist _ _ _ $$ Hpu with #Hpu
    (try wp_auto)
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %cu ⟨Hcu, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    imod ownSlice_persist _ _ _ $$ Hcu with #Hcu
    (try wp_auto)
    -- the feature gate
    wp_apply wp_FG as %fgp ⟨%Hfgp, #Hfg, #Hfgc, #Hflc⟩
    (try wp_auto)
    -- `if c.Auth`
    cases ha : cv.Auth'
    all_goals (
      (try wp_auto)
      iapply HΦ
      iexists pm, M, _, _, fgp
      isplitr
      · ipureintro
        refine ⟨?_, Hfgp, Hdom⟩
        simp only [memberCfg, ha, hr, ↓reduceIte, Bool.false_eq_true]
        rfl
      iframe Hpm Hsls
      isplitr; · iExactEq Hpu; rfl
      isplitr; · iExactEq Hcu; rfl
      iframe Hfg Hfgc Hflc))

end proof

end server
end etcd_dist
end EtcdGrove
end Perennial
