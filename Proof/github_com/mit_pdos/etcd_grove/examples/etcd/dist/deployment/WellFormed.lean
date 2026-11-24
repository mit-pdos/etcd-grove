/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/WellFormed.lean`: every check
in Go's order, each failing one returning a fresh `fmt.Errorf` error (not `nil`); when all pass,
`goWellFormed d` holds, hence `d.WellFormed` (`WellFormedLemmas.goWellFormed_sound`). Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormed
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.nameOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.kindNames
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.boundsOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Kind__String
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.AddrOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.NodeCount
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.IdsOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.compatible
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.NeedsAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormedLemmas
public import Spec.fmt.ErrorfStrs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

/-- Arguments `fmt` formats safely: each a well-formed basic value. -/
theorem strArgOk_list (args : List GoInterface)
    (h : ∀ a ∈ args, ∃ ii, a = interface.ok ii ∧ fmt.ArgWf ii) :
    ⊢ ([∗list] a ∈ args, fmt.strArgOk (GF := GF) a) := by
  induction args with
  | nil => iintro; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons a args ih =>
    obtain ⟨ii, rfl, hw⟩ := h a (List.mem_cons_self ..)
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · unfold fmt.strArgOk; ileft; ipureintro; exact Or.inl hw
    · iapply ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem len_zero (s : GoSlice) (h : sint.nat s.len = 0) (h0 : 0 ≤ sint.Z s.len) : s.len = W64 0 := by
  word

theorem len_le (s : GoSlice) (n k : Nat) (h : ¬ sint.Z (W64 (k : Int)) < sint.Z s.len)
    (hl : n = sint.nat s.len) (hk : k < 2 ^ 63 := by decide) : n ≤ k := by
  word

set_option hygiene false in
/-- A check fails: `fmt.Errorf(format, args...)` (a fresh error, not `nil`) is returned. -/
local macro "err_exit" : tactic => `(tactic| (
  (try wp_auto)
  first
    | (wp_apply (hErrorf _ slice.nil [] (DFrac.own 1)) $$ [] as %e ⟨-, -, -⟩
       · iframe; isplitl
         · iapply ownSlice_nil
         · iapply BigSepL.bigSepL_nil.2; itrivial)
    | (wp_apply wp_slice_literal
       isplitr
       · ipureintro; rfl
       iintro %asl ⟨Hasl, -⟩
       wp_apply (hErrorf _ _ _ (DFrac.own 1)) $$ [Hasl] as %e ⟨-, -, -⟩
       · iframe
         iapply strArgOk_list
         intro a ha
         simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
         first
           | (rcases ha with rfl | rfl <;> exact ⟨_, rfl, by first | exact argWf_int _ | exact argWf_string _⟩)
           | (subst ha; exact ⟨_, rfl, by first | exact argWf_int _ | exact argWf_string _⟩))
  (try wp_auto)
  repeat wp_for_post
  iapply HΦ
  ipureintro; intro h; cases h))

theorem idx_facts (s : GoSlice) (j len : Nat) (hl : len = sint.nat s.len) (h0l : 0 ≤ sint.Z s.len)
    (h : sint.Z (W64 (j : Int)) < sint.Z s.len) (hj : j ≤ len) :
    j < len ∧ 0 ≤ sint.Z (W64 (j : Int)) ∧ (sint.Z (W64 (j : Int))).toNat = j ∧
      W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by
  refine ⟨by word, by word, by word, by word⟩

theorem idx_end (s : GoSlice) (j len : Nat) (hl : len = sint.nat s.len) (h0l : 0 ≤ sint.Z s.len)
    (h : ¬ sint.Z (W64 (j : Int)) < sint.Z s.len) (hj : j ≤ len) : j = len := by
  word

theorem strlen_le (n k : Nat) (hn : n < 2 ^ 63) (hk : k < 2 ^ 63)
    (h : ¬ sint.Z (W64 (n : Int)) > sint.Z (W64 (k : Int))) : n ≤ k := by
  word

theorem deployment.WellFormed.wp_proof
    (hNameOk : etcd_dist.deployment.nameOk.spec (GF := GF) (hG := hG))
    (hNames : etcd_dist.deployment.kindNames.spec (GF := GF) (hG := hG))
    (hBounds : etcd_dist.deployment.boundsOk.spec (GF := GF) (hG := hG))
    (hString : etcd_dist.deployment.Kind.String.spec (GF := GF) (hG := hG))
    (hAddr : etcd_dist.deployment.AddrOk.spec (GF := GF) (hG := hG))
    (hNodeCount : etcd_dist.deployment.NodeCount.spec (GF := GF) (hG := hG))
    (hIds : etcd_dist.deployment.IdsOk.spec (GF := GF) (hG := hG))
    (hCompat : etcd_dist.deployment.compatible.spec (GF := GF) (hG := hG))
    (hAuth : etcd_dist.deployment.NeedsAuth.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.ErrorfStrs.spec (GF := GF) (hG := hG)) :
    etcd_dist.deployment.WellFormed.spec (GF := GF) (hG := hG) := by
  intro v d hfips
  wp_start as #Hd
  wp_auto
  iunfold deploymentRepr at Hd
  icases Hd with ⟨#Hm, %htok, %hcfg, #Hw, %ss, #Hn, #Hns⟩
  ihave %Hlm := ownSlice_len _ _ _ $$ Hm
  rw [List.length_map] at Hlm
  wp_if_destruct
  · err_exit
  have hne0 := Hif
  wp_if_destruct
  · err_exit
  have hle64 := Hif
  have hmem : d.members ≠ [] := by
    intro h; rw [h] at Hlm; exact hne0 (len_zero _ Hlm.1.symm Hlm.2)
  have hmax : d.members.length ≤ etcd_dist.typed.maxMembers := len_le _ _ _ hle64 Hlm.1
  wp_apply (wp_map_make1 (K := GoString) (V := Bool)) as %nm Hnm
  ihave HI : (∃ (j : Nat) (mv : deployment.Member) (mp : GMap GoString Bool),
      "i" ∷ i_ptr ↦ W64 j ∗ "m" ∷ m_ptr ↦ mv ∗ "Hnm" ∷ nm ↦$ mp ∗
      "%Hj" ∷ ⌜j ≤ d.members.length ∧
        (∀ k, mp !! k = if k ∈ (d.members.take j).map Member.name then some true else none) ∧
        ((d.members.take j).map Member.name).Nodup ∧
        (∀ m ∈ d.members.take j, etcd_dist.typed.nameOk m.name = true ∧ m.name.length ≤ etcd_dist.typed.maxLen)⌝ :
      IProp GF) $$ [i m Hnm]
  · iexists 0, _, ∅
    iframe
    ipureintro
    exact ⟨by omega, fun k => by simp, by simp, fun m hm => by simp at hm⟩
  wp_for HI
  obtain ⟨Hj1, Hj2, Hj3, Hj4⟩ := Hj
  wp_if_destruct
  · obtain ⟨hj, h0, hsj, hw⟩ := idx_facts _ _ _ Hlm.1 Hlm.2 Hif Hj1
    simp only [h0, Hif, and_self, ↓reduceIte]
    obtain ⟨mm, hmm⟩ : ∃ mm, d.members[j]? = some mm := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index v.Members' (sint.Z (W64 (j : Int))) (d.members.map Member.val) DFrac.discard mm.val h0) $$ [] as -
    · iframe #; ipureintro; rw [hsj, List.getElem?_map, hmm]; rfl
    have htake : d.members.take (j + 1) = d.members.take j ++ [mm] := by
      rw [List.take_add_one, hmm]; rfl
    wp_apply hNameOk
    by_cases hn : typed.nameOk mm.name = true
    · rw [hn]
      simp only [Bool.not_true]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsl
      wp_if_destruct
      · err_exit
      · have hl255 := strlen_le _ 255 Hsl (by decide) Hif
        wp_apply (wp_map_lookup1 _ _ nm mp mm.name) $$ [Hnm] as Hnm
        · iframe
        rw [Hj2]
        by_cases hin : mm.name ∈ (d.members.take j).map Member.name
        · rw [if_pos hin]
          simp only [Option.getD_some]
          err_exit
        · rw [if_neg hin]
          simp only [Option.getD_none]
          rw [show (zero_val Bool) = false from rfl]
          wp_auto
          wp_apply wp_mapInsert $$ [Hnm] as Hnm
          · iframe
          wp_for_post
          iframe
          iexists (j + 1), _, _
          rw [hw]
          iframe
          ipureintro
          refine ⟨by omega, ?_, ?_, ?_⟩
          · intro k
            rw [htake, List.map_append]
            by_cases hk : k = mm.name
            · subst hk; simp
            · rw [lookup_insert_ne mp true (Ne.symm hk), Hj2 k]; simp [hk]
          · rw [htake, List.map_append, List.nodup_append]
            refine ⟨Hj3, by simp, ?_⟩
            intro a ha b hb hab
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
            subst hb; subst hab; exact hin ha
          · intro m hm
            rw [htake, List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | rfl
            · exact Hj4 m hm
            · exact ⟨hn, hl255⟩
    · rw [Bool.not_eq_true] at hn
      rw [hn]
      simp only [Bool.not_false]
      err_exit
  · skip

end proof

end etcd_dist
end EtcdGrove
end Perennial
