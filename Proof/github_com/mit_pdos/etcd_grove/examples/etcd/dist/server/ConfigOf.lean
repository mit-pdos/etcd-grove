/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/server/ConfigOf.lean`. Lean-first (no Rocq
counterpart); etcd-dist N5 (`notes/etcd-dist-plan.md` §19). The range over the deployment's members (read-only,
`deploymentRepr`) appends one `server.Peer` literal per member to `cl` (`append`), so after `j` iterations `cl`
holds `peerOf` of the first `j` members; then member `i`'s entry (`i` in range) and the `Config` literal, whose
fields are `configOf`'s (`Token` and `Cfg` from `deploymentRepr`); `cl` persisted (`ownSlice_persist`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.ConfigOf

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

attribute [-instance] pure_wp_slice_for_range

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]

theorem ConfigOf.wp_proof : ConfigOf.spec (GF := GF) (hG := hG) := by
  intro v d i m hm hlen64
  unfold typed.maxMembers at hlen64
  wp_start as Hrepr
  iunfold deploymentRepr at Hrepr
  icases Hrepr with ⟨#Hmem, %Htok, %Hcfg, -⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hmem
  simp only [List.length_map] at Hlen
  have hil : i < d.members.length := (List.getElem?_eq_some_iff.1 hm).1
  (try wp_auto)
  irename i => Hiv
  unfold slice.forRange
  (try wp_auto)
  ihave Hc0 := ownSlice_nil (V := github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Peer) (GF := GF)
    (DFrac.own 1)
  ihave Hc1 := ownSliceCap_nil (V := github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Peer) (GF := GF)
  ihave HI : (∃ (j : Nat) (cls : GoSlice) (mv : deployment.Member),
      "i" ∷ i_ptr ↦ W64 j ∗ "m" ∷ m_ptr ↦ mv ∗ "cl" ∷ cl_ptr ↦ cls ∗
      "Hcls" ∷ cls ↦* (d.members.take j).map peerOf ∗
      "Hcap" ∷ ownSliceCap github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Peer cls (DFrac.own 1) ∗
      "%Hj" ∷ ⌜j ≤ d.members.length⌝ : IProp GF) $$ [i m cl Hc0 Hc1]
  · iexists 0, _, _
    simp only [List.take_zero, List.map_nil]
    iframe
    isplitl [Hc0]; · iExactEq Hc0; rfl
    isplitl [Hc1]; · iExactEq Hc1; rfl
    ipureintro; omega
  wp_for HI
  by_cases hj : j < d.members.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z v.Members'.len := by word
    simp only [decide_eq_true hc, eq_self_iff_true, decide_true, ↓reduceIte]
    (try wp_auto)
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, _root_.and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨mm, hmm⟩ : ∃ x, d.members[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    have hx : (d.members.map Member.val)[j]? = some (Member.val mm) := by simp [hmm]
    wp_apply (wp_load_slice_index v.Members' (sint.Z (W64 (j : Int))) (d.members.map Member.val) DFrac.discard
      (Member.val mm) h0) $$ [] as -
    · iframe #; ipureintro; rw [hsj]; exact hx
    (try wp_auto)
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %lit ⟨Hlit, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply (wp_slice_append cls _ _ _ (DFrac.own 1)) $$ [Hcls Hcap Hlit] as %cls' ⟨Hcls, Hcap, -⟩
    · iframe
    (try wp_auto)
    wp_for_post
    iframe
    iexists (j + 1), cls', (Member.val mm)
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    iframe
    isplitl [Hcls]
    · iExactEq Hcls
      rw [List.take_add_one, hmm]
      simp [peerOf, Member.val]
    ipureintro; omega
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z v.Members'.len := by word
    simp only [decide_eq_false hc, false_neq_true, decide_false, decide_true, Bool.false_eq_true,
      ↓reduceIte]
    have hjl : j = d.members.length := by omega
    subst hjl
    rw [List.take_of_length_le (Nat.le_refl _)]
    imod ownSlice_persist _ _ _ $$ Hcls with #Hcls
    (try wp_auto)
    have hi0 : 0 ≤ sint.Z (W64 i) := by word
    have hic : sint.Z (W64 i) < sint.Z v.Members'.len := by word
    try simp only [hi0, hic, _root_.and_self, ↓reduceIte]
    have hsi : (sint.Z (W64 i)).toNat = i := by word
    have hx : (d.members.map Member.val)[i]? = some (Member.val m) := by simp [hm]
    wp_apply (wp_load_slice_index v.Members' (sint.Z (W64 i)) (d.members.map Member.val) DFrac.discard
      (Member.val m) hi0) $$ [] as -
    · iframe #; ipureintro; rw [hsi]; exact hx
    (try wp_auto)
    iapply HΦ
    iunfold configRepr
    iexists m
    isplitr
    · ipureintro
      refine ⟨hm, ?_⟩
      simp [configOf, Member.val, ServerCfg.val, Htok, Hcfg]
    iexact Hcls

end proof

end server
end etcd_dist
end EtcdGrove
end Perennial
