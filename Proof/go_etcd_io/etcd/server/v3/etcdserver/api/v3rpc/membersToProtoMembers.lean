/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.membersToProtoMembers

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.membersToProtoMembers.wp_proof :
    v3rpc.membersToProtoMembers.spec (GF := GF) (hG := hG) := by
  intro sl ms
  wp_start as Hms
  iunfold membership.membersAt at Hms
  icases Hms with ⟨Hsl, Hown⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  wp_auto
  wp_apply (wp_slice_make2 (V := Loc) sl.len) as %psl ⟨Hpsl, -⟩
  · ipureintro; word
  (try wp_auto)
  try rw [if_pos (by refine ⟨by word, by word, by word⟩)]
  (try wp_auto)
  ihave %Hpl := ownSlice_len $$ Hpsl
  ihave IH : iprop(∃ (n : w64) (ps : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "Hsl" ∷ sl ↦* ms ∗ "Hown" ∷ ([∗list] m ∈ ms, membership.ownMember m) ∗
      "Hpsl" ∷ psl ↦* ps ∗ "%Hps" ∷ ⌜ps.length = ms.length⌝ ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ms.length : Int)⌝) $$ [i Hsl Hown Hpsl]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_replicate]; word
    · word
    · word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ms.length := by word
    obtain ⟨m0, Hm0⟩ : ∃ m0, ms[sint.nat n]? = some m0 := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index sl (sint.Z n) ms (DFrac.own 1) m0 Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hm0
    icases (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
      (Φ := fun (_ : Nat) (y : Loc) => membership.ownMember (GF := GF) y) Hm0).1 $$ Hown
      with ⟨Hm, Hclose⟩
    iunfold membership.ownMember at Hm
    icases Hm with ⟨%id, Hm⟩
    iunfold membership.memberIs at Hm
    icases Hm with ⟨%Hmn, %pu, %cu, %il, %nm, %pus, %cus, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
    (try wp_auto)
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index sl (sint.Z n) ms (DFrac.own 1) m0 Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hm0
    (try wp_auto)
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index sl (sint.Z n) ms (DFrac.own 1) m0 Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hm0
    (try wp_auto)
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index sl (sint.Z n) ms (DFrac.own 1) m0 Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hm0
    (try wp_auto)
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index sl (sint.Z n) ms (DFrac.own 1) m0 Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hm0
    (try wp_auto)
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index sl (sint.Z n) ms (DFrac.own 1) m0 Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hm0
    (try wp_auto)
    have hpl : sint.Z n < (ps.length : Int) := by rw [Hps]; word
    wp_auto
    wp_apply (wp_store_slice_index psl (sint.Z n) ps _) $$ [$Hpsl] as Hpsl
    · ipureintro; exact ⟨Hn.1, hpl⟩
    (try wp_auto)
    ihave Hm : membership.ownMember m0 $$ [Hid Hpu Hil Hnm Hcu Hpus Hcus]
    · iunfold membership.ownMember; iexists id
      iunfold membership.memberIs
      iframe
      ipureintro; exact Hmn
    ihave Hown := Hclose $$ Hm
    have hs : ms.set (sint.nat n) m0 = ms := by
      apply List.ext_getElem?
      intro k
      rw [List.getElem?_set]
      split
      · rename_i hk; subst hk; rw [Hm0]; try simp [Hlt]
      · rfl
    rw [hs]
    wp_for_post
    iframe
    iexists n + W64 1, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_set]; exact Hps
    · word
    · word
  · iapply HΦ
    itrivial
end proof

end EtcdGrove
end Perennial
