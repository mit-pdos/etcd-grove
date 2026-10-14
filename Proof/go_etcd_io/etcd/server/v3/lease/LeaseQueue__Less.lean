/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/LeaseQueue__Less.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseQueue__Less
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.LeaseQueue.Less.wp_proof : lease.LeaseQueue.Less.spec (GF := GF) (hG := hG) := by
  intro s xs q i j hi0 hi1 hj0 hj1
  wp_start as Hq
  iunfold queueAt at Hq
  icases Hq with ⟨Hs, Hcap, Hits⟩
  ihave %Hlen := ownSlice_len s _ _ $$ Hs
  simp only [List.length_map] at Hlen
  have hj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨hj0, by word⟩
  have hi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := ⟨hi0, by word⟩
  obtain ⟨xj, hxj⟩ : ∃ x, xs[(sint.Z j).toNat]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨xi, hxi⟩ : ∃ x, xs[(sint.Z i).toNat]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  wp_auto
  simp only [hj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index s (sint.Z j) (xs.map Prod.fst) _ xj.1 hj0 $$ [Hs] as Hs
  · iframe; ipureintro; simp [hxj]
  icases (BigSepL.bigSepL_lookup_acc hxj).1 $$ Hits with ⟨Hxj, Hits⟩
  iunfold lwtAt at Hxj
  icases Hxj with ⟨#Hid, ⟨%t, Ht⟩, Hix⟩
  wp_auto
  ihave Hits := Hits $$ [Hid Ht Hix]
  · iunfold lwtAt; iframe Hid Hix; iexists t; iexact Ht
  rw [list_set_lookup_self xs (sint.Z j).toNat xj hxj]
  simp only [hi, _root_.and_self, ite_true]
  icases (BigSepL.bigSepL_lookup_acc hxi).1 $$ Hits with ⟨Hxi, Hits⟩
  iunfold lwtAt at Hxi
  icases Hxi with ⟨#Hid', ⟨%t', Ht'⟩, Hix'⟩
  wp_apply wp_load_slice_index s (sint.Z i) (xs.map Prod.fst) _ xi.1 hi0 $$ [Hs] as Hs
  · iframe; ipureintro; simp [hxi]
  wp_apply Time.wp_ptr_Before_dq $$ [$Ht'] as %b Ht'
  iapply HΦ
  ihave Hits := Hits $$ [Hid' Ht' Hix']
  · iunfold lwtAt; iframe Hid' Hix'; iexists t'; iexact Ht'
  rw [list_set_lookup_self xs (sint.Z i).toNat xi hxi]
  iunfold queueAt
  iframe

end proof

end EtcdGrove
end Perennial
