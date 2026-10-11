/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/readSet__add.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.readSet__add
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTMMaps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem readSet.add.wp_proof (hGRR : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG)) :
    readSet.add.spec (GF := GF) (hG := hG) := by
  intro m pfx rsMap reads ksl ks resp rsl ps es
  wp_start as ⟨Hm, #Hrs, #Hks, #Hresp, #Hps, %Hlen, #Hall⟩
  wp_auto
  rename_i gi_ptr
  irename : gi_ptr ↦ (zero_val w64) => gi
  ihave %Hpsl := ownSlice_len _ _ _ $$ Hps
  ihave %Hksl := ownSlice_len _ _ _ $$ Hks
  ihave HI : (∃ (j x : w64) (rp : Loc) (rsMap' : GMap GoString Loc),
      "i" ∷ i_ptr ↦ j ∗ "gi" ∷ gi_ptr ↦ x ∗ "resp" ∷ resp_ptr ↦ rp ∗ "Hm" ∷ m ↦$ rsMap' ∗
      "#Hrs'" ∷ readsAt pfx rsMap' (readsAdd reads ((ks.zip es).take (sint.nat j))) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rsl.len⌝ : IProp GF) $$ [i gi resp Hm]
  · iexists W64 0, _, _, rsMap
    simp only [named]
    iframe i gi resp Hm
    isplitr
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      unfold readsAdd
      simp only [List.foldl_nil]
      iexact Hrs
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hif' : sint.Z j < sint.Z rsl.len := Hif
    have hj : sint.nat j < ps.length := by rw [Hpsl.1]; have := Hj.1; simp only [sint.nat, sint.Z] at *; omega
    list_elem ps (sint.nat j) as p
    have hje : sint.nat j < es.length := by omega
    have hjk : sint.nat j < ks.length := by omega
    list_elem es (sint.nat j) as e
    list_elem ks (sint.nat j) as k
    ihave #Hpe := Hall $$ %(sint.nat j) %p %k %e %(⟨Hp_lookup, Hk_lookup, He_lookup⟩)
    rw [ite_eq_left ⟨Hj.1, Hif'⟩]
    wp_apply wp_load_slice_index rsl (sint.Z j) ps DFrac.discard p Hj.1 $$ [] as -
    · iframe #; ipureintro; exact Hp_lookup
    ihave #Hpe' := Hpe
    unfold respOpReadAt
    icases Hpe' with ⟨%Hpnn, %w, %rr, #Hresp1, #Hrr, #Hread⟩
    ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    wp_apply hGRR p w rr $$ [$Hpb]
    · iframe Hresp1 Hrr; ipureintro; exact Hpnn
    have Hjk : sint.Z j < sint.Z ksl.len := by
      have := Hksl.1; have := Hj.1; simp only [sint.nat, sint.Z] at *; omega
    rw [ite_eq_left ⟨Hj.1, Hjk⟩]
    wp_apply wp_load_slice_index ksl (sint.Z j) ks DFrac.discard k Hj.1 $$ [] as -
    · iframe #; ipureintro; exact Hk_lookup
    (try wp_auto)
    wp_apply wp_mapInsert $$ Hm as Hm
    wp_for_post
    iframe
    iexists j + W64 1, j, p, _
    simp only [named]
    iframe
    have hsucc : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    rw [hsucc, readsAdd_take_succ reads ks es _ k e Hk_lookup He_lookup]
    isplitr
    · iapply readsAt_insert
      iframe Hrs' Hread
    ipureintro; word
  have hlen : sint.nat j = es.length := by
    rw [← Hlen.1, Hpsl.1]; have := Hj.2; simp only [sint.nat, sint.Z] at *; omega
  iapply HΦ
  iexists _
  iframe Hm
  rw [← readsAdd_take_all reads ks es (by omega), ← hlen]
  iexact Hrs'

end proof

end concurrency
end EtcdGrove
end Perennial
