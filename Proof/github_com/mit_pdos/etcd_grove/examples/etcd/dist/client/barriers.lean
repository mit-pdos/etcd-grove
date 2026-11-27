/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/barriers.lean`: the range loop over the
endpoints, each `barrier` (`barrier.spec`), the floors gathered over the prefix done. Lean-first (no Rocq
counterpart); F7 stage S4.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.barriers
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.barrier

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.authd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 800000 in
theorem barriers.wp_proof (wp_barrier : barrier.spec (GF := GF) (hG := hG)) :
    barriers.spec (GF := GF) (hG := hG) := by
  intro π eps addrs V Γ γR L₀ Htb Hpe hAs Hau Hauth HγR
  wp_start as ⟨Hlt, #Heps, #Hms, #HL0⟩
  ihave %Hlen := ownSlice_len $$ Heps
  (try wp_auto)
  ihave IB : (∃ (j : w64) (av : GoString),
      "i" ∷ i_ptr ↦ j ∗ "a" ∷ a_ptr ↦ av ∗ "Hlt" ∷ levelTok 0 ∗
      "#Hok" ∷ ([∗list] a ∈ addrs.take (sint.nat j), barrierFloor Γ γR L₀ a) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ addrs.length⌝ : IProp GF) $$ [i a Hlt]
  · iexists W64 0, _
    have h00 : sint.nat (W64 0) = 0 := rfl
    simp only [h00, List.take_zero]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; exact ⟨by decide, by omega⟩
  wp_for IB
  wp_if_destruct
  · have hlt : sint.nat j < addrs.length := by have := Hlen.1; word
    list_elem addrs (sint.nat j) as aj
    have hnz : (sint.Z j).toNat = sint.nat j := by word
    have Hbm : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z eps.len := ⟨Hj.1, Hif⟩
    (try wp_auto)
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index eps (sint.Z j) _ _ aj Hbm.1 $$ [Heps] as -
    · iframe #; ipureintro; rw [hnz]; exact Haj_lookup
    (try wp_auto)
    have hmem : aj ∈ addrs := List.mem_of_getElem? Haj_lookup
    ihave #Hms' := Hms
    iunfold membersAt at Hms'
    ihave ⟨%midj, #Hatj⟩ := BigSepL.bigSepL_lookup Haj_lookup $$ Hms'
    ihave #Hmsj := membersAt_one (Gg := hG.goose_globalGS) aj Γ midj $$ Hatj
    wp_apply (wp_barrier aj V Γ γR L₀ Htb (Hpe aj hmem) hAs Hau Hauth HγR) $$ [$Hlt] as %okj ⟨Hlt, Hbj⟩
    · iframe #
    icases Hbj with (%Hb | ⟨%Hb, #Hfl⟩) <;> subst Hb
    · (try wp_auto)
      wp_for_post
      iapply HΦ; iframe Hlt; ileft; ipureintro; rfl
    (try wp_auto)
    have htk : addrs.take (sint.nat j + 1) = addrs.take (sint.nat j) ++ [aj] := by
      rw [List.take_add_one, Haj_lookup, Option.toList_some]
    ihave #Hok' : [∗list] a ∈ addrs.take (sint.nat j + 1), barrierFloor Γ γR L₀ a $$ []
    · rw [htk]
      iapply BigSepL.bigSepL_snoc.2
      iframe #
    iclear Hok
    wp_for_post
    iframe
    have hn1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    iexists j + W64 1, aj
    rw [hn1]
    iframe
    iframe #
    ipureintro; exact ⟨by word, by omega⟩
  · have hnk' : sint.nat j = addrs.length := by have := Hlen.1; word
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iright
    isplitl []
    · ipureintro; rfl
    iExactEq Hok; rw [hnk', List.take_of_length_le (by omega)]

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
