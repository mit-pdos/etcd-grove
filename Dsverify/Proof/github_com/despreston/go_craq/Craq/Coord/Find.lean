/-
`findReplicaIndex(address, replicas)`: the first replica with the address.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.UpdateNode

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions] [LogSpecs GF]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

theorem wp_findReplicaIndex (cfg : Cfg GF) (a : GoString) (sl : GoSlice) (rs : List Rep)
    (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
        sl ↦*{dq} rs.map Rep.loc ∗ [∗list] r ∈ rs, nodeFacts cfg r.loc r.addr }}
      (App (App (Val (@! coordinator.findReplicaIndex)) (Val #a)) (Val #sl))
    {{ (i : w64) (found : Bool), RET (PairV #i #found); sl ↦*{dq} rs.map Rep.loc ∗
        ⌜found = true → 0 ≤ sint.Z i ∧ ∃ r, rs[sint.nat i]? = some r ∧ r.addr = a⌝ }} := by
  wp_start as ⟨Hsl, #Hnfs⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  simp only [List.length_map] at Hlen
  wp_auto
  rename_i k_ptr
  irename : (k_ptr ↦ zero_val w64 : IProp GF) => k
  ihave IH : iprop(∃ (n kv : w64) (rp : Loc),
      "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ kv ∗ "replica" ∷ replica_ptr ↦ rp ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝) $$ [i k replica]
  · iexists _, _, _
    iframe
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.nat n < rs.length := by word
    list_elem rs (sint.nat n) as r
    ihave #Hnf := nodeFacts_at cfg rs _ r Hr_lookup $$ Hnfs
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) (rs.map Rep.loc) dq r.loc Hn.1 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact locs_at rs _ r Hr_lookup
    wp_apply wp_node_Address' cfg r.loc r.addr $$ Hnf
    wp_if_destruct
    · wp_for_post
      iapply HΦ
      iframe
      ipureintro
      intro _
      exact ⟨Hn.1, r, Hr_lookup, rfl⟩
    · wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; exact ⟨by word, by word⟩
  · iapply HΦ
    iframe
    ipureintro
    intro h; cases h

end proof

end github_com.despreston.go_craq

end Perennial
