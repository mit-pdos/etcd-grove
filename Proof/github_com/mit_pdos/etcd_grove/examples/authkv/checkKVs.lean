/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/checkKVs.lean`: each key-value's
key is permitted. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.checkKVs
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Permitted

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem checkKVs.wp_proof (wp_Permitted : Permitted.spec (GF := GF) (hG := hG)) :
    checkKVs.spec (GF := GF) (hG := hG) := by
  intro who sl ps kvs Hok
  wp_start as ⟨#Hps, #Hkvs⟩
  ihave %Hsl := ownSlice_len $$ Hps
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hkl, #Hkv⟩
  wp_auto
  ihave HI : (∃ (j : w64) (p0 : Loc),
      "i" ∷ i_ptr ↦ j ∗ "kv" ∷ kv_ptr ↦ p0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i kv]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z sl.len :=
      Classical.byContradiction fun h => by simp [h] at Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hlt⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem ps (sint.nat j) as p
    obtain ⟨v, Hv⟩ : ∃ v, kvs[sint.nat j]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hkl]; word)⟩
    wp_apply wp_load_slice_index sl (sint.Z j) ps DFrac.discard p Hj.1 $$ [Hps] as -
    · iframe #; ipureintro; exact Hp_lookup
    ihave #Hp := Hkv $$ %(sint.nat j) %p %v %Hp_lookup %Hv
    iunfold txn.kvIs at Hp
    icases Hp with ⟨%keySl, %valSl, #Hk, #Hks, -⟩
    (try wp_auto)
    wp_apply wp_bytes_to_string keySl v.key DFrac.discard $$ [] as -
    · iexact Hks
    wp_apply wp_Permitted
    rw [decide_eq_true (Hok v (List.mem_of_getElem? Hv))]
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, p
    iframe
    ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ; itrivial

end proof

end authkv
end EtcdGrove
end Perennial
