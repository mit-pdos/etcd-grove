/- Port of election_proof/proof_readOnly__recvAck.v.

Lean notes: Rocq's `wp_max2_uint64` is stepped by hand (`wp_func_call; wp_call`, then a
case split on the comparison), as Perennial's own `wp_readOnly_recvAck`
(`v3_proof/readonly.lean`) does. -/
module

public import Spec.go_etcd_io.raft.v3.readOnly__recvAck

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [GoGlobalContext] in
private theorem readonlyRecvAck_nil (r : ReadOnly) (src : w64) :
    readonlyRecvAck r src [] = r := by
  simp [readonlyRecvAck]

omit [GoGlobalContext] in
private theorem readonlyRecvAck_cons (r : ReadOnly) (src : w64) (cs : List w8) (H : cs ≠ []) :
    readonlyRecvAck r src cs =
      { r with acks := <[src := w64Max ((r.acks !! src).getD (W64 0))
                                       (leToU64 (cs.take 8))]> r.acks } := by
  simp [readonlyRecvAck, H]

theorem readOnly.recvAck.wp_proof : readOnly.recvAck.spec (GF := GF) (hG := hG) := by
  intro ro r src ctx cs dq
  wp_start as Hown
  iNamed Hown
  unfold ownReadOnly
  iNamed Hown
  ihave %Hcl := ownSlice_len _ _ _ $$ Hctx
  wp_auto
  wp_if_destruct
  · have Hnil : cs = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hcl.1]; simp only [sint.nat]; word
    subst Hnil
    iapply HΦ
    iframe Hctx
    rw [readonlyRecvAck_nil]
    iexists rov, ptrs
    iframe Hro Hacks Hucr Hucr_cap Hreqs
    ipureintro; exact ⟨Hro_conf, Hro_safe⟩
  · have Hne : cs ≠ [] := by
      intro h; subst h; apply Hif; simp at Hcl; word
    have Hcs8 : 8 ≤ cs.length := by
      rcases Hlen with h | h
      · exact absurd h Hne
      · exact h
    wp_apply wp_map_lookup1 $$ Hacks as Hacks
    rw [show cs = cs.take 8 ++ cs.drop 8 from (List.take_append_drop 8 cs).symm]
    wp_apply encoding.binary.wp_LittleEndian_Uint64 ctx (cs.take 8) dq (cs.drop 8)
      (by rw [List.length_take]; omega) $$ [$Hctx] as Hctx
    wp_func_call
    wp_call
    rw [List.take_append_drop]
    wp_if_destruct
    all_goals
      wp_apply wp_mapInsert $$ Hacks as Hacks
      iapply HΦ
      iframe Hctx
      rw [readonlyRecvAck_cons r src cs Hne]
      iexists rov, ptrs
      simp only [named]
      iframe Hro Hucr Hucr_cap Hreqs
      isplitr
      · ipureintro; exact Hro_conf
      isplitr
      · ipureintro; exact Hro_safe
    · iExactEq Hacks
      simp only [w64Max, show zero_val w64 = W64 0 from rfl] at Hif ⊢
      rw [ite_eq_left Hif]
    · iExactEq Hacks
      simp only [w64Max, show zero_val w64 = W64 0 from rfl] at Hif ⊢
      rw [ite_eq_right Hif]

end proof

end EtcdGrove
end Perennial
