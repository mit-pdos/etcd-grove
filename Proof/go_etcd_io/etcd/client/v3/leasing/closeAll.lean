/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/closeAll.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.closeAll

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem closeAll.wp_proof : closeAll.spec (GF := GF) (hG := hG) := by
  intro sl cs dq
  wp_start as ⟨Hsl, Hcs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (n : w64) (c0 : GoChan),
      "i" ∷ i_ptr ↦ n ∗ "ch" ∷ ch_ptr ↦ c0 ∗ "Hcs" ∷ ([∗list] c ∈ cs.drop (sint.nat n), waitcClose c) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (cs.length : Int)⌝) $$ [i ch Hcs]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < cs.length := by word
    obtain ⟨c, Hci⟩ : ∃ c, cs[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) cs dq c Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hci
    rw [List.drop_eq_getElem_cons Hlt] at *
    rw [show cs[sint.nat n] = c by simp [List.getElem?_eq_getElem Hlt] at Hci; exact Hci]
    icases Hcs with ⟨Hc, Hcs⟩
    unfold waitcClose
    icases Hc with ⟨%γch, Hc⟩
    wp_apply wp_broadcast_chan_close $$ [$Hc] as -
    · unfold waitQ; imodintro; itrivial
    wp_for_post
    iframe
    iexists n + W64 1, c
    simp only [named]
    iframe
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
    iframe
    ipureintro; constructor <;> word
  · iapply HΦ
    iframe

end proof

end leasing
end EtcdGrove
end Perennial
