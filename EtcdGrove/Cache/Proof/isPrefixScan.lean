/-
Proof of `Spec/isPrefixScan.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.isPrefixScan

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem isPrefixScan.wp_proof : isPrefixScan.spec (GF := GF) (hG := hG) := by
  intro sl key dq
  wp_start as Hsl
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_if_destruct
  · obtain ⟨b, Hb⟩ : ∃ b, key[0]? = some b := ⟨_, List.getElem?_eq_getElem (by word)⟩
    rw [ite_eq_left (by word), show sint.Z (W64 0) = 0 from rfl]
    wp_apply wp_load_slice_index sl 0 key dq b (by omega) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact Hb
    have Hk : key = [b] := by
      match key, Hlen, Hb with
      | [x], _, Hb => simp at Hb; rw [Hb]
      | [], Hl, _ => simp at Hl; word
      | _ :: _ :: _, Hl, _ => simp at Hl; word
    subst Hk
    rw [show decide (b = W8 0) = decide ([b] = [W8 0]) by simp]
    iapply HΦ $$ Hsl
  · have : key ≠ [W8 0] := by
      intro h; subst h; simp at Hlen; apply Hif; word
    rw [decide_eq_false this]
    iapply HΦ $$ Hsl

end proof

end EtcdGrove
end Perennial
