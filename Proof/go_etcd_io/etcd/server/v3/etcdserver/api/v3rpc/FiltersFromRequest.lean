/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.FiltersFromRequest

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

theorem v3rpc.FiltersFromRequest.wp_proof : v3rpc.FiltersFromRequest.spec (GF := GF) (hG := hG) := by
  intro cr fs filters dq
  wp_start as ⟨Hf, #Hfs⟩
  ihave %Hfl := ownSlice_len _ _ _ $$ Hfs
  (try wp_auto)
  wp_apply wp_slice_make3 (V := GoFunc) (W64 0) fs.len (by word) as %sl0 ⟨Hsl0, Hcap0, -⟩
  (try wp_auto)
  ihave IH : iprop(∃ (n : w64) (sl : GoSlice) (fl : List GoFunc) (fv : w32),
      "i" ∷ i_ptr ↦ n ∗ "filters" ∷ filters_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* fl ∗
      "Hcap" ∷ ownSliceCap GoFunc sl (DFrac.own 1) ∗ "ft" ∷ ft_ptr ↦ fv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ filters.length ∧ fl.length ≤ sint.nat n⌝)
    $$ [i filters Hsl0 Hcap0 ft]
  · iexists W64 0, sl0, _, _
    iframe
    ipureintro; simp
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < filters.length := by rw [Hfl.1]; word
    obtain ⟨f, Hf'⟩ : ∃ f, filters[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z fs.len from ⟨Hn.1, Hif⟩, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index fs (sint.Z n) filters DFrac.discard f Hn.1 $$ [$Hfs] as -
    · ipureintro; simpa using Hf'
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply wp_slice_literal (V := GoFunc) (l := [functions v3rpc.filterNoPut []])
      isplitr
      · ipureintro; rfl
      iintro %zsl ⟨Hz, Hzcap⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hz] as %sl1 ⟨Hsl, Hcap, _⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, sl1, fl ++ [functions v3rpc.filterNoPut []], _
      iframe
      ipureintro
      simp only [List.length_append, List.length_singleton]
      refine ⟨by word, by word, by word⟩
    · wp_if_destruct
      · (try wp_auto)
        wp_apply wp_slice_literal (V := GoFunc) (l := [functions v3rpc.filterNoDelete []])
        isplitr
        · ipureintro; rfl
        iintro %zsl ⟨Hz, Hzcap⟩
        (try wp_auto)
        wp_apply wp_slice_append $$ [$Hsl $Hcap $Hz] as %sl1 ⟨Hsl, Hcap, _⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, sl1, fl ++ [functions v3rpc.filterNoDelete []], _
        iframe
        ipureintro
        simp only [List.length_append, List.length_singleton]
        refine ⟨by word, by word, by word⟩
      · (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, sl, fl, _
        iframe
        ipureintro
        refine ⟨by word, by word, by word⟩
  · iapply HΦ
    iframe Hf
    iexists fl
    iframe Hsl
    ipureintro
    have hge : filters.length ≤ sint.nat n := by rw [Hfl.1]; word
    refine ⟨by omega, fun h => ?_⟩
    subst h
    have h1 := Hn.2.1
    have h2 := Hn.2.2
    simp only [List.length_nil] at h1
    exact List.eq_nil_of_length_eq_zero (by omega)

end proof

end EtcdGrove
end Perennial
