/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/cloneCommittedEntries.lean`: `make` and
`copy`. Lean-first (2026-10-17, etcd-io/etcd#22496).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cloneCommittedEntries

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem cloneCommittedEntries.wp_proof : cloneCommittedEntries.spec (GF := GF) (hG := hG) := by
  intro ents L dq
  wp_start as Hents
  ihave %Hlen := ownSlice_len $$ Hents
  wp_auto
  wp_if_destruct
  · -- `len(ents) == 0`: nil
    have hL : L = [] := List.eq_nil_of_length_eq_zero (by word)
    subst hL
    iapply HΦ
    iframe Hents
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; intro _; rfl
  · wp_apply wp_slice_make2 $$ [] as %sl ⟨Hsl, Hcap⟩
    · ipureintro; word
    wp_apply wp_slice_copy $$ [Hsl Hents] as %k ⟨%Hk, Hsl, Hents⟩
    · iframe
    wp_auto
    iapply HΦ
    rw [List.length_replicate, ← Hlen.1, List.take_length, List.drop_of_length_le (by simp),
      List.append_nil]
    iframe
    ipureintro
    intro hL
    subst hL
    exfalso; apply Hif; simp at Hlen; word

end proof

end EtcdGrove
end Perennial
