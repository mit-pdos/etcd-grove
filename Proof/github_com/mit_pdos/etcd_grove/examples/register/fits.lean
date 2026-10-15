/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/fits.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.fits

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem fits.wp_proof : fits.spec (GF := GF) (hG := hG) := by
  intro sl es dq
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe Hs
    ipureintro
    intro _ e0 He0
    have : es = [] := List.length_eq_zero_iff.mp (by rw [Hlen.1, Hif]; rfl)
    subst this; cases He0
  have Hne := Hif
  obtain ⟨e0, He0⟩ : ∃ e0, es[0]? = some e0 := by
    cases es with
    | nil => exfalso; apply Hne; simp at Hlen; word
    | cons e _ => exact ⟨e, rfl⟩
  have Hpos : 0 < sint.Z sl.len := by
    have := (List.getElem?_eq_some_iff.mp He0).1; obtain ⟨h1, h2⟩ := Hlen; word
  wp_if_destruct
  · rw [ite_eq_left (by word)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) e0 sl dq es (by word) (by simpa using He0) $$ Hs
      with ⟨He, Hsback⟩
    icases (AccessStrict.access_strict
        (A := (sliceIndexRef raftpb.Entry (sint.Z (W64 0)) sl).[raftpb.Entry, go!"Index"] ↦{dq}
          e0.Index')
        (A' := (sliceIndexRef raftpb.Entry (sint.Z (W64 0)) sl).[raftpb.Entry, go!"Index"] ↦{dq}
          e0.Index')
        (P := sliceIndexRef raftpb.Entry (sint.Z (W64 0)) sl ↦{dq} e0)) $$ He with ⟨He, Hclose⟩
    wp_auto
    ihave He := Hclose $$ He
    ihave Hs := Hsback $$ He
    rw [list_set_lookup_self es _ e0 (by simpa using He0)]
    iapply HΦ
    iframe Hs
    ipureintro
    intro Hd e0' He0'
    rw [List.head?_eq_getElem?, He0] at He0'
    cases He0'
    simp only [decide_eq_true_eq] at Hd
    obtain ⟨h1, h2⟩ := Hlen
    word
  · iapply HΦ
    iframe Hs
    ipureintro
    intro h; cases h

end proof

end register
end EtcdGrove
end Perennial
