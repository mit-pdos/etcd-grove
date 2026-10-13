/-
Proof of `Spec/.../backend/bucketBuffer__ForEach.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__ForEach
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RangeLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.bucketBuffer.ForEach.wp_proof : backend.bucketBuffer.ForEach.spec (GF := GF) (hG := hG) := by
  intro bb dq p es f P Q
  wp_start as ⟨H, #Hf, HP⟩
  iunfold bbAt at H
  icases H with ⟨Hbb, Hs, Hcap, #Hro, #Hin⟩
  icases bb_fields_acc _ _ _ $$ Hbb with ⟨Hbuf, Hused, Hbb⟩
  ihave #Hin2 := Hin
  iunfold entsIn at Hin2
  icases Hin2 with ⟨%Hle, -⟩
  iunfold visitorSpec at Hf
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  ihave HI : (∃ n : w64, "i" ∷ i_ptr ↦ n ∗ "HP" ∷ P (sint.nat n) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ es.length⌝ : IProp GF) $$ [i HP]
  · iexists W64 0
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  have Hlen : sint.Z (W64 (es.length : Int)) = es.length := by have := Hl.1; have := Hl.2; word
  wp_if_destruct
  · have hn : sint.nat n < es.length := by word
    list_elem es (sint.nat n) as e
    list_elem p.kvs (sint.nat n) as x
    have Hbn : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z p.buf.len := by
      have := Hl.1; refine ⟨Hn.1, ?_⟩; word
    try simp only [Hbn, _root_.and_self, ite_true]
    wp_apply wp_load_slot_key p.buf (sint.Z n) p.kvs dq x Hn.1 Hx_lookup $$ Hs as Hs
    try simp only [Hbn, _root_.and_self, ite_true]
    wp_apply wp_load_slot_val p.buf (sint.Z n) p.kvs dq x Hn.1 Hx_lookup $$ Hs as Hs
    ihave ⟨#Hk, #Hv⟩ := entsIn_lookup _ _ _ _ _ Hx_lookup He_lookup $$ Hin
    ihave #Hc := Hf $$ %(sint.nat n) %e %x.key' %x.val' []
    · ipureintro; exact He_lookup
    wp_apply Hc $$ [HP] as %err Hr
    · iframe # ∗
    icases Hr with (⟨%Herr, HP⟩ | ⟨%Herr, HQ⟩)
    · subst Herr
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
      iframe
      ipureintro; constructor <;> word
    · cases err with
      | nil => exact absurd rfl Herr
      | ok eo =>
        wp_auto
        wp_for_post
        ihave Hbb := Hbb $$ Hbuf Hused
        iapply HΦ
        iunfold bbAt
        iframe # ∗
        iright; iframe; ipureintro; exact Herr
  · have hn : sint.nat n = es.length := by word
    ihave Hbb := Hbb $$ Hbuf Hused
    iapply HΦ
    iunfold bbAt
    rw [hn]
    iframe # ∗
    ileft; iframe; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
