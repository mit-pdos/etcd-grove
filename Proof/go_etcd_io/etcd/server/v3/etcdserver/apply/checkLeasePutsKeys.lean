/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePutsKeys

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
theorem apply.checkLeasePutsKeys.wp_proof :
    apply.checkLeasePutsKeys.spec (GF := GF) (hG := hG) := by
  intro st P f ai info dq l id
  wp_start as ⟨#Hst, Hai, #Hl⟩
  iunfold apply.isAuthStore at Hst
  icases Hst with ⟨%sti, %Hsti, #HPut, -, -, #HAdmin, -⟩
  subst Hsti
  iunfold apply.leaseIs at Hl
  icases Hl with ⟨%Hln, -, -, #HKeys⟩
  wp_auto
  wp_apply HAdmin $$ [$Hai] as %err Hai
  cases err with
  | nil =>
    wp_auto
    iapply HΦ; iexact Hai
  | ok e =>
  wp_auto
  wp_apply HKeys as %sl ⟨%ks, Hks⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hks
  irename «as» => Has
  iunfold apply.permCheck2 at HPut
  ihave IH : iprop(∃ (n : w64) (k : GoString),
      "i" ∷ i_ptr ↦ n ∗ "key" ∷ key_ptr ↦ k ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝) $$ [i key]
  · iexists W64 0, _
    iframe i key
    ipureintro
    constructor
    · decide
    · have := Hsll.2; word
  wp_for IH
  wp_if_destruct
  · obtain ⟨kx, Hkx⟩ : ∃ kx, ks[(sint.Z n).toNat]? = some kx :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) _ _ kx Hn.1 $$ [Hks] as Hks
    · iframe; ipureintro; exact Hkx
    wp_apply wp_string_to_bytes kx as %bsl ⟨Hb, -⟩
    wp_apply HPut $$ [$Hai $Hb] as %err ⟨Hai, -⟩
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, kx
      iframe
      ipureintro; constructor <;> word
    | ok e' =>
      wp_auto
      wp_for_post
      iapply HΦ; iexact Hai
  iapply HΦ; iexact Hai

end proof

end EtcdGrove
end Perennial
