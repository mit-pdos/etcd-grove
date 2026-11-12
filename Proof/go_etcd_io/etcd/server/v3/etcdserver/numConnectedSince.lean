/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/numConnectedSince.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.numConnectedSince
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.isConnectedSince

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem numConnectedSince.wp_proof
    (hC : isConnectedSince.spec (GF := GF) (hG := hG)) :
    numConnectedSince.spec (GF := GF) (hG := hG) := by
  intro tr since self members ms
  wp_start as ⟨#Htr, Hms⟩
  iunfold membership.membersAt at Hms
  icases Hms with ⟨Hsl, Hown⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (n cnt : w64) (x : Loc),
      "i" ∷ i_ptr ↦ n ∗ "connectedNum" ∷ connectedNum_ptr ↦ cnt ∗ "m" ∷ m_ptr ↦ x ∗
      "Hsl" ∷ members ↦* ms ∗ "Hown" ∷ ([∗list] m ∈ ms, membership.ownMember m) ∗
      "self" ∷ self_ptr ↦ self ∗ "since" ∷ since_ptr ↦ since ∗ "transport" ∷ transport_ptr ↦ tr ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ms.length : Int)⌝) $$ [i connectedNum m Hsl Hown self since transport]
  · iexists W64 0, W64 0, zero_val Loc
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ms.length := by word
    obtain ⟨m0, Hm0⟩ : ∃ m0, ms[sint.nat n]? = some m0 := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z members.len := ⟨Hn.1, Hif⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index members (sint.Z n) ms (DFrac.own 1) m0 Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hm0
    icases (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
      (Φ := fun (_ : Nat) (y : Loc) => membership.ownMember (GF := GF) y) Hm0).1 $$ Hown
      with ⟨Hm, Hclose⟩
    iunfold membership.ownMember at Hm
    icases Hm with ⟨%id, Hm⟩
    icases membership.memberIs_id_acc m0 id $$ Hm with ⟨Hid, Hback⟩
    have hs : ms.set (sint.nat n) m0 = ms := by
      apply List.ext_getElem?
      intro k
      rw [List.getElem?_set]
      split
      · rename_i hk; subst hk; rw [Hm0]; try simp [Hlt]
      · rfl
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      ihave Hm := Hback $$ Hid
      ihave Hown := Hclose $$ [Hm]
      · iunfold membership.ownMember; iexists id; iexact Hm
      rw [hs]
      wp_for_post
      iframe
      iexists n + W64 1, cnt + W64 1, m0
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    · (try wp_auto)
      ihave Hm := Hback $$ Hid
      ihave Hown := Hclose $$ [Hm]
      · iunfold membership.ownMember; iexists id; iexact Hm
      rw [hs]
      wp_apply hC tr since id $$ [] as %b -
      · iframe #
      cases b
      · (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, cnt, m0
        simp only [named]
        iframe
        ipureintro; constructor <;> word
      · (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, cnt + W64 1, m0
        simp only [named]
        iframe
        ipureintro; constructor <;> word
  · iapply HΦ
    iunfold membership.membersAt
    iframe

end proof

end EtcdGrove
end Perennial
