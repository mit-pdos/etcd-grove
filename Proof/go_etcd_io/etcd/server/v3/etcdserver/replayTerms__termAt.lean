/- The loop stops at the first run whose last index covers the requested index. -/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.replayTerms__termAt

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem replayTerms.termAt.wp_proof : replayTerms.termAt.spec (GF := GF) (hG := hG) := by
  intro r runs index j run hrun hlast hbefore
  wp_start as #Hr
  ihave %hlen := ownSlice_len r _ runs $$ Hr
  have hj := (List.getElem?_eq_some_iff.1 hrun).1
  (try wp_auto)
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "%hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ j⌝ : IProp GF) $$ [i]
  · iexists W64 0; iframe; ipureintro; exact ⟨by decide, Nat.zero_le _⟩
  wp_for HI
  have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z r.len := by
    obtain ⟨h0, h1⟩ := hi; constructor <;> word
  obtain ⟨cur, hcur⟩ : ∃ cur, runs[sint.nat i]? = some cur :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases ownSlice_elem_acc (sint.Z i) cur r DFrac.discard runs hi.1 hcur $$ Hr with ⟨#Hcur, -⟩
  iStructNamed Hcur
  (try wp_auto)
  simp only [hb, ↓reduceIte]
  (try wp_auto)
  by_cases hij : sint.nat i < j
  · have he := hbefore _ hij _ hcur
    have hc : uint.Z cur.last' < uint.Z index := by word
    simp only [hc, _root_.decide_true, ↓reduceIte]
    wp_auto
    wp_for_post
    iframe
    iexists i + W64 1
    iframe
    ipureintro
    constructor <;> word
  · have he : sint.nat i = j := by omega
    rw [he, hrun] at hcur
    cases hcur
    have hc : ¬ uint.Z run.last' < uint.Z index := by word
    simp only [hc, decide_false, intoVal_eq_iff, Bool.false_eq_true, _root_.decide_true, ↓reduceIte]
    (try wp_auto)
    (try simp only [hb, ↓reduceIte])
    (try wp_auto)
    iapply HΦ
    itrivial

end EtcdGrove
end Perennial
