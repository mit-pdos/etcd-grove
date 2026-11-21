/- The two endpoint checks on the immutable runs of a Ready. -/
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

theorem replayTerms.covers.wp_proof : replayTerms.covers.spec (GF := GF) (hG := hG) := by
  intro r runs index
  wp_start as #Hr
  ihave %hlen := ownSlice_len r _ runs $$ Hr
  cases runs with
  | nil =>
    have hz : ¬ sint.Z (W64 0) < sint.Z r.len := by simp only [List.length_nil] at hlen; word
    (try wp_auto)
    iterate 4 (try simp only [hz, decide_false, Bool.false_eq_true, intoVal_eq_iff, ↓reduceIte]; try wp_auto)
    rw [show replayRunCovers [] index = false from rfl]
    iapply HΦ; itrivial
  | cons first tail =>
    have hpos : 0 < sint.Z r.len := by simp only [List.length_cons] at hlen; word
    have hfirst : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z r.len := ⟨by decide, hpos⟩
    icases ownSlice_elem_acc (sint.Z (W64 0)) first r DFrac.discard (first :: tail) (by decide) rfl $$ Hr
      with ⟨#Hfirst, -⟩
    iStructNamed Hfirst
    have hlast : 0 ≤ sint.Z (r.len - W64 1) ∧ sint.Z (r.len - W64 1) < sint.Z r.len := by constructor <;> word
    let last := (first :: tail).getLast (List.cons_ne_nil _ _)
    have he : (first :: tail).getLast? = some last := List.getLast?_eq_some_getLast _
    have hi : sint.nat (r.len - W64 1) = (first :: tail).length - 1 := by word
    have hget : (first :: tail)[sint.nat (r.len - W64 1)]? = some last := by
      rw [hi, ← List.getLast?_eq_getElem?]; exact he
    icases ownSlice_elem_acc (sint.Z (r.len - W64 1)) last r DFrac.discard (first :: tail) hlast.1 hget $$ Hr
      with ⟨#Hlast, -⟩
    iStructNamed Hlast
    by_cases hlo : uint.Z first.first' ≤ uint.Z index <;> by_cases hhi : uint.Z index ≤ uint.Z last.last'
    all_goals
      iterate 5 (try wp_auto; try simp only [hpos, hfirst, hlast, hlo, hhi, _root_.and_self, _root_.false_and, _root_.and_false,
                       intoVal_eq_iff, Bool.false_eq_true, decide_false, _root_.decide_true, ↓reduceIte])
      have hout : replayRunCovers (first :: tail) index = decide (uint.Z first.first' ≤ uint.Z index ∧ uint.Z index ≤ uint.Z last.last') := by simp [replayRunCovers, he]
      rw [hout]
      simp only [hlo, hhi, _root_.and_self, _root_.and_true, _root_.and_false, _root_.false_and, decide_false, _root_.decide_true]
      iapply HΦ; itrivial

end EtcdGrove
end Perennial
