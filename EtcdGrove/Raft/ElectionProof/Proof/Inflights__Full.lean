/-
Port of `election_proof/proof_Inflights__Full.v`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.Inflights__Full

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Re-seal the raw predicate the proof opened. -/
private theorem ownInflights_reseal (l : Loc) (iv : tracker.Inflights)
    (buf : List tracker.inflight) (Hinfl_ok : InflightsOk iv (buf.length : Int)) :
    ⊢ (l ↦ iv : IProp GF) -∗ iv.buffer' ↦* buf -∗
      ownSliceCap tracker.inflight iv.buffer' (DFrac.own 1) -∗
      ownInflights l (inflightsAbs iv) := by
  iintro Hiv Hbuf Hbuf_cap
  iapply ownInflights_intro l iv buf
  unfold ownInflightsRaw
  simp only [named]
  iframe Hiv Hbuf Hbuf_cap
  ipureintro
  exact Hinfl_ok

theorem tracker.Inflights.Full.wp_proof : tracker.Inflights.Full.spec (GF := GF) (hG := hG) := by
  intro l i
  wp_start as Hin
  iNamed Hin
  iNamed Hin
  iNamed Hin
  wp_auto
  subst Hiabs
  rw [inflightsFull_abs]
  wp_if_destruct
  · -- count = size: the answer is `true || _`
    iapply HΦ
    iapply ownInflights_reseal l iv buf Hinfl_ok $$ Hiv Hbuf Hbuf_cap
  · -- The program tests `maxBytes == 0` (negated), the postcondition `maxBytes ≠ 0`.
    wp_if_destruct
    · -- maxBytes = 0: the byte test is skipped
      rw [show (false || decide (iv.maxBytes' ≠ W64 0) &&
          decide (uint.Z iv.maxBytes' ≤ uint.Z iv.bytes')) = false by simp [Hif]]
      iapply HΦ
      iapply ownInflights_reseal l iv buf Hinfl_ok $$ Hiv Hbuf Hbuf_cap
    · -- maxBytes ≠ 0: the byte comparison decides
      rw [show (false || decide (iv.maxBytes' ≠ W64 0) &&
          decide (uint.Z iv.maxBytes' ≤ uint.Z iv.bytes')) =
          decide (uint.Z iv.maxBytes' ≤ uint.Z iv.bytes') by
        rw [decide_eq_true Hif]; rfl]
      iapply HΦ
      iapply ownInflights_reseal l iv buf Hinfl_ok $$ Hiv Hbuf Hbuf_cap

end proof

end EtcdGrove
end Perennial
