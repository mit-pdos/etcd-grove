/-
Port of election_proof/proof_matchAckIndexer__AckedIndex.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.matchAckIndexer__AckedIndex

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

/-- `prs` and `pvs` have the same domain (`[∗map]` of two maps), so the lookup
hits exactly when `pvsAcked pvs id` is `some`. -/
theorem tracker.matchAckIndexer.AckedIndex.wp_proof :
    tracker.matchAckIndexer.AckedIndex.spec (GF := GF) (hG := hG) := by
  intro mref prs pvs id
  wp_start as Hm
  iNamed Hm
  wp_auto
  wp_apply wp_map_lookup2 $$ Hprs as -
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  have Hacked : pvsAcked pvs id = (pvs !! id).map Progress.matched := rfl
  rw [Hacked]
  cases Hpr : prs !! id with
  | some pr =>
    obtain ⟨p, Hp⟩ := Option.isSome_iff_exists.1
      ((Hiff id).1 (by show (prs !! id).isSome = true; rw [Hpr]; rfl))
    icases BigSepM2.bigSepM2_lookup_acc (Φ := fun _ pr p => ownProgress (GF := GF) pr p)
      (m1 := prs) (m2 := pvs) Hpr Hp $$ Hprogs with ⟨Hp, Hback⟩
    iNamed Hp
    have Hm := ((progressAbs_Some _ _ _).1 Habs).2.2.1
    rw [show (pvs !! id) = some p from Hp]
    simp only [Option.isSome_some, Option.map_some, Option.getD_some]
    wp_auto
    rw [Hm]
    ihave Hprogs := Hback $$ [Hpv Hinfl]
    · unfold ownProgress
      iexists _
      iframe Hpv Hinfl
      ipureintro; exact Habs
    iapply HΦ
    unfold ownProgressMap
    iframe Hprs Hprogs
  | none =>
    have Hv : pvs !! id = none := by
      cases Hv : pvs !! id with
      | none => rfl
      | some _ =>
        have := (Hiff id).2 (by show (pvs !! id).isSome = true; rw [Hv]; rfl)
        rw [show (Iris.Std.get? prs id) = prs !! id from rfl, Hpr] at this
        cases this
    rw [Hv]
    simp only [Option.isSome_none, Option.map_none, Option.getD_none]
    wp_auto
    iapply HΦ
    unfold ownProgressMap
    iframe Hprs Hprogs

end proof

end EtcdGrove
end Perennial
