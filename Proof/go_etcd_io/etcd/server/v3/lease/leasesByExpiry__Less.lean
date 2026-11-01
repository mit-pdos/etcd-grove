/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/leasesByExpiry__Less.lean`. Lean-first (no Rocq
counterpart); the lease-read plan (2026-10-31), as `MembersByID.Less`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.leasesByExpiry__Less
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Remaining

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.leasesByExpiry.Less.wp_proof
    (hRem : lease.Lease.Remaining.spec (GF := GF) (hG := hG)) :
    lease.leasesByExpiry.Less.spec (GF := GF) (hG := hG) := by
  intro γl sl ls dq i j a b
  wp_start as ⟨Hs, #Hls, Htt, %Hb, %Hij⟩
  wp_auto
  obtain ⟨hi0, hj0, ha, hb⟩ := Hij
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hilt : sint.nat i < ls.length := (List.getElem?_eq_some_iff.1 ha).1
  have hjlt : sint.nat j < ls.length := (List.getElem?_eq_some_iff.1 hb).1
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by have := Hl.1; refine ⟨hi0, ?_⟩; word
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by have := Hl.1; refine ⟨hj0, ?_⟩; word
  ihave #Ha := BigSepL.bigSepL_lookup (Φ := fun _ l => isLeaseObj (GF := GF) γl l) ha $$ Hls
  ihave #Hb' := BigSepL.bigSepL_lookup (Φ := fun _ l => isLeaseObj (GF := GF) γl l) hb $$ Hls
  try simp only [Hbi, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z i) _ dq a hi0 $$ [Hs] as Hs
  · iframe; ipureintro; exact ha
  wp_apply hRem γl a $$ [$Ha $Htt] as %di Htt
  · ipureintro; exact Hb
  (try wp_auto)
  try simp only [Hbj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z j) _ dq b hj0 $$ [Hs] as Hs
  · iframe; ipureintro; exact hb
  wp_apply hRem γl b $$ [$Hb' $Htt] as %dj Htt
  · ipureintro; exact Hb
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
