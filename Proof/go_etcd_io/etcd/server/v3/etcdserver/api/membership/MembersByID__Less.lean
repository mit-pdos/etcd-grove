/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/MembersByID__Less.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.MembersByID__Less

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

theorem membership.MembersByID.Less.wp_proof :
    membership.MembersByID.Less.spec (GF := GF) (hG := hG) := by
  intro sl l dq i j a b
  wp_start as ⟨Hs, Hms, %Hij⟩
  wp_auto
  obtain ⟨hi0, hj0, ha, hb⟩ := Hij
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_map] at Hl
  have hilt : sint.nat i < l.length := (List.getElem?_eq_some_iff.1 ha).1
  have hjlt : sint.nat j < l.length := (List.getElem?_eq_some_iff.1 hb).1
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by have := Hl.1; refine ⟨hi0, ?_⟩; word
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by have := Hl.1; refine ⟨hj0, ?_⟩; word
  simp only [Hbi, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z i) _ dq a.1 hi0 $$ [Hs] as Hs
  · iframe; ipureintro; rw [List.getElem?_map]; exact congrArg (Option.map Prod.fst) ha
  icases membership.membersL_acc l (sint.nat i) a ha $$ Hms with ⟨Ha, Hclose⟩
  icases membership.memberIs_id_acc a.1 a.2 $$ Ha with ⟨Hida, Hbacka⟩
  wp_auto
  ihave Ha := Hbacka $$ Hida
  ihave Hms := Hclose $$ Ha
  simp only [Hbj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z j) _ dq b.1 hj0 $$ [Hs] as Hs
  · iframe; ipureintro; rw [List.getElem?_map]; exact congrArg (Option.map Prod.fst) hb
  icases membership.membersL_acc l (sint.nat j) b hb $$ Hms with ⟨Hb, Hclose⟩
  icases membership.memberIs_id_acc b.1 b.2 $$ Hb with ⟨Hidb, Hbackb⟩
  wp_auto
  ihave Hb := Hbackb $$ Hidb
  ihave Hms := Hclose $$ Hb
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
