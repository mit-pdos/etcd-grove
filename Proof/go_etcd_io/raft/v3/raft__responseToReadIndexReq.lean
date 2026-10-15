/- Lean-first (no Rocq counterpart; 2026-10-12, read-index).

The local case reaches `r.readStates` through `ownRaftPhysC_misc`, reads `req.Entries[0].Data`
through the read-only entries, and appends the `ReadState`; the forwarded case builds the
response literal and touches nothing.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__responseToReadIndexReq

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- The local case, once the test is decided: `r.readStates` through `ownRaftPhysC_misc`,
`req.Entries[0].Data` through the read-only entries, the `ReadState` appended. -/
local macro "local_case" : tactic => `(tactic| (
  icases ownRaftPhysC_misc c r id s $$ Hphys with ⟨%rs, %ro, %pr, Hrs, Hro, Hpr, Hmisc, Hback⟩
  iunfold ownRaftMisc at Hmisc
  iNamed Hmisc
  ihave %Hlen := ownSlice_len _ _ _ $$ Hents
  wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z req.Entries'.len by
    obtain ⟨h1, h2⟩ := Hlen; simp only [List.length_cons] at h1; word)]
  icases ownSlice_elem_acc (sint.Z (W64 0)) e req.Entries' DFrac.discard (e :: es) (by decide)
    rfl $$ Hents with ⟨He, -⟩
  icases (AccessStrict.access_strict
      (A := (sliceIndexRef raftpb.Entry (sint.Z (W64 0)) req.Entries').[raftpb.Entry, go!"Data"]
        ↦□ e.Data')
      (A' := (sliceIndexRef raftpb.Entry (sint.Z (W64 0)) req.Entries').[raftpb.Entry, go!"Data"]
        ↦□ e.Data')
      (P := sliceIndexRef raftpb.Entry (sint.Z (W64 0)) req.Entries' ↦□ e)) $$ He with ⟨He, -⟩
  wp_auto
  wp_apply wp_slice_literal (V := ReadState) [ReadState.mk idx e.Data']
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_apply wp_slice_append_persistent (V := ReadState) _ _ _ _ _
      $$ [HreadStates HreadStates_cap Hsl]
    as %rs' ⟨HreadStates, HreadStates_cap, -⟩
  · iframe
  wp_auto
  iapply HΦ
  rw [ite_eq_left Hlocal]
  ihave Hphys := Hback $$ %rs' %ro %pr
    %({ s.rd with states := s.rd.states ++ [ReadState.mk idx e.Data'] }) Hrs Hro Hpr
    [HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]
  · unfold ownRaftMisc
    simp only [named]
    iframe HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap Hpri_ents
  ihave Hphys := ownRaftPhysC_eq c r id
    { s with rd := { s.rd with states := s.rd.states ++ [ReadState.mk idx e.Data'] } }
    (addReadState s idx e.Data') rfl $$ Hphys
  iframe Hphys
  ipureintro; rfl))

theorem raft.responseToReadIndexReq.wp_proof :
    raft.responseToReadIndexReq.spec (GF := GF) (hG := hG) := by
  intro c r id s req idx e es
  wp_start as Hpre
  iNamed Hpre
  wp_auto
  by_cases H0 : req.From' = W64 0
  · have Hlocal : req.From' = W64 0 ∨ req.From' = id := .inl H0
    rw [decide_eq_true H0]
    wp_auto
    local_case
  · rw [decide_eq_false H0]
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    by_cases Hid : req.From' = id
    · have Hlocal : req.From' = W64 0 ∨ req.From' = id := .inr Hid
      rw [decide_eq_true Hid]
      wp_auto
      local_case
    · rw [decide_eq_false Hid]
      wp_auto
      iapply HΦ
      rw [ite_eq_right (by rintro (h | h) <;> contradiction)]
      iframe Hphys
      ipureintro; rfl

end proof

end EtcdGrove
end Perennial
