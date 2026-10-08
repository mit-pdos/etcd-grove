/- Port of election_proof/proof_raft__increaseUncommittedSize.v. -/
import EtcdGrove.Raft.Spec.raft__increaseUncommittedSize
import EtcdGrove.Raft.Spec.payloadsSize

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

set_option hygiene false in
/-- The fall-through: `uncommittedSize += s`, then `return true`. -/
local macro "incr" : tactic => `(tactic| (
  wp_apply raft.wp_load_uncommittedSize $$ Hphys as %u_inc Hphys
  wp_apply raft.wp_store_uncommittedSize $$ Hphys as Hphys
  iapply HΦ
  iframe
  ipureintro
  intro _; rfl))

theorem raft.increaseUncommittedSize.wp_proof
    (wp_payloadsSize : payloadsSize.spec (GF := GF) (hG := hG)) :
    raft.increaseUncommittedSize.spec (GF := GF) (hG := hG) := by
  intro cfg r id s es ents dq
  wp_start as H
  iNamed H
  wp_alloc r_ptr as r; wp_pures; wp_alloc ents_ptr as ents; wp_pures; wp_load; wp_pures; iclear ents
  -- `payloadsSize` pins the result only for an all-empty batch, as an implication --
  -- exactly the shape the postcondition passes on.
  wp_apply wp_payloadsSize $$ [$Hes] as %psz ⟨Hes, %Hpsz⟩
  wp_pures; wp_alloc s_ptr as s; wp_pures; wp_store; wp_pures; wp_load; wp_pures
  -- `&&` is a nest of `if`s over fields `ownRaftPhys` does not track; walk it. Every
  -- fall-through reaches the increment and `return true`.
  wp_apply raft.wp_load_uncommittedSize $$ Hphys as %u Hphys
  wp_pures
  wp_if_destruct
  · wp_load; wp_pures
    wp_if_destruct
    · wp_load; wp_pures
      wp_load; wp_pures; wp_load; wp_pures
      wp_apply raft.wp_load_uncommittedSize $$ Hphys as %u' Hphys
      wp_apply raft.wp_load_maxUncommittedSize $$ Hphys as %m Hphys
      wp_pures
      wp_if_destruct
      · -- the reject path: the payload is positive, so the batch is not all-empty
        iapply HΦ
        iframe
        ipureintro
        intro Hz
        rw [Hpsz Hz] at *
        word
      -- TODO(no-wp-auto): macro `incr` runs wp_auto: wp_load; wp_pures; iclear s | wp_pures
      · wp_load; wp_pures; wp_load; wp_pures; iclear r
        incr
    -- TODO(no-wp-auto): macro `incr` runs wp_auto: wp_load; wp_pures; iclear s | wp_pures
    · wp_load; wp_pures; wp_load; wp_pures; iclear r
      incr
  -- TODO(no-wp-auto): macro `incr` runs wp_auto: wp_load; wp_pures; iclear s | wp_pures
  · wp_load; wp_pures; wp_load; wp_pures; iclear r
    incr

end proof

end EtcdGrove
end Perennial
