/-
Port of `election_proof/proof_unstable__nextSnapshot.v` (857d09190).
-/
import EtcdGrove.Raft.Spec.unstable__nextSnapshot

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

theorem unstable.nextSnapshot.wp_proof : unstable.nextSnapshot.spec (GF := GF) (hG := hG) := by
  intro u us
  obtain ⟨uents, off, ip, snap⟩ := us
  wp_start as H
  iNamed H
  open_unstable
  wp_auto
  cases snap with
  | some sid =>
    icases (ownSnap_Some _ _).1 $$ Hsnap with ⟨%sv, #Hsv, -⟩
    ihave %Hnn := typedPointsto_not_null $$ Hsv
    simp only [Hnn, _root_.decide_false]
    wp_auto
    rcases Hsip : uv.snapshotInProgress' <;> wp_auto <;>
    · iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      intro h
      cases h
  | none =>
    ihave %Hn := (ownSnap_None _).1 $$ Hsnap
    simp only [decide_eq_true Hn]
    wp_auto
    iapply HΦ
    isplitl
    · close_unstable
    ipureintro
    intro _
    rfl

end proof

end EtcdGrove
end Perennial
