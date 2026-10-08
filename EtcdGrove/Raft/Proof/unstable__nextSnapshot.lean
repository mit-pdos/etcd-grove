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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem unstable.nextSnapshot.wp_proof : unstable.nextSnapshot.spec (GF := GF) (hG := hG) := by
  intro u uv uents snap
  wp_start as H
  iNamed H
  iunfold ownUnstable at Hun
  iNamed Hun
  wp_auto
  cases snap with
  | some sid =>
    icases (ownSnap_Some _ _).1 $$ Hsnap with ⟨%sv, #Hsv, -⟩
    ihave %Hnn := typedPointsto_not_null $$ Hsv
    simp only [Hnn, _root_.decide_false]
    wp_auto
    rcases Hsip : uv.snapshotInProgress' <;> wp_auto <;>
    · iapply HΦ
      unfold ownUnstable
      iframe
      ipureintro
      intro h
      cases h
  | none =>
    icases (ownSnap_None _).1 $$ Hsnap with %Hn
    simp only [Hn, _root_.decide_true]
    wp_auto
    iapply HΦ
    unfold ownUnstable
    iframe
    ipureintro
    intro _
    rfl

end proof

end EtcdGrove
end Perennial
