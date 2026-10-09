/-
Port of `election_proof/proof_unstable__nextSnapshot.v` (857d09190).
-/
module

public import Spec.go_etcd_io.raft.v3.unstable__nextSnapshot

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

theorem unstable.nextSnapshot.wp_proof : unstable.nextSnapshot.spec (GF := GF) (hG := hG) := by
  intro u us
  wp_start as H
  iNamed H
  open_unstable
  wp_auto
  rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
  · icases ownSnap_of_eq_some Hs $$ Hsnap with ⟨%sv, #Hsv, -⟩
    ihave %Hnn := typedPointsto_not_null $$ Hsv
    simp only [Hnn, _root_.decide_false]
    wp_auto
    rcases Hsip : uv.snapshotInProgress' <;> wp_auto <;>
    · iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      rw [Hs]
      intro h
      cases h
  · ihave %Hn := ownSnap_of_eq_none Hs $$ Hsnap
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
