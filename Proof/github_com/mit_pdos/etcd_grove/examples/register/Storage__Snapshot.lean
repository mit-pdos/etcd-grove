/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Storage__Snapshot.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Storage__Snapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem Storage.Snapshot.wp_proof
    (wp_MemoryStorage_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG)) :
    Storage.Snapshot.spec (GF := GF) (hG := hG) := by
  intro s ms γs σ esu
  wp_start as ⟨#Hms, Hown, #Hesu⟩
  wp_auto
  wp_apply wp_MemoryStorage_Snapshot ms γs σ esu $$ [$Hown $Hesu] as %snap %err ⟨Hown, Hr⟩
  cases err with
  | nil =>
    wp_auto
    wp_if_destruct
    · -- an empty snapshot: `ErrSnapshotTemporarilyUnavailable`
      iapply HΦ
      iframe Hown
      ileft; ipureintro; rfl
    · iapply HΦ
      iframe Hown
      icases Hr with (%Herr | ⟨%Herr, Hv⟩)
      · ileft; ipureintro; exact Herr
      · iright; iframe Hv; ipureintro; exact ⟨rfl, Herr.2, Hif⟩
  | ok i =>
    wp_auto
    iapply HΦ
    iframe Hown
    icases Hr with (%Herr | ⟨%Herr, -⟩)
    · ileft; ipureintro; exact Herr
    · exact absurd Herr.1 (by simp)

end proof

end register
end EtcdGrove
end Perennial
