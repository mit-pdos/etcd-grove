/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/NewInmemSnapshotStore.lean (241f27e).
-/
/-
The proof of `raft.NewInmemSnapshotStore`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.NewInmemSnapshotStore

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft

theorem github_com.hashicorp.raft.NewInmemSnapshotStore.wp_proof :
    github_com.hashicorp.raft.NewInmemSnapshotStore.spec (GF := GF) (hG := hG) := by
  intro hb
  wp_start
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hs
  generalize «$r0_ptr» = m at *
  iStructNamed Hs
  imod sync.init_RWMutex_qpool (snapInv m) (E := ⊤) snapPoolN (m.[InmemSnapshotStore, go!"RWMutex"])
    (ThreadBoundLe.le _) $$ [hasSnapshot] RWMutex with ⟨%γp, #Hguard, #Hpool⟩
  · inext; iapply (snapInv_unfold m 1).mpr; iexact hasSnapshot
  imodintro
  iapply HΦ
  unfold isInmemSnapshotStore
  iframe #
  iexists γp
  iframe #

end proof

end Perennial
