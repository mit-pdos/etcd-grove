/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/newStorage.lean`. Lean-first (no
Rocq counterpart): `NewMemoryStorage`, then the empty image (a fresh empty snapshot, frozen
read-only) and the storage struct, split into its fields.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.newStorage
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem newStorage.wp_proof (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG)) :
    newStorage.spec (GF := GF) (hG := hG) := by
  intro bp
  wp_start as -
  wp_auto
  wp_apply +noauto wp_NewMemoryStorage as %ms %γs ⟨Hlock, Hlog, Hend, Hnone, Hmeta, Hfresh⟩
  iapply wp_fupd
  wp_auto
  imod ownSnapM_of_struct «$v0_ptr» (zero_val raftpb.Snapshot) memSnapEmpty ⊤ rfl $$ [«$v0»]
    with Hsn
  · iframe «$v0»
    isplitl []
    · simp only [memSnapEmpty]; iapply ownSlice_nil
    iunfold smOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
  imod ownSnapM_persist $$ Hsn with #Hsn
  iStructNamedPrefix «$v2» "I"
  iStructNamedPrefix «$r0» "S"
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Sboot with #Sboot
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Simg with #Simg
  imodintro
  iapply HΦ
  iexists ms, «$v2_ptr», γs
  iframe # ∗
  ihave #Hh := hsOpt_null (GF := GF)
  ihave #He := entsPts_nil (GF := GF) DFrac.discard
  iunfold ownImage
  iexists null, «$v0_ptr», slice.nil
  simp only [imgEmpty, named]
  iframe # ∗
  isplitl [Iprev]
  · rw [show W64 0 = (0 : w64) from rfl]; iexact Iprev
  isplitl [IprevTerm]
  · rw [show W64 0 = (0 : w64) from rfl]; iexact IprevTerm
  ipureintro; simp

end proof

end kvdurable
end EtcdGrove
end Perennial
