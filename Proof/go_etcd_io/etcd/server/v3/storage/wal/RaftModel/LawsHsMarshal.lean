/-
**`MarshalHsLaw` of the server's (and the raftpb) instance** (wal-fsfix2 item 3): `pbutil.MustMarshalMessage`
of a non-empty hard state, over `proto.Marshal`'s trust-boundary spec at the registered `raftpb.HardState`
(`pbHsC`, `RaftModel/PbHardState.lean`): the instance's hard states are frozen at the canonical content
(`walHsIn`), whose encoding `hsEnc (walHsCanon h)` is the marshaller's `encState`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Srv
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.PbHardState
public import Spec.google_golang_org.protobuf.proto.MarshalPb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 WalEnc WalFs

/-- A non-empty hard state's canonical encoding is not empty. -/
theorem walHsCanon_enc_pos [GooseExts] (h : HardStateM) (hne : ¬ hsEmptyP h) :
    0 < (hsEnc (walHsCanon h)).length := by
  unfold walHsCanon
  rw [if_neg hne]
  obtain ⟨x, t, hx⟩ := varintEnc_cons (1 * 8)
  simp only [hsEnc, Option.map_some, optVarintField, hx, List.length_append, List.length_cons]
  omega

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **`MarshalHsLaw`** of the raftpb instance, over `proto.Marshal`'s trust-boundary spec at the
registered `raftpb.HardState`. -/
theorem walRaftP_marshalHs (wp_Marshal : proto.MarshalPb.spec (GF := GF) (hG := hG)) :
    WalPbIn.MarshalHsLaw (walRaftP (GF := GF)) walRaftMr := by
  intro hp hs hne
  simp only [walRaftP]
  wp_start as #Hh
  unfold walHsIn
  icases Hh with (%Hn | ⟨%c, #Hro, %Hc⟩)
  · exfalso; apply hne; rw [Hn.2]; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨-, hcan⟩ := Hc
  have hc : c = walHsCanon hs := hcan.resolve_left hne
  subst hc
  have hlen := walHsCanon_enc_len hs
  have hpos := walHsCanon_enc_pos hs hne
  wp_auto
  have wpM := wp_Marshal pbHsC pbHsC_reg hp (walHsCanon hs) trivial
    (by simp only [pbHsC_size, hsSize]; omega)
  simp only [pbHsC_ty, pbHsC_roC, pbEncC_pbHsC] at wpM
  wp_apply wpM $$ [] as %d ⟨Hd, Hcap⟩
  · iframe #
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hd
  iapply HΦ
  simp only [walRaftMr]
  iframe
  ipureintro
  rintro rfl
  rw [Hlen.1] at hpos
  simp [slice.nil] at hpos

/-- **`MarshalHsLaw`** of the server's instance (its hard states and state codec are the raftpb
instance's). -/
theorem walSrvP_marshalHs (wp_Marshal : proto.MarshalPb.spec (GF := GF) (hG := hG)) :
    WalPbIn.MarshalHsLaw (walSrvP (GF := GF)) walSrvMr :=
  walRaftP_marshalHs wp_Marshal

end laws

end EtcdGrove
end Perennial
