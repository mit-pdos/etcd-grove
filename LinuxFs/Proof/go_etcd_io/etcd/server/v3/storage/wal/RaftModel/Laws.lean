/-
**The raftpb instance's laws, bundled** (W4c U4 b of `notes/wal-fsext-w4c-plan.md`, "W4c U4 log"): the
model premises the WAL's Link results take (`h_WalPbIn_*`, `h_U_*`, ...), discharged for the instance
`walRaftP`/`walRaftMr`/`walRaftU`/`walRaftHsO` over the part's `proto.Marshal`/`proto.Unmarshal`
trust-boundary specs (copies of the main tree's axioms, `proto.MarshalPb.wp_proof`,
`proto.UnmarshalPb.wp_proof`):

- `walPb_laws : WalPbLaws walRaftP walRaftMr walRaftU`, every law but four;
- `walRaftHsO_own`: `WalHsOwn` from its two fields that need `raftpb.HardState`'s trusted model
  (`unmarshal`, `reset`).

`WalPbIn.MarshalHsLaw`, `WalPbIn.CloneHsLaw`, `WalHsOwn.unmarshal` and `WalHsOwn.reset` stay hypotheses
of the closed result (`notes/wal-fsext-plan.md`, §10, "The raftpb instance's laws pending the user").
Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.LawsHs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.LawsEnt
public import LinuxFs.Proof.google_golang_org.protobuf.proto.MarshalPb
public import LinuxFs.Proof.google_golang_org.protobuf.proto.UnmarshalPb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 WalEnc WalFs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **The model laws of a client's raft messages and codec** the WAL's results take (but
`MarshalHsLaw`, `CloneHsLaw` and `WalHsOwn`). -/
structure WalPbLaws (P : WalPbIn GF) (Mr : WalMarshal) (U : WalUnmarshal) : Prop where
  nil : WalPbIn.NilLaw P
  zero : WalPbIn.ZeroLaw P
  mustSync : WalPbIn.MustSyncLaw P
  isEmpty : WalPbIn.IsEmptyLaw P
  getIndex : WalPbIn.GetIndexLaw P
  getTerm : WalPbIn.GetTermLaw P
  marshalEnt : WalPbIn.MarshalEntLaw P Mr
  unmarshalEnt : WalPbIn.UnmarshalEntLaw P U
  uOk : U.Ok Mr
  snapCoh : U.SnapCoh
  createOk : WalMarshalCreateOk Mr
  encState : ∀ hs, (Mr.encState hs).length < 2 ^ 32

/-- **The raftpb instance's laws.** -/
theorem walPb_laws : WalPbLaws (walRaftP (GF := GF)) walRaftMr walRaftU where
  nil := walRaftP_nil
  zero := walRaftP_zero
  mustSync := walRaftP_mustSync
  isEmpty := walRaftP_isEmpty
  getIndex := walRaftP_getIndex
  getTerm := walRaftP_getTerm
  marshalEnt := walRaftP_marshalEnt proto.MarshalPb.wp_proof
  unmarshalEnt := walRaftP_unmarshalEnt proto.UnmarshalPb.wp_proof
  uOk := walRaftU_ok
  snapCoh := walRaftU_snapCoh
  createOk := walRaftMr_createOk
  encState := walRaftMr_encState_lt

/-- **The hard states `ReadAll` owns**, from the two laws that need `raftpb.HardState`'s trusted model. -/
theorem walRaftHsO_own
    (h_unmarshal : ∀ (d : GoSlice) (dq : DFrac) (bs : List w8) (h : HardStateM),
      walRaftU.decState bs = some h →
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ d ↦*{dq} bs }}
        (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.MustUnmarshalState)) (Val #d))
      {{ (p : Loc), RET #p; d ↦*{dq} bs ∗ walRaftHsO p h }})
    (h_reset : ∀ (p : Loc) (h : HardStateM),
      {{ walRaftHsO (GF := GF) p h }}
        (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.raftpb.HardState.ty @!! go!"Reset"))
          (Val #()))
      {{ RET #(); walRaftHsO p hsZero }}) :
    WalHsOwn (walRaftP (GF := GF)) walRaftU walRaftHsO where
  zero := walRaftHsO_zero
  unmarshal := h_unmarshal
  getCommit := walRaftHsO_getCommit
  reset := h_reset
  freeze := walRaftHsO_freeze

end laws

end EtcdGrove
end Perennial
