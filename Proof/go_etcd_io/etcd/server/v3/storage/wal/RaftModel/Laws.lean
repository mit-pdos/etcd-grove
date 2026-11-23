/-
**The raftpb instance's laws, bundled** (W4c U4 b of `notes/wal-fsext-w4c-plan.md`, "W4c U4 log"): the
model premises the WAL's Link results take (`h_WalPbIn_*`, `h_U_*`, ...), discharged for the instance
`walRaftP`/`walRaftMr`/`walRaftU`/`walRaftHsO` over the part's `proto.Marshal`/`proto.Unmarshal`
trust-boundary specs (copies of the main tree's axioms, `proto.MarshalPb.wp_proof`,
`proto.UnmarshalPb.wp_proof`, and since fix 0009 `proto.SizePb.wp_proof`):

- `walPb_laws : WalPbLaws walRaftP walRaftMr walRaftU`, every law but four;
- `walRaftHsO_own`: `WalHsOwn`, its `unmarshal` over `proto.Unmarshal`'s spec at the registered
  `raftpb.HardState` (`LawsHsPb.lean`), its `reset` over the trusted model `HardState.Reset.impl`
  (`LawsHs.lean`, 2026-11-22).

Every raftpb law is proved (`WalPbIn.MarshalHsLaw` since wal-item3, 2026-11-21, `LawsHsMarshal.lean`;
`WalPbIn.CloneHsLaw` and `WalHsOwn.unmarshal` since 2026-11-22, `LawsHsPb.lean`, over the registered
`raftpb.HardState`, `PbHardState.lean`; `WalHsOwn.reset` since 2026-11-22, over `TrustedCode/go_etcd_io/raft/v3/
raftpb.lean`'s `HardState.Reset.impl`) (`notes/wal-fsext-plan.md`, §10).
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.LawsHs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.LawsEnt
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.LawsHsPb
public import Proof.google_golang_org.protobuf.proto.MarshalPb
public import Proof.google_golang_org.protobuf.proto.UnmarshalPb
public import Proof.google_golang_org.protobuf.proto.SizePb

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
  size : WalPbIn.SizeLaw P Mr
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
  size := walRaftP_size proto.SizePb.wp_proof
  unmarshalEnt := walRaftP_unmarshalEnt proto.UnmarshalPb.wp_proof
  uOk := walRaftU_ok
  snapCoh := walRaftU_snapCoh
  createOk := walRaftMr_createOk
  encState := walRaftMr_encState_lt

/-- **The hard states `ReadAll` owns**, over `proto.Unmarshal`'s spec (and, for `reset`, the trusted model
`HardState.Reset.impl`: `walRaftHsO_reset`). -/
theorem walRaftHsO_own (wp_Unmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG)) :
    WalHsOwn (walRaftP (GF := GF)) walRaftU walRaftHsO where
  zero := walRaftHsO_zero
  unmarshal := walRaftHsO_unmarshal wp_Unmarshal
  getCommit := walRaftHsO_getCommit
  reset := walRaftHsO_reset
  freeze := walRaftHsO_freeze
  notNull := walRaftHsO_notNull

end laws

end EtcdGrove
end Perennial
