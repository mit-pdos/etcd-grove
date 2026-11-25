/-
`(*member).sync()` (wal.go) over `fsExt` (W4c U5): `w.Sync()` on the member's open WAL (`walOpenWF`,
whose state `d` is candidate `c`'s whole history, `tMemOk`), then the oracle's mark moved to the end of
`since` (`tSynced`) and stored (`storeOracle`, with `tRelI` re-established from `Sync`'s `walSyncedLb`).
`true`: the member as before with the synced oracle. `false` (`Sync` failed, the handle lost): the
oracle unchanged. Touches the member's fields `orPath`, `w`, `o`. The client's call permission `qc`
(for `storeOracle`) is the caller's: ledger 2026-11-14, "the client keeps no call permission while a
WAL is open". Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Member
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Pb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev member.sync.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (v : oracle) (o os : TOracle) (c : TCand) (d : WalDur)
    (qc : Qp),
  e.orFile.Ok → tMemOk o c d → tOrSmall (tSynced o) → tCheckWf o →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) e.R ∗ TInv (W := W) e γ ∗
      DurFs.durInv (GF := GF) γ.γd e.orFile ∗ DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗
      tPerm (GF := GF) e qc ∗
      m.[member, go!"orPath"] ↦ tOrPath e.orDir ∗ m.[member, go!"w"] ↦ w ∗ m.[member, go!"o"] ↦ v ∗
      oracleRep v o ∗ tOrOwn γ os none ∗ tWalOwn γ (some d) ∗
      WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (e.area) ∗
      walOpenWFI (W := W) (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) 0 ∗
      WalFs.walLenLb (W := W) w (tWalDir e.area) 0 d.H.length ∗ WalFs.walNamed (W := W) (tWalDir e.area) 0 }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"sync")) (Val #()))
  {{ (b : Bool), RET #b; DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗ tPerm (GF := GF) e qc ∗
      m.[member, go!"orPath"] ↦ tOrPath e.orDir ∗ m.[member, go!"w"] ↦ w ∗ ∃ v' : oracle,
      m.[member, go!"o"] ↦ v' ∗ tWalOwn γ (some d) ∗
      if b then oracleRep v' (tSynced o) ∗ tOrOwn γ (tSynced o) none ∗
        walOpenWFI (W := W) (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) 0 ∗
        WalFs.walLenLb (W := W) w (tWalDir e.area) 0 d.H.length ∗
        WalFs.walSyncedLb (W := W) (tWalDir e.area) 0 d.H.length
      else oracleRep v' o ∗ tOrOwn γ os none }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
