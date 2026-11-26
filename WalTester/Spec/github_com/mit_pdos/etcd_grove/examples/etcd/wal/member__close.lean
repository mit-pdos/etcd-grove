/-
`(*member).close()` (wal.go) over `fsExt` (W4c U5): `w.Close()` on the member's open WAL (its update
committed on the tester's invariant, the WAL state `d` unchanged), `m.w = nil`, then, on success, the
oracle's mark moved to the end of `since` (`tSynced`) and stored (`storeOracle`, with `tRelI` from
`Close`'s `walSyncedLb` at the whole history). `true`: the synced oracle, the WAL closed (the lock token
and `Close`'s half of the call permission back, the history synced). `false`: the oracle unchanged (the WAL state's
half lost with `Close`'s update: a failed `Close` may not have committed it). Touches the
member's fields `orPath`, `w`, `o`. The client's call permission `qc` (for `storeOracle`) as in
`member.sync.spec`. Lean-first (no Rocq counterpart).
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
abbrev member.close.spec : Prop :=
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
      WalFs.walPurgeW (W := W) w (tWalDir e.area) ∗ WalFs.walNamed (W := W) (tWalDir e.area) 0 }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"close")) (Val #()))
  {{ (b : Bool), RET #b; DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗ tPerm (GF := GF) e qc ∗
      m.[member, go!"orPath"] ↦ tOrPath e.orDir ∗ m.[member, go!"w"] ↦ (null : Loc) ∗ ∃ v' : oracle,
      m.[member, go!"o"] ↦ v' ∗
      if b then oracleRep v' (tSynced o) ∗ tOrOwn γ (tSynced o) none ∗ tWalOwn γ (some d) ∗
        WalFs.walUnlockedTok (W := W) ∗ osCallPerm (GF := GF) (callKey e.R (tWalDir e.area)) (1 : Qp).half ∗
        WalFs.walSyncedLb (W := W) (tWalDir e.area) 0 d.H.length
      else oracleRep v' o ∗ tOrOwn γ os none }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
