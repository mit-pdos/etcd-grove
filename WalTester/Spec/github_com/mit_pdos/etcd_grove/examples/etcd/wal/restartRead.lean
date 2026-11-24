/-
`restartRead(lg, walDir, m)` (wal.go) over `fsExt` (W4c U5), for a non-nil member `m` whose oracle `o`'s
candidate `cd` accounts for the WAL state `od`, if there is one (`tCandOk`), and whose relation to the WAL
the restart takes is `tRelW` (created, `cd`'s mark synced and the WAL named; or fresh up to its opens:
`Boot`'s restart after a crash between `Create` and the store of `created`, B1): `ValidSnapshotEntries`, the
newest valid pair `(idx, term)`, then at most two attempts (`Repair` once between them), each storing the
oracle with `idx` appended to its opens (`storeOracle`; the open raises `d.unl` within the new opens bound,
`tCandOk_open`) before `Open`, then `ReadAll`; a failed `ReadAll` is followed by `Close` (`Close.spec` (state `failed`))
and `Repair`. Every update leaves `d`'s history and read position as they are.

The post, whatever the result: the oracle `tWithOpens o l` (at most two opens appended) stored and the
program's halves of the ghost state at it and at the WAL state `od'` (`od` with `unl` raised), still accounted
for by `cd`. On `readOK` (0): the WAL is there (`od = some d`), and the read `c`, which an image `img` of `cd`'s
history, the WAL's model, reads from
the purged prefix 0 (`tRead img = some c`); the open handle and the WAL's facts `ReadAll` gives; `Open`'s half
of the call permission. On a failure: nothing more (the member is down).

Premises: `m` is not nil (`restartRead`'s `if m != nil`; the caller allocated it); the paths are the
area's (`tWalPathsOk`); the history `ReadAll` reads reads back
(`tReadsBackOk`, W4b's `walReadsBack` where `ReadAll` succeeds; `tCandOk_readsBack`); the oracle has room for two opens (16 bytes below `tOrSmall`'s bound,
`tEncodeOracle_withOpens_length`). Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Member
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RestartOk
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Pb
public import Spec.go_uber_org.zap.Defs

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
abbrev restartRead.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (lg m : Loc) (v : oracle) (o : TOracle) (cd : TCand)
    (od : Option WalDur) (qp : Qp),
  m ≠ null → e.orFile.Ok → tWalPathsOk e.area → PathFits (tWalDir e.area) →
  cd ∈ o.cands → (∀ d, od = some d → tCandOk o cd d) →
  (tCandHist o cd).length < 2 ^ 63 → (∀ d, od = some d → tReadsBackOk (d.H.map WalOpG.toM)) →
  (tEncodeOracle o).length + 16 ≤ 0x40000000 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) e.R ∗ TInv (W := W) e γ ∗
      DurFs.durInv (GF := GF) γ.γd e.orFile ∗ DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗
      tPerm (GF := GF) e 1 ∗ zapLoggerOk lg ∗
      WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (e.area) ∗
      osPathS (GF := GF) e.R (e.area) (DFrac.own qp) e.jr ∗ WalFs.walAreaRes (W := W) e.jr ∗
      WalFs.walUnlockedTok (W := W) ∗
      m.[member, go!"orPath"] ↦ tOrPath e.orDir ∗ m.[member, go!"o"] ↦ v ∗
      oracleRep v o ∗ tOrOwn γ o none ∗ tWalOwn γ od ∗ tRelW (W := W) e.area o cd }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.restartRead)) (Val #lg))
      (Val #(tWalDir e.area))) (Val #m))
  {{ (st : w64) (vc : contents) (w : Loc), RET (PairV (PairV #st #vc) #w);
      DurFs.durHandle (GF := GF) γ.γd e.orFile e.R ∗
      osPathS (GF := GF) e.R (e.area) (DFrac.own qp) e.jr ∗ WalFs.walAreaRes (W := W) e.jr ∗
      m.[member, go!"orPath"] ↦ tOrPath e.orDir ∗
      ∃ (v' : oracle) (l : List w64) (od' : Option WalDur), m.[member, go!"o"] ↦ v' ∗
      oracleRep v' (tWithOpens o l) ∗ tOrOwn γ (tWithOpens o l) none ∗ tWalOwn γ od' ∗
      ⌜l.length ≤ 2 ∧ Option.Rel (fun d d' => d'.H = d.H ∧ d'.cut = d.cut ∧
        tCandOk (tWithOpens o l) cd d') od od'⌝ ∗
      if st = W64 0 then
        tPerm (GF := GF) e (1 : Qp).half ∗ ∃ (c : TContents) (d : WalDur), ⌜od = some d⌝ ∗
        contentsRep vc c ∗
        ⌜∃ img ∈ tImgs (tCandHist o cd) (tCandMark o cd), d.H.map WalOpG.toM = img.map absOp ∧
          tRead img = some c⌝ ∗
        walOpenWF (W := W) (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) ∗
        WalFs.walPurgeW (W := W) w (tWalDir e.area) ∗ WalFs.walLenLb (W := W) w (tWalDir e.area) d.H.length ∗
        WalFs.walSyncedLb (W := W) (tWalDir e.area) d.H.length ∗ WalFs.walNamed (W := W) (tWalDir e.area)
      else True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
