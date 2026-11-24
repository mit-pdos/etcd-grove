/- Lean-first (no Rocq counterpart).

# The WAL tester (`examples/etcd/wal`): the definitions its top-level statement is written in

The tester's semantics (`tExtsSem`: the file system does not fail, `tSQ`, and a crash keeps no CRC
collision in the WAL's images, `tQ`), its boot program (`bootWal`), the first boot's facts (`tFirst`),
the specs its proof takes that no proof discharges yet (`TOpen`), moved here unchanged out of `Adequacy.lean`, and
the WAL's ghost state in the file extension's (`tAbsPre`, new), so that the statement (`WalTester/Spec/.../TopLevelRobustness.lean`) imports no
proof (CLAUDE.md, "Import tiers").
-/
module

public import GooseLang.Ext.Fs.Adequacy
public import GooseLang.Ext.Fs.AdequacyS
public import GooseLang.Ext.Fs.NoIoErr
public import GooseLang.Ext.Fs.NoMapLockErr
public import GooseLang.Ext.AbsDisk.Specs
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Inv
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RestartOk
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.W1
public import Spec.google_golang_org.protobuf.proto.UnmarshalWalRecordE
public import Robustness.Statement

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3 Fs WalEnc WalFs

attribute [local instance] fsExts fsExtsInterp

/-! ## The semantics -/

/-- **Every file and every path.** -/
def tIo : IoSet := ⟨fun _ _ => True, fun _ => True⟩

/-- **The file system does not fail** (the etcd examples' `etcdSQ`). -/
abbrev tSQ : StepPrem := StepPrem.and (NoIoErr tIo) (NoMapLockErr tIo)

/-- **A crash keeps no CRC collision in the WAL's images** (`W1`, `walInv_crash`'s premise). -/
def tQ : OsState → OsState → Prop := fun st st' => W1 walCodec st st'

/-- The file extension's semantics: steps restricted by `tSQ`, crashes by `tQ`. -/
@[reducible] def tFsSem : ExtSemantics fsExt := fsSemWithS tSQ tQ

/-- The program's semantics. -/
@[reducible] def tExtsSem : GooseSemantics := fsExtsSemanticsWithS tSQ tQ

theorem tFsSemOk : letI := tFsSem; FsSemOk :=
  fsSemWithS_ok tSQ tQ (noIoErr_noMapLockErr_keeps tIo tIo)

theorem tHasFs : letI := tExtsSem; letI := tFsSem; HasExt fsExt := fsExtsWithS_hasFs tSQ tQ

theorem tSat : FsStepSat (NoIoErr tIo) (S := tFsSem) :=
  letI := tFsSem
  haveI : FsStepSat tSQ := fsSemWithS_sat tSQ tQ
  fsStepSat_and_left (NoIoErr tIo) (NoMapLockErr tIo)

theorem tSatL : FsStepSat (NoMapLockErr tIo) (S := tFsSem) :=
  letI := tFsSem
  haveI : FsStepSat tSQ := fsSemWithS_sat tSQ tQ
  fsStepSat_and_right (NoIoErr tIo) (NoMapLockErr tIo)

attribute [local instance] tExtsSem tFsSem tFsSemOk tHasFs tSat tSatL

/-! ## The program -/

/-- **The tester's boot program**: initialize the package, then `Main(area, orDir)`. (Until 2026-11-24 the bare
`initialize'` here resolved, through `open go_etcd_io.raft.v3`, to raft's initializer, not the tester's: the
program initialized raft only, and the hypothesis `Hinit_wp` asked raft's initializer for the tester's
`isPkgInit`. Fixed with `Hinit_wp`'s removal, branch `wal-open`.) -/
def bootWal [GoGlobalContext] [GoSemanticsFunctions] (area orDir : GoString) : Expr :=
  Seq (App (Val github_com.mit_pdos.etcd_grove.examples.etcd.wal.initialize') (Val #()))
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.Main)) (Val #area)) (Val #orDir))

/-- **The first boot's facts on the tree**: nothing logged, the area and the oracle directory in the
tree, no WAL name of the area holding anything, neither the oracle file nor its temporary. -/
def tFirst (e : TEnv) (V : Hist) : Prop :=
  V.2 = [] ∧ e.jr ∈ V.now ∧ (∀ b, AreaSlot b → V.now.entry e.jr b = none) ∧ e.jo ∈ V.now ∧
    V.now.entry e.jo e.orFile.b = none ∧ V.now.entry e.jo e.orFile.tb = none

section open_
variable [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
  [_root_.Perennial.internal.filepathlite.Assumptions] [_root_.Perennial.io.Assumptions]
  [_root_.Perennial.time.Assumptions] [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
  [go_etcd_io.raft.v3.Assumptions]

/-- **The specs the tester's proof takes that no proof discharges yet** (the tester Link's hypotheses
but the model's laws and `WalDecEnvSupply`, which are proved): the trust-boundary spec of `proto.Unmarshal`
on a WAL record. (`errors.{IsErrno, IsPathErrnoEof, IsPathErrnoNotExist, IsPathErrnoTerm}` and
`WalDecEnvSupply` proved 2026-11-22, `wal-safe-errors`; `stringslite.HasPrefix` Perennial's, proved there,
since the pin 9c3b81f30.) -/
structure TOpen : Prop where
  unmarshalWalRecordE : proto.UnmarshalWalRecordE.spec (GF := GF) (hG := hG)

end open_

section ghost
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `hG` with the Go local context `lctx` (a closed theorem's hypotheses are stated at the program's). -/
abbrev tHeapAt (hG : HeapGS .hasLC GF) (lctx : GoLocalContext) : HeapGS .hasLC GF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

end ghost

/-- **The WAL's ghost state in the file extension's** (`fsGF`, `GooseLang/Ext/Fs/Adequacy.lean`, the
statement's ghost state): `AbsDiskGpreS` asks only for the universal camera, `fsGpreS`'s. -/
abbrev tAbsPre : AbsDiskGpreS fsGF := ⟨fsGpreS.goosePreGAllG⟩

end etcd_wal
end EtcdGrove
end Perennial

end
