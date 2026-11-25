/- Lean-first (no Rocq counterpart).

# The WAL tester (`examples/etcd/wal`): the definitions its top-level statement is written in

The tester's semantics (`tExtsSem`: the file system does not fail, `tSQ`, and a crash keeps no CRC
collision in the WAL's images, `tQ`), its boot program (`bootWal`), the first boot's facts (`tFirst`),
the step and thread bounds (`tStepBound`, `tThreads`), and the WAL's ghost state in the file extension's
(`tAbsPre`), so that the statement (`WalTester/Spec/.../TopLevelRobustness.lean`) imports no proof
(CLAUDE.md, "Import tiers").
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

/-- **The tester's boot program**: initialize the tester's package (its initializer named in full: `open
go_etcd_io.raft.v3` would resolve a bare `initialize'` to raft's), then `Main(area, orDir)`. -/
def bootWal [GoGlobalContext] [GoSemanticsFunctions] (area orDir : GoString) : Expr :=
  Seq (App (Val github_com.mit_pdos.etcd_grove.examples.etcd.wal.initialize') (Val #()))
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.Main)) (Val #area)) (Val #orDir))

/-- **The first boot's facts on the tree**: nothing logged, the area and the oracle directory in the
tree, no WAL name of the area holding anything, neither the oracle file nor its temporary. -/
def tFirst (e : TEnv) (V : Hist) : Prop :=
  V.2 = [] ∧ e.jr ∈ V.now ∧ (∀ b, AreaSlot b → V.now.entry e.jr b = none) ∧ e.jo ∈ V.now ∧
    V.now.entry e.jo e.orFile.b = none ∧ V.now.entry e.jo e.orFile.tb = none

/-! ## The bounds -/

/-- **The step bound: the proof's limit.** The WAL's file pipeline counts the files it hands over in a
Go `int`, and a cut needs `count + 2 < 2 ^ 63` (`WAL.cut.spec`); the WAL spends one receipt per step and
turns the global receipt bound into that counter's bound (`walAreaOk`'s `ReceiptBoundLe GF (2 ^ 62)`, `walPc_bound`,
`Proof/go_etcd_io/etcd/server/v3/storage/wal/Handle.lean`). -/
abbrev tStepBound : Nat := 2 ^ 62

/-- **No thread bound.** An execution of fewer than `tStepBound` steps started by one thread has fewer
than `tStepBound + 1` live threads (a step spawns at most one: `RealCrashThreadsBelow.of_single`), so
`Robust` at this thread bound covers every execution within the step bound. -/
abbrev tThreads : Nat := tStepBound + 1

/-- **The WAL's ghost state in the file extension's** (`fsGF`, `GooseLang/Ext/Fs/Adequacy.lean`, the
statement's ghost state): `AbsDiskGpreS` asks only for the universal camera, `fsGpreS`'s. -/
abbrev tAbsPre : AbsDiskGpreS fsGF := ⟨fsGpreS.goosePreGAllG⟩

end etcd_wal
end EtcdGrove
end Perennial

end
