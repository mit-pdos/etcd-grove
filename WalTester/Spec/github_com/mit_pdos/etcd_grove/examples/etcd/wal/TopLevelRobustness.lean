/- Lean-first (no Rocq counterpart).

# The WAL tester (`examples/etcd/wal`): the top-level robustness result, stated

`etcd_wal_safe`: the tester's crash safety (`etcd_wal_crash_safety_bounded`,
`WalTester/Proof/.../examples/etcd/wal/Adequacy.lean`) as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads, no thread is
stuck and none has an unrecovered panic). The tester runs alone on one machine that may crash at any
step and restart. The tester checks the WAL against its oracle and panics on a violation, so its
robustness is the WAL's crash correctness as `Main` checks it (`notes/wal-units/tester.md`).

Its semantics is the file extension's restricted by `tSQ` (no I/O error, no lock or mapping error,
on any file or path) and `tQ` (a crash keeps no CRC collision in the WAL's images): `tExtsSem`,
`WalTester/Proof/.../TopLevelDefs.lean`. That semantics' `initLocal` is the default (`True`), so the file
state as on disk (`FsInit`) is a premise here, as in the osfs examples.

**A visible premise: `Hopen`** (`TOpen`): the specs the proof takes that no proof discharges yet, today
only `proto.UnmarshalWalRecordE.spec` (`proto.Unmarshal` of a WAL record, with its error's identity;
upamanyus's protobuf plan, etcd-grove#37 S3). When it is proved the premise goes, a strengthening.

The thread bound is the step bound's (`threads := bound + 1`, `Robust` without a thread bound): the
bounded theorem's thread bound `T` is free and an execution of `n` steps from one thread has fewer than
`n + 2` (`RealCrashThreadsBelow.of_single`). The step bound `2 ^ 62` is the bounded theorem's largest.

This file only states it (to audit); the proof is in
`WalTester/Proof/github_com/mit_pdos/etcd_grove/examples/etcd/wal/TopLevelRobustness.lean`.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.TopLevelDefs
public import Robustness.Statement
public import Proof.log.NewModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3 Fs WalEnc WalFs

attribute [local instance] fsExts fsExtsInterp tExtsSem tFsSem tFsSemOk tHasFs tSat tSatL

section statement
-- the premises are named for the reader
set_option linter.unusedVariables false
variable [GoGlobalContext]

/-- **The WAL tester is robust** (see the file header): `bootWal area orDir` alone on one machine that
may crash at any step and restart, a fresh Go process (`Robust`'s premise), its file state as on disk,
the area and the oracle directory two distinct roots (`e.jr`, `e.jo` of the roots `e.R`), the first
boot's facts (`tFirst`: no WAL in the area, no oracle file), the WAL's paths fitting, and the open specs
(`Hopen`): in every execution of fewer than `2 ^ 62` steps no thread is stuck and none has an
unrecovered panic. -/
def etcd_wal_safe.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.go_uber_org.zap.Assumptions]
    [github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions] [os.Assumptions]
    [os.fileStat.FieldAssumptions] [github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]
    [os.file.FieldAssumptions] [_root_.Perennial.internal.filepathlite.Assumptions]
    [_root_.Perennial.path.filepath.Assumptions] [syscall.Assumptions]
    [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]
    [go_etcd_io.etcd.server.v3.storage.wal.Assumptions] [go_etcd_io.raft.v3.Assumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.strings.Assumptions]
    [go_etcd_io.etcd.pkg.v3.ioutil.Assumptions] [_root_.Perennial.encoding.binary.Assumptions]
    [_root_.Perennial.bufio.Assumptions] [go_etcd_io.etcd.pkg.v3.crc.Assumptions]
    [hash.crc32.Assumptions] [go_etcd_io.etcd.pkg.v3.pbutil.Assumptions] [go_uber_org.zap.Assumptions]
    [_root_.Perennial.time.Assumptions] [_root_.Perennial.io.Assumptions]
    [_root_.Perennial.internal.stringslite.Assumptions] [_root_.Perennial.log.NewModel]
    -- the specs no proof discharges yet (see the file header)
    (Hopen : ∀ hG : HeapGS .hasLC fsGF, TOpen (GF := fsGF) (hG := tHeapAt hG lctx))
    (σ : state) (g : GlobalState) (e : TEnv)
    (Hinit : FsInit (extLocal fsExt σ.world)) (hRe : (extLocal fsExt σ.world).fs.roots = e.R)
    (hr : (e.area, e.jr) ∈ e.R) (ho : (e.orDir, e.jo) ∈ e.R) (hne : e.jo ≠ e.jr)
    (hf : e.orFile.Ok) (hpaths : tWalPathsOk e.area)
    (hfit : PathFits (tWalDir e.area ++ go!".tmp") ∧ PathFits (tWalDir e.area))
    (Hfirst : tFirst e ((extLocal fsExt σ.world).fs.treeDur, [])),
    Robustness.Robust [(bootWal e.area e.orDir, σ)] [] g (threads := 2 ^ 62 + 1)
      (bound := 2 ^ 62)

end statement

end etcd_wal
end EtcdGrove
end Perennial

end
