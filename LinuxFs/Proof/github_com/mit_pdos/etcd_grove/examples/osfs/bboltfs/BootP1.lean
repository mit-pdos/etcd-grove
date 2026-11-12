/- Lean-first (no Rocq counterpart). minibolt's crash property (`examples/osfs/bboltfs/README.md`):
the premise P1, and the statement of `BootMinibolt`'s crash safety under it, over the Linux file
extension's per-byte semantics (`GooseLang/Ext/Fs/Impl.lean`).

**P1: no checksum collision on a torn meta.** A meta slot is the 64 bytes at offset 16 of page 0
or 1 of a file (minibolt's database file's metas; P1 is stated of every file, the database file
being the only one the boot program makes, and its reason, a checksum collision, holding of any). At a crash from `st` to `st'`, each byte of a file comes back as one of
its candidates in `st` (`CrashFile`), independently: the semantics lets a crash mix, inside a slot,
bytes of two writes, or a write's prefix with what was there before. P1 says that a slot that does
so does not validate: if the slot of the crash image, read through its page cache (past the size
included, in a page that holds a byte of the file), passes `validate` (`metaValid`: magic, version,
and the FNV-64a checksum of its first 56 bytes), then it is the slot as of one change `n`: each of
its bytes is its value as of `n` (`valAt`, its candidate of the largest stamp up to `n`).

Why P1 holds of `BootMinibolt`'s real runs on the target configuration (the final review,
`notes/axiom-review/fs-final.md`): between two syncs a slot of `dir/db` has only two states: zeros
and `meta(j)` (`init`, slot `j`), or `meta(t-2)` and `meta(t)` (commit `t`, slot `t % 2`), because an
`fdatasync` follows every slot write before the next, a failed sync ends the boot program's writes,
and `meta(t)` is a function of `t` (a commit retried after a crash writes the same meta). A slot left
torn by an earlier crash is itself a mix of the same two states. The enumeration
`notes/axiom-review/fs-final/p1mix/main.go` tries every byte-wise mix of every such pair for every
txid up to the 1 GiB bound (2^18 pairs, 2.2 M mixes of the checksummed 56 bytes, with every mix of the
checksum field): no mix validates except the two states themselves. So P1 removes no crash Linux on
the target configuration can produce in a `BootMinibolt` run (given the semantics' device assumption:
a byte comes back old or new, never garbage); in general it is bbolt's own assumption that a torn meta
does not collide on its checksum. P1 is never vacuous (`P1Sat.p1_crash_exists`: from every reachable
state, whenever there is a crash there is one satisfying P1) and a file other than the database never
makes it fail (`P1Sat.p1_untouched`).

**The statement** (`BootCrashSafety`): the boot program (initialize the package, call
`BootMinibolt(dir)`) runs with the extension's semantics whose crash relation is `OsCrash ∧ P1`
and whose steps are all of `FsStep`'s (`fsExtsSemanticsWithS AnyStep P1`):
in every execution with crashes from a state as on disk (`FsInit`) in which `dir` is one of the
roots and `dir/db` names nothing, no thread is stuck and none has an unrecovered panic, for
executions along which fewer than `2 ^ 30` threads are live (`RealCrashThreadsBelow`: `Open`
builds the reader pool of `mmaplock` for at most `2 ^ 30` live threads, Go's `rwmutexMaxReaders`).
Proved in `Results.lean` (`bootCrashSafety`).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.CrashGood
public import GooseLang.Ext.Fs.AdequacyS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs Fs

/-- No premise on steps: every step of `FsStep`. -/
def AnyStep : StepPrem := fun _ _ _ _ _ => True

/-- **P1**, at a crash from `st` to `st'` (see the file header): a meta slot of a crash image that
validates, in a page that holds a byte of the file, is the slot as of one change. -/
def P1 [GooseExts] (st st' : OsState) : Prop :=
  ∀ (i : Ino) (f f' : OsFile), st.fs.files !! i = some f →
    st'.fs.files !! i = some f' → ∀ j < 2, 4096 * j < f'.size →
      metaValid (decode (rawSlot f' j) : Meta) →
      ∃ n, ∀ k < 64, f'.cache (4096 * j + 16 + k) = valAt (f.cand (4096 * j + 16 + k)) n

attribute [local instance] fsExts fsExtsInterp

/-- The boot program: initialize the package, then call `BootMinibolt(dir)`. -/
def boot [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve BootMinibolt []))) (Val #())) (Val #dir))

/-- **The crash safety of `BootMinibolt`** under P1 (see the file header): the statement. -/
def BootCrashSafety [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions]
    (dir : GoString) : Prop :=
  letI := fsExtsSemanticsWithS AnyStep P1
  letI := fsExtsWithS_hasFs AnyStep P1
  ∀ (σ : state) (g : GlobalState),
    σ.goState.goLctx = lctx → σ.goState.packageState = ∅ →
    FsInit (extLocal fsExt σ.world) →
    (∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots) →
    (extLocal fsExt σ.world).lookup (dir ++ go!"/db") = none →
    σ.threads = 1 →
    ∀ (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool),
    RealCrashNsteps (boot dir) n ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b →
    RealCrashThreadsBelow (boot dir) (2 ^ 30) n ([boot dir], ((σ, g) : CfgState)) →
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧ (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)

end osfs_bboltfs
end EtcdGrove
end Perennial

end
