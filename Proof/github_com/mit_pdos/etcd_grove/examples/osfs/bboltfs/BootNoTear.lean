/- Lean-first (no Rocq counterpart). The statement of minibolt's crash safety over Fs v2, under the
no-tear assumption (`GooseLang/Ext/Fs/NoTear.lean`) in place of v1's P1 (no checksum collision on
a torn meta, `old/osfs-v1/.../BootP1.lean`).

**The statement** (`BootCrashSafety`): the boot program (initialize the package, call
`BootMinibolt(dir)`) runs with the Linux file extension v2's semantics restricted by the no-tear
premises (`fsExtsSemanticsWithS NoTearStep NoTearCrash`: a `pwrite` within one page lands all of
it or nothing, and a crash leaves each sector such a write in flight touches as one of its versions
or the write's): in every execution with crashes from a state as on disk (`FsInit`) in which
`dir` names a directory and `dir/db` nothing, no thread is stuck and none has an unrecovered panic,
for executions along which fewer than `2 ^ 30` threads are live (`RealCrashThreadsBelow`: `Open`
builds the reader pool of `mmaplock` for at most `2 ^ 30` live threads, Go's `rwmutexMaxReaders`).

What replaces P1 is not an assumption: minibolt writes each meta page at most once between two
successful `fdatasync`s, so the file's `OsMeta` knows each meta sector has at most two versions
(`OsMeta.vk`), and a crash leaves the sector whole (`crashSeen_sec`); the in-page write in flight
is the no-tear premise. Its proof is not done (`notes/STATUS.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.CrashOk
public import GooseLang.Ext.Fs.AdequacyS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs Fs

attribute [local instance] fsExts fsExtsInterp

/-- The boot program: initialize the package, then call `BootMinibolt(dir)`. -/
def boot [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve BootMinibolt []))) (Val #())) (Val #dir))

/-- **The crash safety of `BootMinibolt`** under the no-tear premises (see the file header): the
statement. -/
def BootCrashSafety [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions]
    (dir : GoString) : Prop :=
  letI := fsExtsSemanticsWithS NoTearStep NoTearCrash
  letI := fsExtsWithS_hasFs NoTearStep NoTearCrash
  ∀ (σ : state) (g : GlobalState),
    σ.goState.goLctx = lctx → σ.goState.packageState = ∅ →
    FsInit (extLocal fsExt σ.world) →
    (∃ j, (extLocal fsExt σ.world).lookup dir = some (.dir j)) →
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
