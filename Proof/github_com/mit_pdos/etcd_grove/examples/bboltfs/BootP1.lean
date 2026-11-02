/- Lean-first (no Rocq counterpart). minibolt's crash property (`examples/bboltfs/README.md`):
the premise P1, and the statement of `BootMinibolt`'s crash safety under it.

**P1: no checksum collision on a torn meta** (plan D1). A meta slot is the 64 bytes at offset
16 of page 0 or 1. At a crash, if the slot of the crash image of the database file passes
`validate` (`metaValid`: magic, version, and the FNV-64a checksum of the first 56 bytes), then it
is the slot's durable bytes; or the slot's page-cache bytes, if each byte of the slot is dirty
or lost (it was written whole since the last sync: a write that failed part-way leaves a slot
whose untouched bytes are still clean, and such a mix validates only by a collision); or the
slot as a write in flight would leave it. `P1 p st st'` relates the state `st` at the crash and
the state `st'` the next boot starts from (`OsCrash st st'`).

The write in flight is nonempty: an empty write changes nothing, so the slot "as it would leave
it" is the page cache's, which the second case admits only if every byte of the slot is dirty or
lost. Without it, an empty write in flight anywhere in the file (which any thread may start) would
admit the page cache's slot even when torn (a failed write's mix of new bytes and clean old
ones), which is a checksum collision on a torn meta, the case P1 excludes.

**The statement** (`BootCrashSafety`): the boot program (initialize the package, call
`BootMinibolt(dir)`) is run with the Linux file extension's semantics whose crash relation is
`OsCrash ∧ P1 (dir ++ "/db")` (`osFsExtsSemanticsWith`, `GooseLang/Ext/OsFs/CrashP1.lean`): that
is where P1 shows. In every execution with crashes from a state where `dir/db` is allowed and
absent, no thread is stuck and none has an unrecovered panic, for executions along which fewer
than `2 ^ 30` threads are live (`RealCrashThreadsBelow`, the thread bound Perennial's adequacy
theorems take as a hypothesis on the executions: `Open` builds the reader pool of `mmaplock` for at
most `2 ^ 30` live threads, Go's `rwmutexMaxReaders`). It is a `def`:
`bootCrashSafety` (`Results.lean`) proves it under the hypotheses of package initialization
(`Hinit_wp`) and the `os.file`/`os.fileStat` field instances.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB
public import GooseLang.Ext.OsFs.CrashP1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open github_com.mit_pdos.etcd_grove.examples.bboltfs

/-- The meta slot of page `i` of the bytes `l`: 64 bytes at offset 16. -/
def metaSlot (l : List w8) (i : Nat) : List w8 := ((l.drop (4096 * i)).drop 16).take 64

/-- **P1** for the file at `p`, at a crash from `st` to `st'` (see the file header). -/
def P1 [GooseExts] (p : GoString) (st st' : OsState) : Prop :=
  ∀ (f : OsFile) (img : List w8) (i : Nat), st.file p = some f →
    st'.files !! p = some (some (OsFile.ofDisk img)) → i < 2 → 4096 * i + 80 ≤ img.length →
    metaValid (fileMeta img i) →
    metaSlot img i = metaSlot f.durable i ∨
    ((∀ k < 64, f.dirty (4096 * i + 16 + k) = true ∨ f.lost (4096 * i + 16 + k) = true) ∧
      metaSlot img i = metaSlot f.cur i) ∨
    ∃ (t off : Nat) (data : List w8), st.inflight !! t = some ⟨p, .write off data⟩ ∧ data ≠ [] ∧
      metaSlot img i = metaSlot (writeBytes f.cur off data) i

attribute [local instance] osFsExts osFsExtsInterp

/-- The boot program: initialize the package, then call `BootMinibolt(dir)`. -/
def boot [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve BootMinibolt []))) (Val #())) (Val #dir))

/-- **The crash safety of `BootMinibolt`** under P1 (see the file header): the statement. -/
def BootCrashSafety [GoGlobalContext] [lctx : GoLocalContext]
    [sem : go.Semantics] [package_sem : Assumptions]
    (dir : GoString) : Prop :=
  ∀ (σ : state) (g : GlobalState),
    σ.goState.goLctx = lctx → σ.goState.packageState = ∅ →
    OsInit (extLocal (h := osFsExts_hasOsFs.toElemExt) osFsExt σ.world) →
    (extLocal (h := osFsExts_hasOsFs.toElemExt) osFsExt σ.world).files !! (dir ++ go!"/db") =
      some none →
    σ.threads = 1 →
    ∀ (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool),
    @RealCrashNsteps osFsExts (osFsExtsSemanticsWith (P1 (dir ++ go!"/db"))) _ (boot dir) n
      ([boot dir], ((σ, g) : CfgState)) κs (t2, σ2) b →
    @RealCrashThreadsBelow osFsExts (osFsExtsSemanticsWith (P1 (dir ++ go!"/db"))) _ (boot dir)
      (2 ^ 30) n ([boot dir], ((σ, g) : CfgState)) →
    (∀ e2, e2 ∈ t2 → @RealNotStuck osFsExts (osFsExtsSemanticsWith (P1 (dir ++ go!"/db"))) _ e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)

end bboltfs
end EtcdGrove
end Perennial
