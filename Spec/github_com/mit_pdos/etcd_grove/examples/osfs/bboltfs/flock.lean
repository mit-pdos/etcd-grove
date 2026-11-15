/- Lean-first (no Rocq counterpart). `flock(f, exclusive)` (`examples/osfs/bboltfs/page.go`, bolt_unix.go's `flock` with no timeout): `syscall.Flock` with `LOCK_NB` and `LOCK_EX` or `LOCK_SH`, retried (after a `time.Sleep`) while it answers `EWOULDBLOCK`. Over the lock semantics (2026-11-15, `notes/wal-units/locks.md`; `Spec/syscall/Flock.lean`): on a description with no `flock` lock, with the whole fd; on success the description holds the lock (exclusive iff `exclusive`, with its token if exclusive, `lockTok`), on an error nothing changed. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Meta
public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- See the file header. -/
abbrev flock.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (d : OsFd) (exclusive : Bool),
  d.flk = none →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd (DFrac.own 1) d }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.flock)) (Val #f))
      (Val #exclusive))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗
      ((⌜err = interface.nil⌝ ∗ osFd fd (DFrac.own 1) (d.setLk .flock (some exclusive)) ∗
          lockTok (GF := GF) .flock fd (d.setLk .flock (some exclusive))) ∨
       (⌜err ≠ interface.nil⌝ ∗ osFd fd (DFrac.own 1) d)) }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
