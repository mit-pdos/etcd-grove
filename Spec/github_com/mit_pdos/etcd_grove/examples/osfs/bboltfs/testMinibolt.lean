/- Lean-first (no Rocq counterpart). `testMinibolt(dir)` (`examples/osfs/bboltfs/programs.go`): on a fresh database (no file at `dir/db`, `dir` a directory of the tree, of which the caller gives the whole history), 39 commits, each visible to `Get` and `Snapshot`, then `Close`, `Open` and the last commit still there. It returns true in every run: on an environmental failure it stops through `envFailure` (true), and otherwise every check holds. The precondition: minibolt's package facts (`pkgFacts`), the programs' (`envFacts`), the file system's invariant, no file at `dir/db`, and the main thread's thread token, with which it reads (`Get`, `Snapshot`), under `threadBound GF ≤ 2 ^ 30` (`Open`'s pool of reader slots). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.envFailure
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- See the file header. -/
abbrev testMinibolt.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] (dir : GoString) (R : Roots) (V : Hist) (j : Ino),
  RootsOk R → lookupH R V dir = some (.dir j) → lookupH R V (dir ++ go!"/db") = none →
  {{ pkgFacts (GF := GF) ∗ envFacts (GF := GF) ∗ osInv (GF := GF) ∗
      osTree (GF := GF) (DFrac.own 1) R V ∗ threadTok }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.testMinibolt)) (Val #dir))
  {{ RET #true; True }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
