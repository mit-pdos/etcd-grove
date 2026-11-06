/- Lean-first (no Rocq counterpart). `testMiniboltConcurrent(dir)` (`examples/osfs/bboltfs/programs.go`): on a fresh database (no file at `dir/db`, `dir` a directory of the tree, of which the caller gives the whole history), two readers (one calling `Get`, one `Snapshot`, 20 times each) while the main thread commits 39 times; each reader sees a value `valueOk` accepts, never older than one it saw before. It returns true in every run. The precondition is `testMinibolt`'s; each reader goroutine reads with its own thread token, the one its `go` statement gives it. -/
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
abbrev testMiniboltConcurrent.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] (dir : GoString) (R : Roots) (V : Hist) (j : Ino),
  RootsOk R → lookupH R V dir = some (.dir j) → lookupH R V (dir ++ go!"/db") = none →
  {{ pkgFacts (GF := GF) ∗ envFacts (GF := GF) ∗ osInv (GF := GF) ∗
      osTree (GF := GF) (DFrac.own 1) R V ∗ threadTok }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.testMiniboltConcurrent)) (Val #dir))
  {{ RET #true; True }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
