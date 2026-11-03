/- Lean-first (no Rocq counterpart). `testMinibolt(dir)` (`examples/bboltfs/programs.go`): on a fresh database (no file at `dir/db`), 39 commits, each visible to `Get` and `Snapshot`, then `Close`, `Open` and the last commit still there. It returns true in every run: on an environmental failure it stops through `envFailure` (true), and otherwise every check holds. The precondition: minibolt's package facts (`pkgFacts`), the programs' (`envFacts`), the file system's invariant, no file at `dir/db`, and the main thread's thread token, with which it reads (`Get`, `Snapshot`), under `threadBound GF ≤ 2 ^ 30` (`Open`'s pool of reader slots). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.envFailure
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- See the file header. -/
abbrev testMinibolt.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] (dir : GoString),
  {{ pkgFacts (GF := GF) ∗ envFacts (GF := GF) ∗ osInv (GF := GF) ∗
      osMeta (GF := GF) (dir ++ go!"/db") (DFrac.own 1) none ∗ threadTok }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.testMinibolt)) (Val #dir))
  {{ RET #true; True }}

end spec

end bboltfs
end EtcdGrove
end Perennial
