/- Lean-first (no Rocq counterpart). `testMiniboltConcurrent(dir)` (`examples/bboltfs/programs.go`): on a fresh database (no file at `dir/db`), two readers (one calling `Get`, one `Snapshot`, 20 times each) while the main thread commits 39 times; each reader sees a value `valueOk` accepts, never older than one it saw before. It returns true in every run. The precondition is `testMinibolt`'s; each reader goroutine reads with its own thread token, the one its `go` statement gives it. -/
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
abbrev testMiniboltConcurrent.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 30)] (dir : GoString),
  {{ pkgFacts (GF := GF) ∗ envFacts (GF := GF) ∗ osInv (GF := GF) ∗
      osMeta (GF := GF) (dir ++ go!"/db") (DFrac.own 1) none ∗ threadTok }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.testMiniboltConcurrent)) (Val #dir))
  {{ RET #true; True }}

end spec

end bboltfs
end EtcdGrove
end Perennial
