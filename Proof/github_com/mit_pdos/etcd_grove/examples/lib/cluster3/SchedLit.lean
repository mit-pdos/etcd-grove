/-
**A partition schedule as a Go slice literal** (`schedLit`; until 2026-11-05, K6 of
`notes/k8s-compactor-plan.md`, in `examples/etcd/partition/Adequacy.lean`): what a caller of a
program taking a schedule (`[]cluster3.Step`) builds before the call, since a fresh state holds no
slice; with the literal's size (`arrayLiteralSize_vals`, from `proto/Store.lean` since the per-type
stage). The closed theorems of the programs over
`cluster3`'s partitioner take it. Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3
public import Perennial.Golang.Theory.ArrayLit
public import Proof.google_golang_org.protobuf.proto.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section lit
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **The schedule `steps` as the Go slice literal `[]Step{...}`**: what a caller of `Main` builds
(its keyed elements as the value they take one pure step to become, `LiteralValueV`). -/
def schedLit (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) : Expr :=
  App (Val (GoInstruction (CompositeLiteral
    (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty))))
    (Val (LiteralValueV
      (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty))))

end lit

end EtcdGrove
end Perennial
