/-
**A partition schedule as a Go slice literal** (`schedLit`; until 2026-11-05, K6 of
`notes/k8s-compactor-plan.md`, in `examples/etcd/partition/Adequacy.lean`): what a caller of a
program taking a schedule (`[]cluster3.Step`) builds before the call, since a fresh state holds no
slice; with the literal's size (`arrayLiteralSize_vals`). The closed theorems of the programs over
`cluster3`'s partitioner take it. Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3
public import Perennial.Golang.Theory.ArrayLit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section lit
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The fold of `go.arrayLiteralSize` over the keyed elements of values counts them. -/
theorem foldl_arrayLitKE {V : Type} (t : go.GoType) (F : Int × Int → keyed_element → Int × Int)
    (hF : ∀ (i m : Int) (x : V), F (i, m) (arrayLitKE t x) = (i + 1, m)) :
    ∀ (l : List V) (i m : Int), List.foldl F (i, m) (l.map (arrayLitKE t)) = (i + l.length, m)
  | [], i, m => by simp
  | x :: xs, i, m => by
    rw [List.map_cons, List.foldl_cons, hF, foldl_arrayLitKE t F hF xs]
    simp only [List.length_cons]
    congr 1
    push_cast
    omega

/-- **A literal of values has the values' count as size** (`go.arrayLiteralSize`). -/
theorem arrayLiteralSize_vals {V : Type} (t : go.GoType) (l : List V) :
    go.arrayLiteralSize (l.map (arrayLitKE t)) = l.length := by
  unfold go.arrayLiteralSize
  rw [foldl_arrayLitKE t _ (fun _ _ _ => rfl) l 0 0]
  simp

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
