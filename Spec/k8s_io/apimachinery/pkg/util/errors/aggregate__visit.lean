/-
`aggregate.visit(f)` (`k8s.io/apimachinery/pkg/util/errors/errors.go`, translated with its body):
calls `f` on the leaves of the error tree, depth first, stopping at the first `true`. The spec is
for a tree (`errTreeN`: its `aggregate`s read-only, its leaves no `Aggregate`) and an `f` that, on
any leaf, returns `false` keeping `I` (what `aggregate.Error`'s closure does): `visit` returns
`false`, keeping `I`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.errors.Defs
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace utilerrors

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `f(e)` on any leaf `e` returns `false`, keeping `I`. -/
def visitFnOk (f : GoFunc) (I : IProp GF) : IProp GF :=
  iprop(□ ∀ e : GoInterface, errLeafOk e -∗ {{ I }} (App (Val #f) (Val #e)) {{ RET #false; I }})

instance visitFnOk_persistent (f : GoFunc) (I : IProp GF) :
    Persistent (visitFnOk (GF := GF) f I) := by
  unfold visitFnOk; infer_instance

/-- See the file header. -/
abbrev aggregate.visit.spec : Prop :=
  ∀ (n : Nat) (sl : GoSlice) (ys : List GoInterface) (f : GoFunc) (I : IProp GF),
  {{ sl ↦*□ ys ∗ ([∗list] y ∈ ys, errTreeN n y) ∗ visitFnOk f I ∗ I }}
    (App (Val #(methods k8s_io.apimachinery.pkg.util.errors.aggregate.ty go!"visit" #sl)) (Val #f))
  {{ RET #false; I }}

end spec

end utilerrors
end EtcdGrove
end Perennial
