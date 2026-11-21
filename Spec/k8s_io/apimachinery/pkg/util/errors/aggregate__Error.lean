/-
`aggregate.Error()` (`k8s.io/apimachinery/pkg/util/errors/errors.go`, translated with its body):
the messages of the tree's leaves, deduplicated (`sets.String`), joined. The spec: for a tree
(`errTreeN`), some string, needing nothing more; so an error tree is `errOk`
(`Proof/.../util/errors/ErrTreeOk.lean`), what `fmt.Errorf("%w", agg)` needs of it (conditional
authorization's `validateConditions` and `collectReasonsAndErrors`). Lean-first (no Rocq
counterpart).
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

/-- See the file header. -/
abbrev aggregate.Error.spec : Prop :=
  ∀ (n : Nat) (sl : GoSlice) (ys : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.errors ∗
      sl ↦*□ ys ∗ [∗list] y ∈ ys, errTreeN n y }}
    (App (Val #(methods k8s_io.apimachinery.pkg.util.errors.aggregate.ty go!"Error" #sl)) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end utilerrors
end EtcdGrove
end Perennial
