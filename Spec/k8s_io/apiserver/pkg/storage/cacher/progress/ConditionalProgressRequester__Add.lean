/-
`(*ConditionalProgressRequester).Add()` (`progress/watch_progress.go`): one more waiting request (its counter, under the mutex), and a signal to the requester's loop. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.progress.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI k8s_io.apiserver.pkg.storage.cacher.progress

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.progress.Assumptions]

/-- See the file header. -/
abbrev ConditionalProgressRequester.Add.spec : Prop :=
  ∀ (pr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.progress ∗ isPR pr }}
    (App (Val (pr @!! go.GoType.PointerType ConditionalProgressRequester.ty @!! go!"Add")) (Val #()))
  {{ RET #(); True }}

end spec

end cacher
end EtcdGrove
end Perennial
