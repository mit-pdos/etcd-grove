/-
`errors.Join(errs...)` (names-only in Perennial): Go's documentation, "Join returns nil if every
value in errs is nil"; the spec says only that (the batch informer's `processDeltasInBatch` returns
`errors.Join(keyErrs...)` with no key error). The slice is only read. The trust boundary: an axiom,
`Proof/errors/Join.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Code.errors
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev errors.Join.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (es : List GoInterface),
  {{ (sl ↦*{dq} es : IProp GF) }}
    (App (Val (@! _root_.Perennial.errors.Join)) (Val #sl))
  {{ (e : GoInterface), RET #e; ⌜(∀ x ∈ es, x = interface.nil) → e = interface.nil⌝ ∗
      sl ↦*{dq} es }}

end spec

end EtcdGrove
end Perennial
