/-
`reflect.Zero(typ)` of the `reflect.Type` of `T`: the zero `Value` of `T` (`reflZero`).

The trust boundary: an axiom, `Proof/reflect/Zero.lean` (`reflect` is names-only; the reasoning principles of `Proof/reflect/Values.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.reflect.Values
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI reflectM

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reflect.Assumptions]

/-- See the file header. -/
abbrev reflect.Zero.spec : Prop :=
  ∀ (rt : _root_.Perennial.reflect.Type') (T : go.GoType),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ ⌜reflType rt T⌝ }}
    (App (Val (@! _root_.Perennial.reflect.Zero)) (Val #rt))
  {{ (z : _root_.Perennial.reflect.Value), RET #z; ⌜reflZero z T⌝ }}

end spec

end EtcdGrove
end Perennial
