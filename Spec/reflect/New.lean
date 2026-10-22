/-
`reflect.New(typ)` of the `reflect.Type` of `T`: the `Value` of a pointer to a fresh zeroed `T`
(`reflNew`).

The trust boundary: an axiom, `Proof/reflect/New.lean` (`reflect` is names-only; the reasoning
principles of `Proof/reflect/Values.lean`). Lean-first (no Rocq counterpart).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reflect.Assumptions]

/-- See the file header. -/
abbrev reflect.New.spec : Prop :=
  ∀ (rt : _root_.Perennial.reflect.Type') (T : go.GoType),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ ⌜reflType rt T⌝ }}
    (App (Val (@! _root_.Perennial.reflect.New)) (Val #rt))
  {{ (w : _root_.Perennial.reflect.Value) (p : Loc), RET #w;
      ⌜reflPtr w T p ∧ p ≠ null⌝ ∗ reflNew T p }}

end spec

end EtcdGrove
end Perennial
