/-
`reflect.TypeOf`: the trust boundary (`reflect` is names-only: Go reflection, which Goose does not
model). Lean-first (no Rocq counterpart); for the Kubernetes etcd3 store's `getTypeName`
(`reflect.TypeOf(obj).String()`, a tracing attribute).

For a non-nil interface (whose `TypeOf` is a non-nil `reflect.Type`; `String()` of the nil
`Type` panics): some `reflect.Type`, whose `String()` returns some string. As `reflect.ValueOf`'s
`IsNil`, `String` is specified in the postcondition, as a persistent triple of the call as Goose
translates it (`MethodResolve reflect.Type'.ty "String"` on the value).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev reflect.TypeOf.spec : Prop :=
  ∀ (x : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ ⌜x ≠ GoInterface.nil⌝ }}
    (App (Val (@! _root_.Perennial.reflect.TypeOf)) (Val #x))
  {{ (t : val), RET t;
      □ ({{ True }}
          (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.reflect.Type'.ty go!"String")))
            (Val t)) (Val #()))
        {{ (s : GoString), RET #s; True }}) }}

end spec

end EtcdGrove
end Perennial
