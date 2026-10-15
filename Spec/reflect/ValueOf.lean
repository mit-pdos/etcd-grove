/-
`reflect.ValueOf`: the trust boundary (`reflect` is names-only: Go reflection, which Goose does
not model). Lean-first (no Rocq counterpart); unit P4 (2026-10-14), for the txn package's `isNil`
(`util.go`: `reflect.ValueOf(msg).IsNil()`).

For the one call shape: an interface holding a pointer `p` (of any type `*T`). `ValueOf` returns
the `reflect.Value` of it (an axiomatized type: the result is a `val`), whose `IsNil()` reports
whether `p` is nil (`reflect/value.go`: `IsNil` of a `Pointer` kind reads the pointer; it panics
only for a kind that cannot be nil, which a pointer is not). `IsNil` is a method of that value,
specified here, in `ValueOf`'s postcondition, as a persistent triple of the call as Goose
translates it (`MethodResolve reflect.Value.ty "IsNil"` on the value: `reflect.Value` is
axiomatized, without the underlying type `MethodResolve`'s step needs; the shape of
`prometheus.HistogramVec.WithLabelValues`' observer).
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

/-- `reflect.ValueOf(i)` of an interface holding the pointer `p` of type `*T`: a value `v` whose
`IsNil()` returns whether `p` is nil (persistent). -/
abbrev reflect.ValueOf.spec : Prop :=
  ∀ (T : go.GoType) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
    (App (Val (@! _root_.Perennial.reflect.ValueOf))
      (Val #(interface.mkOk (go.GoType.PointerType T) #p)))
  {{ (v : val), RET v;
      □ ({{ True }}
          (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.reflect.Value.ty go!"IsNil")))
            (Val v)) (Val #()))
        {{ RET #(decide (p = null)); True }}) }}

end spec

end EtcdGrove
end Perennial
