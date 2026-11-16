/-
`(*Event_EventType).String()` (k8s 7f-5a-P: the etcd3 watcher's `parseEvent` calls `e.Type.String()`
on the field's address, `etcd3.lean`'s `MethodResolve (PointerType Event_EventType.ty) "String"`):
the value method `Event_EventType.String` of the value read at the pointer, so some string, the
pointer's value unchanged (read-only). In Go the pointer's method is the value method of `*l`; the
translation does not say so for a names-only value method (goose emits the `ptr_M_unfold` of a value
method only when the method is not axiomatized), so no proof derives this from
`mvccpb.Event_EventType.String.spec` yet: `parseEvent.wp_proof` takes it as a callee spec, and its
discharge is open (`notes/k8s-7f5-handoff.md`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init

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
abbrev mvccpb.Event_EventType.StringPtr.spec : Prop :=
  ∀ (l : Loc) (t : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb ∗ l ↦□ t }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.api.v3.mvccpb.Event_EventType.ty
      @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
