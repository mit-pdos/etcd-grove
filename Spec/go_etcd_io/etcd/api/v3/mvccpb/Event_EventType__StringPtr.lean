/-
`(*Event_EventType).String()` (k8s 7f-5a-P: the etcd3 watcher's `parseEvent` calls `e.Type.String()`
on the field's address, `etcd3.lean`'s `MethodResolve (PointerType Event_EventType.ty) "String"`):
some string, the pointer's value unchanged (read-only). The trust boundary: an axiom,
`Proof/go_etcd_io/etcd/api/v3/mvccpb/Event_EventType__StringPtr.lean` (T5-f over the pointer receiver,
approved by the user 2026-11-15 via etcd-grove-81; `notes/k8s-7f5a-draft.md` §11.5). Why it is
faithful: `String` is a value method (`kv.pb.go:50`); the method set of `*Event_EventType` contains it
by Go's method-set rule ("the method set of a pointer to a defined type T is the set of all methods
declared with receiver *T or T"), as the compiler's wrapper that reads `*l` and calls the value method:
so the call reads the value at `l` (the read-only points-to), writes nothing, and returns what the
value method returns, some string for every value once mvccpb is initialized (`String` reads the
enum's descriptor, which `file_kv_proto_init` fills; unknown values print as numbers); a nil `l`
panics, which `l ↦□ t` excludes. Go evidence: `examples/premisefix/eventtypestr/` (the pointer call
equals the value call for named, unknown, negative and extreme values, through every call form;
read-only under `-race`; nil panics). When goose emits the `ptr_M_unfold` of an axiomatized value
method (`notes/perennial-changes.md`), this becomes a theorem of a value axiom. Lean-first.
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
