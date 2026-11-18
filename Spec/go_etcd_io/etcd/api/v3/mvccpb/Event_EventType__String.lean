/-
`Event_EventType.String(t)` (names-only; k8s 7f-5a, T5-f: the etcd3 watcher's `parseEvent` error for
a `nil` `PrevKv`, Q5): returns some string, for every value, once mvccpb is initialized (`String`
reads the enum's descriptor, which `file_kv_proto_init` fills; unknown values print as numbers).
No axiom (k8s 7f-5a-P step 7, `notes/k8s-7f5a-draft.md` §11.5): the watcher calls `String` through
the pointer, whose trust boundary is `Event_EventType__StringPtr.lean`; this value form is kept as the
statement the pointer form becomes a theorem of once goose unfolds an axiomatized value method's
pointer method (`notes/perennial-changes.md`). Lean-first.
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
abbrev mvccpb.Event_EventType.String.spec : Prop :=
  ∀ (t : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb }}
    (App (App (Val (GoInstruction (MethodResolve go_etcd_io.etcd.api.v3.mvccpb.Event_EventType.ty
      go!"String"))) (Val #t)) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
