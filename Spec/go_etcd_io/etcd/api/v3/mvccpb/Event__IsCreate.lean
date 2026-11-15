/-
`(*mvccpb.Event).IsCreate()` (`api/mvccpb/extension.go:18-20`, translated for the etcd3 watcher's `parseEvent`, called through the client's alias `clientv3.Event`, k8s 7f-5a-P): on a non-nil `*Event` whose `Kv` is non-nil, whether its type is `PUT` (`0`) and its key-value's create and mod revisions are equal. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev mvccpb.Event.IsCreate.spec : Prop :=
  ∀ (p kv : Loc) (t : w32) (cr mr : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb ∗ ⌜p ≠ null ∧ kv ≠ null⌝ ∗
      structFieldRef mvccpb.Event go!"Type" p ↦□ t ∗ structFieldRef mvccpb.Event go!"Kv" p ↦□ kv ∗
      structFieldRef mvccpb.KeyValue go!"CreateRevision" kv ↦□ cr ∗
      structFieldRef mvccpb.KeyValue go!"ModRevision" kv ↦□ mr }}
    (App (Val (p @!! go.GoType.PointerType mvccpb.Event.ty @!! go!"IsCreate")) (Val #()))
  {{ RET #(decide (t = W32 0 ∧ cr = mr)); True }}

end spec

end EtcdGrove
end Perennial
