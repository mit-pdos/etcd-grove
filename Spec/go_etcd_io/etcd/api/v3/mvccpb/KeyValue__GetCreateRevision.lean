/-
`(*mvccpb.KeyValue).GetCreateRevision()` (`api/mvccpb/kv.pb.go`, translated for the etcd3 watcher's `parseEvent`, through `IsCreate`, k8s 7f-5a-P): on a non-nil `*KeyValue`, its `CreateRevision` field. Lean-first (no Rocq counterpart).
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
abbrev mvccpb.KeyValue.GetCreateRevision.spec : Prop :=
  ∀ (p : Loc) (r : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb ∗ ⌜p ≠ null⌝ ∗
      structFieldRef mvccpb.KeyValue go!"CreateRevision" p ↦□ r }}
    (App (Val (p @!! go.GoType.PointerType mvccpb.KeyValue.ty @!! go!"GetCreateRevision")) (Val #()))
  {{ RET #r; True }}

end spec

end EtcdGrove
end Perennial
