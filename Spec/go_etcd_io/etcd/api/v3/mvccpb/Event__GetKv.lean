/-
`(*mvccpb.Event).GetKv()` (`api/mvccpb/kv.pb.go`, translated for the etcd3 watcher's `parseEvent`, through `IsCreate`, k8s 7f-5a-P): on a non-nil `*Event`, its `Kv` field. Lean-first (no Rocq counterpart).
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
abbrev mvccpb.Event.GetKv.spec : Prop :=
  ∀ (p : Loc) (kv : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb ∗ ⌜p ≠ null⌝ ∗
      structFieldRef mvccpb.Event go!"Kv" p ↦□ kv }}
    (App (Val (p @!! go.GoType.PointerType mvccpb.Event.ty @!! go!"GetKv")) (Val #()))
  {{ RET #kv; True }}

end spec

end EtcdGrove
end Perennial
