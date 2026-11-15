/-
`(*etcdserverpb.AlarmType).String()` (`api/etcdserverpb/rpc.pb.go`, generated, names only here:
assumed; `protoimpl.X.EnumStringOf`).

Users: the apply's alarm logging (`server/etcdserver/apply/backend.go:124,131`:
`m.Alarm.String()`, through the field's address).

Why true: it reads `*p` and looks the value up in the enum's descriptor (built at package
initialization), returning its name, else the number in decimal: ASCII either way (the names are
`NONE`, `NOSPACE`, `CORRUPT`).

Changes: verify-round: restored (A6 completeness F6: dropped from the old tree,
`specs-ref/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/AlarmType__String.lean`), the ASCII fact stated
byte-wise (the old `asciiStr` is gone).
Margin: the string is the value's name; the spec says only that it is ASCII.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI
open go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `(*p).String()`: an ASCII string, reading `*p`. -/
def AlarmType.String.spec : Prop :=
  ∀ (p : Loc) (a : w32) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ p ↦{dq} a }}
    (App (Val (p @!! go.GoType.PointerType etcdserverpb.AlarmType.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; p ↦{dq} a ∗ ⌜∀ b ∈ s, uint.nat b < 128⌝ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
