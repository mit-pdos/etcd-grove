/-
`(*Options).String()` (`db.go`): `fmt.Sprintf` of the fields, the logger with `%p`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) some string. -/
def Options.String.spec : Prop :=
  ∀ [HasExt osFsExt] (l : Loc) (dq : DFrac) (o : OptsM),
  {{ optsAt (GF := GF) l dq o ∗ ⌜loggerPtrOk o.logger⌝ }}
    (App (Val (l @!! go.GoType.PointerType Options.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; optsAt l dq o }}

end spec

end Bbolt
end EtcdGrove
end Perennial
