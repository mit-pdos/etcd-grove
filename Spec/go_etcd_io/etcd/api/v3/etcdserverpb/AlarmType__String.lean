/-
`etcdserverpb.AlarmType.String`: the trust boundary (`etcdserverpb` is names-only for its methods). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `(*p).String()` (`m.Alarm.String()`, through the field's address) returns some string,
reading `*p`. -/
abbrev etcdserverpb.AlarmType.String.spec : Prop :=
  ∀ (p : Loc) (a : w32) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ p ↦{dq} a }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.AlarmType.ty
      @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; p ↦{dq} a }}

end spec

end EtcdGrove
end Perennial
