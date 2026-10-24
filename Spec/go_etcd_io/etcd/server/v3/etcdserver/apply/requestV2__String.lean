/-
`(*requestV2).String` (`legacy_request.go:92`): formats `RequestV2{ID:%d Method:%q Path:%q}`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Perennial.Proof.fmt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `r.String()` returns a formatted string (`fmt.SprintfOut`) without mutating `*r`. -/
abbrev apply.requestV2.String.spec : Prop :=
  ∀ (r_ptr : Loc) (r : requestV2) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      r_ptr ↦{dq} r }}
    (App (Val (r_ptr @!! go.GoType.PointerType requestV2.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s;
      r_ptr ↦{dq} r ∗
      ⌜_root_.Perennial.fmt.SprintfOut go!"RequestV2{ID:%d Method:%q Path:%q}"
        [interface.mkOk go.uint64 #r.ID',
         interface.mkOk go.string #r.Method',
         interface.mkOk go.string #r.Path'] s⌝ }}

end spec

end EtcdGrove
end Perennial
