/-
`(*requestV2).Unmarshal` (`legacy_request.go:44`): unmarshals a legacy v2 `Request` protobuf wire
encoding into `*r`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

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

/-- `r.Unmarshal(data)` decodes `bs` according to the wire-format loop `apply.v2Decode bs`:
if `apply.v2Decode bs = some r`, it returns `nil` and stores `r` at `r_ptr`;
if `apply.v2Decode bs = none`, it returns a non-nil `error` and leaves `r_ptr` writable. -/
abbrev apply.requestV2.Unmarshal.spec : Prop :=
  ∀ (r_ptr : Loc) (r0 : requestV2) (data : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      r_ptr ↦ r0 ∗ data ↦*{dq} bs }}
    (App (Val (r_ptr @!! go.GoType.PointerType requestV2.ty @!! go!"Unmarshal")) (Val #data))
  {{ (err : GoInterface), RET #err;
      data ↦*{dq} bs ∗
      match apply.v2Decode bs with
      | some r => ⌜err = GoInterface.nil⌝ ∗ r_ptr ↦ r
      | none => ⌜err ≠ GoInterface.nil⌝ ∗ ∃ r' : requestV2, r_ptr ↦ r' }}

end spec

end EtcdGrove
end Perennial
