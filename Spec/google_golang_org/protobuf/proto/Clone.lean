/-
`proto.Clone`: the trust boundary (protobuf's `proto` is names-only), for the one message
`clientv3` clones, a `*pb.Compare` (`cloneCompare`). Lean-first (no Rocq counterpart); see
`InvCmp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvCmp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.protobuf.proto.Assumptions]

/-- `proto.Clone(c)` of a `*pb.Compare` holding `m` (as a `proto.Message`): a deep copy, a fresh
`*pb.Compare` holding `m`, owned (`compareOwn`). -/
abbrev proto.Clone.spec : Prop :=
  ∀ (p : Loc) (m : CmpModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ compareAt p m ∗
      ⌜p ≠ null⌝ }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.Compare.ty) #p)))
  {{ (p' : Loc), RET #(interface.mkOk (go.GoType.PointerType etcdserverpb.Compare.ty) #p');
      ⌜p' ≠ null⌝ ∗ compareOwn p' m }}

end spec

end EtcdGrove
end Perennial
