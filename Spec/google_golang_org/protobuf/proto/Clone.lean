/-
`proto.Clone`: the trust boundary (protobuf's `proto` is names-only), a case per message type
cloned: `clientv3`'s `*pb.Compare` (`cloneCompare`), and the server's raft wrapper's nil
`*raftpb.Snapshot` (raft v3.7's; 2026-10-12). Lean-first (no Rocq counterpart); see
`InvCmp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvCmp
public import EtcdDeps.Code.go_etcd_io.raft.v3.raftpb

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
`*pb.Compare` holding `m`, owned (`compareOwn`). Of a nil `*raftpb.Snapshot` (an invalid
message): a nil `*raftpb.Snapshot` (protobuf: "if the top-level message is invalid, it returns
an invalid message as well"). -/
abbrev proto.Clone.spec : Prop :=
  (∀ (p : Loc) (m : CmpModel),
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ compareAt p m ∗
        ⌜p ≠ null⌝ }}
      (App (Val (@! google_golang_org.protobuf.proto.Clone))
        (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.Compare.ty) #p)))
    {{ (p' : Loc), RET #(interface.mkOk (go.GoType.PointerType etcdserverpb.Compare.ty) #p');
        ⌜p' ≠ null⌝ ∗ compareOwn p' m }}) ∧
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.Snapshot.ty)
        #(null : Loc))))
  {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.Snapshot.ty)
      #(null : Loc)); True }}

end spec

end EtcdGrove
end Perennial
