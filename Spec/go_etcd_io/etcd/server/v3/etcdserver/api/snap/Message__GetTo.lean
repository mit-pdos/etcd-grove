/-
`m.GetTo()` (`etcdserver/api/snap/message.go`: the method of the embedded `*raftpb.Message`,
promoted; names only, `snap.Message` an axiomatized type): the raft message's destination. The
trust boundary (D22 S-h, 2026-10-20; an axiom in `Proof/.../snap/Message__GetTo.lean`). Lean-first
(no Rocq counterpart); the vocabulary is `Proof/.../snap/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI snap

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `m.GetTo()` of a merged message: some id (the sender only logs it). (prove-grpcsmall,
2026-11-20) With raftpb's package initialization in the precondition: the body is raftpb's getter,
promoted. -/
abbrev snap.Message.GetTo.spec : Prop :=
  ∀ (m ml : Loc) (rc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      msgIs (GF := GF) m ml rc }}
    (App (Val (m @!! go.GoType.PointerType
        _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message.ty @!!
        go!"GetTo")) (Val #()))
  {{ (to : w64), RET #to; True }}

end spec

end EtcdGrove
end Perennial
