/-
`snap.NewMessage(rs, rc, rcSize)` (`etcdserver/api/snap/message.go`; names only): the merged
snapshot message of the raft message `rs` and the reader `rc` of `rcSize` bytes. The trust
boundary (D22 S-h, 2026-10-20; an axiom in `Proof/.../snap/NewMessage.lean`). Lean-first (no Rocq
counterpart); the vocabulary is `Proof/.../snap/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import Proof.go_etcd_io.raft.v3.InvPb
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI snap

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- `snap.NewMessage(ml, rc, sz)` of a read-only raft message `ml` (`proto.Size` reads it): a
fresh `*snap.Message` `m` of `ml` and `rc` (`msgIs`, read-only for good), its `TotalSize` field
read-only at some value (`proto.Size(ml) + sz`, which the sender only logs), and its `closeC`, a
fresh channel of booleans (`msgCloseC`) whose receives carry nothing (`isChanBag` at `True`: the
transport's `CloseWithError` sends on it once, its success). -/
abbrev snap.NewMessage.spec : Prop :=
  ∀ (ml : Loc) (st : MsgSt) (rc : GoInterface) (sz : w64),
  {{ msgOwn (GF := GF) ml DFrac.discard st }}
    (App (App (App (Val (@! _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.NewMessage))
      (Val #ml)) (Val #rc)) (Val #sz))
  {{ (m : Loc), RET #m;
      msgIs m ml rc ∗ ∃ (tsz : w64) (c : Loc) (γc : ChanNames),
        structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message
          go!"TotalSize" m ↦□ tsz ∗
        msgCloseC m c ∗ isChanBag γc c (V := Bool) (fun _ => iprop(True)) }}

end spec

end EtcdGrove
end Perennial
