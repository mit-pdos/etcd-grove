/-
## `(*messageEncoder).encode(m)`

**Users.** `streamWriter.run` (the message stream), `createSnapBody` (the snapshot envelope).

**Proof sketch.** `proto.Size` (3h), `binary.Write` of a `uint64` (Perennial's `encoding/binary`, translated), `pbutil.MustMarshalMessage` (an encoding of the size computed), the writer's `Write`s (each a prefix of the frame).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. verify-round (A8 F8): raftpb's `msgEncodes` (was `pbEncodes`), the transparent `msgFrame`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) **Writes a message's frame** (its encoding's length, eight bytes big-endian, then the encoding), with the writer's permission for every frame of an encoding of it; on an error, some prefix may have been written. -/
def messageEncoder.encode.spec : Prop :=
  ∀ (enc : Loc) (w : GoInterface) (Ok : List w8 → IProp GF) (bs : List w8) (ml : Loc) (dq : DFrac) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ msgEncAt enc w ∗ writerAt w Ok bs ∗ msgPts ml dq m ∗ □ (∀ e ys, ⌜RaftPb.msgEncodes e m ∧ ys <+: msgFrame e⌝ -∗ Ok (bs ++ ys)) }}
    (App (Val (enc @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageEncoder.ty @!! go!"encode")) (Val #ml))
  {{ (err : GoInterface), RET #err; msgPts ml dq m ∗ Http.errOk err ∗ ∃ bs', writerAt w Ok bs' ∗ ⌜err = interface.nil → ∃ e, RaftPb.msgEncodes e m ∧ bs' = bs ++ msgFrame e⌝ }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
