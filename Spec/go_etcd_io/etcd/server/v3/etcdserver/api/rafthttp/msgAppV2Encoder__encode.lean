/-
## `(*msgAppV2Encoder).encode(m)`

**Users.** `streamWriter.run` (the msgappv2 stream).

**Proof sketch.** `isLinkHeartbeatMessage`; an `AppEntries` frame when `index`, `logTerm`, `term` match the state (the entries' sizes and encodings, `MarshalAppend` into the buffer, the commit), else a full frame (`binary.Write`, `proto.Size`, `MustMarshalMessage`) and the state from the message; `FollowerStats.Succ` (2e: no-op). The shape premise is what makes the short frame's decoding equal `m` (`sendable`). The full frame's next state is the last entry's `GetIndex()`, which `msgPts_msgAt`'s `msgWf` (entries numbered from `Index + 1`) makes `m.index + |m.entries|`, `v2Frame`'s.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. verify-round (A8 F8): `v2Frame` transparent (was opaque); the premise adds `dst ≠ 0` (a peer's id, which `msgChanAt` carries: `peer.send` takes `m.to ≠ 0`), without which `sendable` says nothing and the short frame would not be `v2Frame`'s. verify-round (R-A8 S3): the sketch says where the full frame's consecutive indexes come from (`msgPts`'s `msgWf`); no premise added, statement unchanged.

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

/-- (internal) **Writes a msgappv2 frame** of a link heartbeat or a `MsgApp` of raft's shape from `src` to `dst`, with the writer's permission for every prefix of a frame of it; the state moves on success. -/
def msgAppV2Encoder.encode.spec : Prop :=
  ∀ (enc : Loc) (w : GoInterface) (src dst : w64) (st : w64 × w64) (Ok : List w8 → IProp GF) (bs : List w8) (ml : Loc) (dq : DFrac) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ v2EncAt enc w src dst st ∗ writerAt w Ok bs ∗ msgPts ml dq m ∗ ⌜isLinkHeartbeat m ∨ (m.type = MsgApp ∧ m.to = dst ∧ dst ≠ W64 0 ∧ sendable src m)⌝ ∗ □ (∀ fb st' ys, ⌜v2Frame st src dst m fb st' ∧ ys <+: fb⌝ -∗ Ok (bs ++ ys)) }}
    (App (Val (enc @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder.ty @!! go!"encode")) (Val #ml))
  {{ (err : GoInterface), RET #err; msgPts ml dq m ∗ Http.errOk err ∗ ∃ bs' st', v2EncAt enc w src dst st' ∗ writerAt w Ok bs' ∗ ⌜err = interface.nil → ∃ fb, v2Frame st src dst m fb st' ∧ bs' = bs ++ fb⌝ }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
