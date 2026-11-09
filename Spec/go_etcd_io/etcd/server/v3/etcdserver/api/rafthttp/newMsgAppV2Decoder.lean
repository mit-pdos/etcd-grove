/-
## `newMsgAppV2Decoder(r, local, remote)`

**Users.** `streamReader.decodeLoop`.

**Proof sketch.** The literal and its buffers.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

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

/-- (internal) A msgappv2 decoder on `rd` for the stream from `remote` to `local`, at the initial state. -/
def newMsgAppV2Decoder.spec : Prop :=
  ∀ (rd : GoInterface) (lcl remote : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ True }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newMsgAppV2Decoder)) (Val #rd)) (Val #lcl)) (Val #remote))
  {{ (dec : Loc), RET #dec; v2DecAt dec rd remote lcl (W64 0, W64 0) }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
