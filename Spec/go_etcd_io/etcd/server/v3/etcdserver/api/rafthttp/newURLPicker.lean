/-
## `newURLPicker(urls)`

**Users.** `startPeer`, `startRemote`.

**Proof sketch.** The literal; its mutex invariant over `urls` (with `urlsAt`, non-empty) and `picked < len(urls)`.

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

/-- (internal) A picker over URLs whose hosts are peer addresses (non-empty). -/
def newURLPicker.spec : Prop :=
  ∀ (ν : Net GF) (urls : GoSlice) (hs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ Types.urlsAt urls hs ∗ ⌜hs ≠ []⌝ ∗ ([∗list] a ∈ hs, peerAddr ν a) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newURLPicker)) (Val #urls))
  {{ (pk : Loc), RET #pk; pickerAt pk ν }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
