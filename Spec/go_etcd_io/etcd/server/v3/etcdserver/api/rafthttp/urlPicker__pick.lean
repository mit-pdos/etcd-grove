/-
## `(*urlPicker).pick()`

**Users.** `pipeline.post`, `streamReader.dial`, `snapshotSender.send`.

**Proof sketch.** Under `mu`: `urls[picked]` (in bounds by the invariant).

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

/-- (internal) **The current URL**: its host a peer address, a URL `NewRequest` accepts. -/
def urlPicker.pick.spec : Prop :=
  ∀ (ν : Net) (pk : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ pickerAt pk ν }}
    (App (Val (pk @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.urlPicker.ty @!! go!"pick")) (Val #()))
  {{ (u : _root_.Perennial.net.url.URL), RET #u; peerAddr ν u.Host' ∗ ⌜Http.urlOk u⌝ }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
