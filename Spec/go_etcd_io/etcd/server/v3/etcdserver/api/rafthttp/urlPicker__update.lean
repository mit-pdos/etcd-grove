/-
## `(*urlPicker).update(urls)`

**Users.** `peer.update`.

**Proof sketch.** Under `mu`: the URLs, `picked = 0`.

**Changes.** New (no old spec).

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

/-- (internal) Replaces the URLs (non-empty, peer addresses). -/
def urlPicker.update.spec : Prop :=
  ∀ (ν : Net GF) (pk : Loc) (urls : GoSlice) (hs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ pickerAt pk ν ∗ urlsAt urls hs ∗ ⌜hs ≠ []⌝ ∗ ([∗list] a ∈ hs, peerAddr ν a) }}
    (App (Val (pk @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.urlPicker.ty @!! go!"update")) (Val #urls))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
