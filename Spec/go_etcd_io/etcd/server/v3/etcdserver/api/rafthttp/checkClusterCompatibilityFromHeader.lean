/-
## `checkClusterCompatibilityFromHeader(lg, localID, header, cid)`

**Users.** the three handlers.

**Proof sketch.** `Header.Get`s, `serverVersion`, `minClusterVersion`, `checkVersionCompatibility`, `ID.String` (1c).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** A request from a non-member with a malformed version header panics the handler, which `Serve` recovers (outside the closed world).
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

/-- (internal) **Checks a request's version and cluster headers**: `nil`, `errIncompatibleVersion` or `ErrClusterIDMismatch`. The version headers parse (`semver.MustParse` panics otherwise: a member's request sets them to its own versions). -/
def checkClusterCompatibilityFromHeader.spec : Prop :=
  ∀ (lg : Loc) (localID : w64) (hm : GoInterface) (hs : List (GoString × GoString)) (cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ Http.hdrRO hm hs ∗ ⌜verHdrOk (Http.hdrGet hs go!"X-Server-Version") ∧ verHdrOk (Http.hdrGet hs go!"X-Min-Cluster-Version")⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkClusterCompatibilityFromHeader)) (Val #lg)) (Val #localID)) (Val #hm)) (Val #cid))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∨ errIs go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.errIncompatibleVersion err ∨ errIs go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.ErrClusterIDMismatch err }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
