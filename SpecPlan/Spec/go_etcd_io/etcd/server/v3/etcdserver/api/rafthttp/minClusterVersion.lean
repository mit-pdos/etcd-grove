/-
## `minClusterVersion(h)`

**Users.** `checkClusterCompatibilityFromHeader`.

**Proof sketch.** `Header.Get`, `semver.MustParse` (trust: semver; it parses what `verHdrOk` says).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** A malformed header panics: `issues/etcd-rafthttp-stream-dial-bad-server-version-panic.md` (the premise is met between members).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

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

/-- (internal) The `X-Min-Cluster-Version` header as a version (`2.0.0` if absent); its value must parse (`MustParse`). -/
def minClusterVersion.spec : Prop :=
  ∀ (hm : GoMap) (hs : List (GoString × GoString)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ Http.hdrRO hm hs ∗ ⌜verHdrOk (Http.hdrGet hs go!"X-Min-Cluster-Version")⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.minClusterVersion)) (Val #hm))
  {{ (v : Loc), RET #v; semverAt v }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
