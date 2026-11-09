/-
## `compareMajorMinorVersion(a, b)`

**Users.** `checkVersionCompatibility`, `streamReader.dial`.

**Proof sketch.** `semver.New`, `LessThan` (trust: semver, pure).

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

/-- (internal) Compares two versions' major and minor numbers: `-1`, `0` or `1`. -/
def compareMajorMinorVersion.spec : Prop :=
  ∀ (a b : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ semverAt a ∗ semverAt b }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.compareMajorMinorVersion)) (Val #a)) (Val #b))
  {{ (n : w64), RET #n; ⌜sint.Z n = -1 ∨ sint.Z n = 0 ∨ sint.Z n = 1⌝ }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
