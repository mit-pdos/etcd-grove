/-
## `addPeerToProber(lg, p, id, us, roundTripperName, rttSecProm)`

**Users.** `Transport.AddPeer`, `UpdatePeer`.

**Proof sketch.** Assumed: `probing.Prober.AddHTTP` and the `monitorProbingStatus` goroutine affect nothing the program reads (their only effects are logs and metrics).

**Changes.** Unchanged in substance (names-only before).

**Margin.** None.
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

/-- (trust boundary: untranslated; the probes) Registers the peer's URLs with a prober (its goroutine only measures and logs). -/
def addPeerToProber.spec : Prop :=
  ∀ (lg : Loc) (p : GoInterface) (id : GoString) (sl : GoSlice) (us : List GoString) (name : GoString) (rtt : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ proberAt p ∗ sl ↦*{DFrac.discard} us }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.addPeerToProber)) (Val #lg)) (Val #p)) (Val #id)) (Val #sl)) (Val #name)) (Val #rtt))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
