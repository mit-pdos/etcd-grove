/-
## `waitSchedule()`

**Users.** `pipeline.post`'s canceller.

**Proof sketch.** Assumed: `runtime.Gosched` yields and returns.

**Changes.** Unchanged (was an accepted trust item).

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

/-- (trust boundary: untranslated, `runtime.Gosched()`) Returns. -/
def waitSchedule.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ True }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.waitSchedule)) (Val #()))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
