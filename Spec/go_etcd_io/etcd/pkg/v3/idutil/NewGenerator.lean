/-
## `idutil.NewGenerator(memberID, now)`

**Users.** `etcdserver.NewServer` (`server.go:327`: `NewGenerator(uint16(b.cluster.nodeID),
time.Now())`, once per run). Snippet: `examples/specreq/wait/idutil.go` (`ReqIdsDistinct`).

**Proof sketch.** Allocates the struct (`prefix = memberID << 48`, `suffix = lowbit(ms, 40) << 8`,
`lowbit.spec`); allocates the generator's invariant (its prefix's issued-ids count and the token
`idPrefix γi memberID`, which the realization of `idFresh` uses to tie issued ids to this run).

**Changes.** The old spec (`specs-ref`'s `NewGenerator.lean`) took the cluster's claims map, a
per-prefix fact family `Φs`, the member's share and an incarnation key, and gave a generator
carrying the claimers' facts: the request path's bookkeeping. Restated over the id space only: a
token per run in, a generator out; what an id is claimed for is the client's (the server's
invariant), keyed by `idFresh`.

**Margin.** The ids' values (prefix, suffix) are not exposed: no user inspects them.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace IdUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.idutil.Assumptions]

/-- **A generator of the id space `γi`**, for one run of the member owning the prefix `memberID`. -/
def NewGenerator.spec : Prop :=
  ∀ (γi : IdSpace) (memberID : w16) (now : time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil ∗ idPrefix γi memberID }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.idutil.NewGenerator)) (Val #memberID)) (Val #now))
  {{ (g : Loc), RET #g; idGen g γi }}

end spec
end IdUtil
end EtcdGrove
end Perennial
