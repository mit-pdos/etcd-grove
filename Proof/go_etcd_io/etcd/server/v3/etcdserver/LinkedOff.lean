/-
The server's linked results at auth off, for the off-only callers outside the server (the auth
component's stage 2, 2026-11-04): the linked spec is the merged one, over the component `C`
(`Link.lean`), and these callers keep its off corollary (`ModeSpecs.lean`), until they move to the
merged spec (stage 3). The examples' Links take them as `=` callees (`etc/gen-link.py`'s
`EXTRA_IMPORTS`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`Start` with auth off**, linked: `Start.spec_off` of the linked `EtcdServer.wp_Start`. -/
theorem EtcdServer.wp_Start_off [go_etcd_io.etcd.cache.v3.Assumptions] :
    EtcdServer.Start.specOff (GF := GF) (hG := hG) :=
  EtcdServer.Start.spec_off EtcdServer.wp_Start

end linked

end EtcdGrove
end Perennial
