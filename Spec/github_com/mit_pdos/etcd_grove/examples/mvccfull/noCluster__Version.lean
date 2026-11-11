/- Lean-first (no Rocq counterpart).

`noCluster{}.Version()` (`examples/mvccfull/mvccfull.go`): `nil`, no version known (the lessor's
cluster: `lease.clusterOk` of `noCluster{}` follows, its `Version` returning).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev noCluster.Version.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val #(methods noCluster.ty go!"Version" #(noCluster.mk))) (Val #()))
  {{ (v : Loc), RET #v; ⌜v = null⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
