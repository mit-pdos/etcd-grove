/- Lean-first (no Rocq counterpart).

`noCluster{}.Version()` (`examples/mvccrand/mvccrand.go`): `nil`, no version known (the lessor's
cluster: `lease.clusterOk` of `noCluster{}` follows, its `Version` returning).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev noCluster.Version.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val #(methods noCluster.ty go!"Version" #(noCluster.mk))) (Val #()))
  {{ (v : Loc), RET #v; ⌜v = null⌝ }}

end spec

end mvccrand
end EtcdGrove
end Perennial
