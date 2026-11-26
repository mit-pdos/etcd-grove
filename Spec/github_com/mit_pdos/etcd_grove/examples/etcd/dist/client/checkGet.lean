/- Lean-first (no Rocq counterpart). `checkGet(evs, r, kvs)` (`examples/etcd/dist/client/watch.go`):
copy of the cache example's `checkGet` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/cache/checkGet.lean`),
at the dist package's copy in `watch.go`: the same triple (`etcd_cache.CheckGetOk`, `hasKey`'s
`kvsHold`), the function and package initializer the dist package's.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.hasKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.lastVal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
abbrev checkGet.spec : Prop :=
  ∀ (esl : GoSlice) (evs : List etcd_cache.cev) (r : w64) (ksl : GoSlice) (ps : List Loc)
    (s : List EtcdKv),
  etcd_cache.CheckGetOk evs r s →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      esl ↦*□ evs ∗ ksl ↦*□ ps ∗ kvsHold ps s }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checkGet)) (Val #esl))
      (Val #r)) (Val #ksl))
  {{ RET #(); True }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
