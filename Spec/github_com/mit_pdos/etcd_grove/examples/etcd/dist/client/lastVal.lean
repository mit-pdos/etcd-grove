/- Lean-first (no Rocq counterpart). `lastVal(evs, key, r)` (`examples/etcd/dist/client/watch.go`):
copy of the cache example's `lastVal` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/cache/lastVal.lean`),
at the dist package's copy in `watch.go`: the same triple (`etcd_cache.lastValL`), the function and
package initializer the dist package's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CacheBase
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CacheGetCheck

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
abbrev lastVal.spec : Prop :=
  ∀ (sl : GoSlice) (evs : List etcd_cache.cev) (dq : DFrac) (key : GoString) (r : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      sl ↦*{dq} evs }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.lastVal)) (Val #sl))
      (Val #key)) (Val #r))
  {{ (v : GoString) (ok : Bool), RET (PairV #v #ok);
      sl ↦*{dq} evs ∗ ⌜(if ok then some v else none) = etcd_cache.lastValL evs key r⌝ }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
