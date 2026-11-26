/- Lean-first (no Rocq counterpart). `checkProgress(evs, p)` (`examples/etcd/dist/client/watch.go`):
copy of the cache example's `checkProgress` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/cache/checkProgress.lean`),
at the dist package's copy in `watch.go`: the same triple, the function and package initializer the
dist package's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.Defs

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
abbrev checkProgress.spec : Prop :=
  ∀ (sl : GoSlice) (evs : List etcd_cache.cev) (p : w64),
  (∀ (i : Nat) (e : etcd_cache.cev), evs[i]? = some e → sint.Z e.Rev' = 2 + i) →
  sint.Z p ≤ 1 + evs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      sl ↦*□ evs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checkProgress)) (Val #sl))
      (Val #p))
  {{ RET #(); True }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
