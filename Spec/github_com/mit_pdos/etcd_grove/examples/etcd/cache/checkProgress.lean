/- Lean-first (no Rocq counterpart).

`checkProgress(evs, p)` (etcd_cache.go): panics unless the progress notification's revision `p` is
at most the last event's revision (`1` if none). For events at revisions `2, 3, ...`, the last
one's is `1` plus their number, so it does not panic when `p` is at most that (`awaitProgress`'s
post).
-/
module

public import Code.github_com.mit_pdos.etcd_grove.examples.etcd.cache
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.cache.lastVal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_cache

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.cache.Assumptions]

/-- See the file header. -/
abbrev checkProgress.spec : Prop :=
  ∀ (sl : GoSlice) (evs : List cev) (p : w64),
  (∀ (i : Nat) (e : cev), evs[i]? = some e → sint.Z e.Rev' = 2 + i) →
  sint.Z p ≤ 1 + evs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.cache ∗
      sl ↦*□ evs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.cache.checkProgress)) (Val #sl))
      (Val #p))
  {{ RET #(); True }}

end spec

end etcd_cache
end EtcdGrove
end Perennial
