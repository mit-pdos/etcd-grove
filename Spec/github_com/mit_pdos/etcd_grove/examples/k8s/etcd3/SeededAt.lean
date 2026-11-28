/-
Lean-first (no Rocq counterpart).

`SeededAt(r1, r2)` (`examples/k8s/etcd3/export.go`; k8s-dist K9 §2.8, `SeedShared`'s pure half): the
seeded store `SeedShared` makes when its two Puts get the revisions `r1 < r2`, without a cluster. It
holds `seedSharedL r1 r2` (the empty store at revision 1, each revision between the seeds the store
before it, the seeds at `r1` and `r2`), which `seedSharedL_ok` shows is a seeded store as
`Seeded.SharedModel` takes it (its history slice owned: persist it for `SharedModel`). For `1 < r1 < r2 < 2^63` (the history has `r2` stores).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SeedSharedDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Seeded mstore)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev SeededAt.spec : Prop :=
  ∀ (r1 r2 : w64), 1 < uint.nat r1 → uint.nat r1 < uint.nat r2 → uint.nat r2 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SeededAt)) (Val #r1))
      (Val #r2))
  {{ (s : Seeded), RET #s; ∃ hs : List mstore, storeOwn s.st0' (seedSharedL r1 r2).st ∗
      s.h0' ↦* hs ∗ [∗list] x;g ∈ hs;(seedSharedL r1 r2).hist, storeOwn x g }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
