/- Lean-first (no Rocq counterpart).

`configEqual(a, b)` (k8setcd3.go): whether the configurations `a` and `b` hold the same
contents.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8setcd3


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev configEqual.spec : Prop :=
  ∀ (a b : mcfg) (ga gb : GCfg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ cfgOwn a ga ∗ cfgOwn b gb }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.configEqual)) (Val #a)) (Val #b))
  {{ RET #(decide (ga = gb)); True }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
