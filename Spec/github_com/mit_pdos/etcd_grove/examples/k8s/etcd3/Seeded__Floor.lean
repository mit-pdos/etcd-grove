/-
Lean-first (no Rocq counterpart).

`Seeded.Floor()` (`examples/k8s/etcd3/export.go`; k8s-dist K9 step 5): the seeded store's revision, the floor of the drawn resource versions.

-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev Seeded.Floor.spec : Prop :=
  ∀ (s : Seeded),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val #(methods Seeded.ty go!"Floor" #s)) (Val #()))
  {{ RET #(s.st0'.rv'); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
