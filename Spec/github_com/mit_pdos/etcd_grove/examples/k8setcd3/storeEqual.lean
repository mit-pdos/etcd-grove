/- Lean-first (no Rocq counterpart).

`storeEqual(a, b)` (k8setcd3.go): whether the stores `a` and `b` hold the same items and
resource version.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev storeEqual.spec : Prop :=
  ∀ (a b : mstore) (ga gb : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ storeOwn a ga ∗ storeOwn b gb }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.storeEqual)) (Val #a)) (Val #b))
  {{ RET #(decide (ga = gb)); True }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
