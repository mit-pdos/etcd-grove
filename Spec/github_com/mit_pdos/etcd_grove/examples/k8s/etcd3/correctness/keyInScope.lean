/- Lean-first (no Rocq counterpart).

`keyInScope(key, recursive, k)` (`correctness/model.go`, the checker's copy of the driver's text):
`keyInScopeL` (`KList.lean`), the driver's (k8s 7g step 3).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI k8s_etcd3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]

/-- See the file header. -/
abbrev keyInScope.spec : Prop :=
  ∀ (key : GoString) (r : Bool) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.keyInScope))
      (Val #key)) (Val #r)) (Val #k))
  {{ RET #(keyInScopeL key r k); True }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
