/- Lean-first (no Rocq counterpart).

`histEqual(a, b)` (k8setcd3.go): whether the histories `a` and `b` hold the same stores (a
shared tail is equal). Its premise: the nodes' lengths do not wrap.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev histEqual.spec : Prop :=
  ∀ (a b : Loc) (ha hb : List GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ histOwn a ha ∗ histOwn b hb ∗ ⌜ha.length < 2 ^ 64 ∧ hb.length < 2 ^ 64⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histEqual)) (Val #a)) (Val #b))
  {{ RET #(decide (ha = hb)); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
