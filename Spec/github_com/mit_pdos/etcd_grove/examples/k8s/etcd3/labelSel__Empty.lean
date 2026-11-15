/- Lean-first (no Rocq counterpart).

`labelSel.Empty()` (k8setcd3.go): everything (`all`).
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
abbrev labelSel.Empty.spec : Prop :=
  ∀ (s : labelSel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.labelSel.ty go!"Empty" #s)) (Val #()))
  {{ RET #s.all'; True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
