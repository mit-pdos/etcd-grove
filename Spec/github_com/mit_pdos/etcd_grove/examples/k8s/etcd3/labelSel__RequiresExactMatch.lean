/- Lean-first (no Rocq counterpart).

`labelSel.RequiresExactMatch(label)` (k8setcd3.go): the selector's `app`, for the label
`app` of a selector that is not everything.
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
abbrev labelSel.RequiresExactMatch.spec : Prop :=
  ∀ (s : labelSel) (l : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.labelSel.ty go!"RequiresExactMatch" #s)) (Val #l))
  {{ RET (PairV #(if !s.all' ∧ l = go!"app" then s.app' else [])
        #(decide (!s.all' ∧ l = go!"app"))); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
