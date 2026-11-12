/- Lean-first (no Rocq counterpart).

`fieldSel.RequiresExactMatch(field)` (k8setcd3.go): the value of the first of the
selector's equalities on `field`, if any.
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
abbrev fieldSel.RequiresExactMatch.spec : Prop :=
  ∀ (s : fieldSel) (f : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.fieldSel.ty go!"RequiresExactMatch" #s)) (Val #f))
  {{ RET (PairV
        #(if 1 ≤ sint.Z s.n' ∧ s.f1' = f then s.v1'
          else if 2 ≤ sint.Z s.n' ∧ s.f2' = f then s.v2' else [])
        #(decide (1 ≤ sint.Z s.n' ∧ s.f1' = f) || decide (2 ≤ sint.Z s.n' ∧ s.f2' = f))); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
