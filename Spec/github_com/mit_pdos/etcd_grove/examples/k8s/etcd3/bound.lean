/- Lean-first (no Rocq counterpart).

`bound(in, out)` (export.go, notes/k8s-dist-k9.md §2.5): exactly `boundL` (`SharedLand.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedLand

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
abbrev bound.spec : Prop :=
  ∀ (x : Input) (y : Output),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.bound)) (Val #x)) (Val #y))
  {{ RET #(boundL x y); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
