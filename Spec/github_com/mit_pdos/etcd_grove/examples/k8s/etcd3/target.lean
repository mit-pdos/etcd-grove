/- Lean-first (no Rocq counterpart).

`target(in, out, rv)` (export.go, notes/k8s-dist-k9.md §2.5): exactly `targetL` (`dist/SharedSearch.lean`),
as a `uint64` (every value it names is one).
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
abbrev target.spec : Prop :=
  ∀ (x : Input) (y : Output) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.target)) (Val #x)) (Val #y)) (Val #rv))
  {{ (t : w64), RET #t; ⌜uint.nat t = k8s_dist.targetL x y (uint.nat rv)⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
