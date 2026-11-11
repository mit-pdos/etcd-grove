/- Lean-first (no Rocq counterpart).

`histLen(h)` (k8setcd3.go): the length of the history `h` holds (its stores' count, as the
newest node records it).
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
abbrev histLen.spec : Prop :=
  ∀ (h : Loc) (hs : List GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ histOwn h hs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histLen)) (Val #h))
  {{ RET #(W64 (hs.length : Int)); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
