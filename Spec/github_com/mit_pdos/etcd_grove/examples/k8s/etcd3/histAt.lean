/- Lean-first (no Rocq counterpart).

`histAt(h, r)` (k8setcd3.go): `histAtL` (`KList.lean`): the store at revision `r`. Its premise:
the nodes' lengths do not wrap.
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
abbrev histAt.spec : Prop :=
  ∀ (h : Loc) (hs : List GSt) (r : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ histOwn h hs ∗ ⌜hs.length < 2 ^ 64⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histAt)) (Val #h)) (Val #r))
  {{ (s : mstore), RET #s; storeOwn s (histAtL hs r) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
