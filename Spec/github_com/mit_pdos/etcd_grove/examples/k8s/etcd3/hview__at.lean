/- Lean-first (no Rocq counterpart).

`v.at(r)` (export.go): what `histAt(v.h, r)` returns (`histAt`'s post): the store at revision `r`
(`histAtL`), from the view when `r` is in it. Its premise: `histAt`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.HView

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel hview)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev hview.at.spec : Prop :=
  ∀ (v : hview) (hs : List GSt) (r : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ hviewOwn v hs ∗
      ⌜hs.length < 2 ^ 64⌝ }}
    (App (Val (v @!! hview.ty @!! go!"at")) (Val #r))
  {{ (s : mstore), RET #s; storeOwn s (histAtL hs r) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
