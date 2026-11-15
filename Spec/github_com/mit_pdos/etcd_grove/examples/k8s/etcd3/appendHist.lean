/- Lean-first (no Rocq counterpart).

`appendHist(h, s)` (k8setcd3.go): a new history node, holding `h`'s stores and the store `s`
holds (`h` is shared, not changed).
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
abbrev appendHist.spec : Prop :=
  ∀ (h : Loc) (hs : List GSt) (s : mstore) (g : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ histOwn h hs ∗ storeOwn s g }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.appendHist)) (Val #h)) (Val #s))
  {{ (h' : Loc), RET #h'; histOwn h' (hs ++ [g]) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
