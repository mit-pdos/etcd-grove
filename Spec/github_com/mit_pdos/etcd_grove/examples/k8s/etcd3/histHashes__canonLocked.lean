/- Lean-first (no Rocq counterpart).

`(*histHashes).canonLocked(h)` (export.go), `hh.mu` held: a node holding `h`'s history (its
canonical node: `h`'s nodes back to the first recorded one, re-interned).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (mstore mcfg hnode Input histHashes cfgSet)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev histHashes.canonLocked.spec : Prop :=
  ∀ (hh h : Loc) (hs : List GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ hhInv hh ∗ histOwn h hs ∗ ⌜hs.length < 2 ^ 64⌝ }}
    (App (Val (hh @!! go.GoType.PointerType histHashes.ty @!! go!"canonLocked")) (Val #h))
  {{ (c : Loc), RET #c; hhInv hh ∗ histOwn c hs }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
