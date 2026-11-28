/- Lean-first (no Rocq counterpart).

`(*cfgSet).add(c)` (export.go, notes/k8s-dist-k9.md §2.3): `c` added to the set (its history node made
canonical), unless a configuration with the same history node, store and pending inputs is in it
already (`false`: then `c`'s configuration is in the set).
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
abbrev cfgSet.add.spec : Prop :=
  ∀ (s hh : Loc) (gs : List GCfg) (c : mcfg) (g : GCfg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ hhOwn hh ∗ cfgSetOwn s hh gs ∗ cfgOwn c g }}
    (App (Val (s @!! go.GoType.PointerType cfgSet.ty @!! go!"add")) (Val #c))
  {{ (b : Bool), RET #b; if b then cfgSetOwn s hh (gs ++ [g]) else cfgSetOwn s hh gs ∗ ⌜g ∈ gs⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
