/- Lean-first (no Rocq counterpart).

`(*histHashes).canonical(h)` (export.go): `canonLocked` under `hh.mu`.
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
abbrev histHashes.canonical.spec : Prop :=
  ∀ (hh h : Loc) (hs : List GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ hhOwn hh ∗ histOwn h hs ∗ ⌜hs.length < 2 ^ 64⌝ }}
    (App (Val (hh @!! go.GoType.PointerType histHashes.ty @!! go!"canonical")) (Val #h))
  {{ (c : Loc), RET #c; histOwn c hs }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
