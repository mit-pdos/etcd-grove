/- Lean-first (no Rocq counterpart).

`(*histHashes).intern(prev, st, n)` (export.go), `hh.mu` held: a node holding the history `prev`
holds with the store `st` appended (an equal node of `canon[prev, n, hash]`, or a new one, recorded).
The caller holds `hhCanon hh` (the lock's maps `canon` and `is`) and gets it back.
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
abbrev histHashes.intern.spec : Prop :=
  ∀ (hh prev : Loc) (hs : List GSt) (st : mstore) (s : GSt) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ hhCanon hh ∗ histOwn prev hs ∗ storeOwn st s ∗ ⌜uint.nat n = hs.length + 1⌝ }}
    (App (App (App (Val (hh @!! go.GoType.PointerType histHashes.ty @!! go!"intern")) (Val #prev)) (Val #st)) (Val #n))
  {{ (c : Loc), RET #c; hhCanon hh ∗ histOwn c (hs ++ [s]) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
