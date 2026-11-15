/- Lean-first (no Rocq counterpart).

`encodeItems(items)` (k8setcd3.go): `encItemsL` (`Codec.lean`): the items' resource versions,
encodings' lengths and encodings, in order (the slice read-only).
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
abbrev encodeItems.spec : Prop :=
  ∀ (sl : GoSlice) (os : List Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ sl ↦*□ os }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeItems)) (Val #sl))
  {{ RET #(encItemsL os); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
