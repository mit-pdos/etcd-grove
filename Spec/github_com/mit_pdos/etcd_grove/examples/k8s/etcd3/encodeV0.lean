/- Lean-first (no Rocq counterpart).

`encodeV0(name, val)` (k8s_etcd3.go): the older encoding, `encodeWith(tagV0, name, val)`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev encodeV0.spec : Prop :=
  ∀ (name uid val : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeV0)) (Val #name)) (Val #uid)) (Val #val))
  {{ (sl : GoSlice), RET #sl; sl ↦* encodeWith tagV0 name uid val }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
