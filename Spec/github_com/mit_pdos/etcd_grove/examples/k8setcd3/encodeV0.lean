/- Lean-first (no Rocq counterpart).

`encodeV0(name, val)` (k8setcd3.go): the older encoding, `encodeWith(tagV0, name, val)`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev encodeV0.spec : Prop :=
  ∀ (name val : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.encodeV0)) (Val #name)) (Val #val))
  {{ (sl : GoSlice), RET #sl; sl ↦* encodeWith tagV0 name val }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
