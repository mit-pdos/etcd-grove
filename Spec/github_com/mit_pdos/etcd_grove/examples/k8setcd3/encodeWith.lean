/- Lean-first (no Rocq counterpart).

`encodeWith(tag, name, val)` (k8setcd3.go): the encoding `encodeWith tag name val` (the tag, the
name's length byte, the name, the value), in a new slice.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev encodeWith.spec : Prop :=
  ∀ (tag name val : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.encodeWith))
      (Val #tag)) (Val #name)) (Val #val))
  {{ (sl : GoSlice), RET #sl; sl ↦* encodeWith tag name val }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
