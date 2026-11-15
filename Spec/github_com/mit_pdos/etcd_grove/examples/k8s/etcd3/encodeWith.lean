/- Lean-first (no Rocq counterpart).

`encodeWith(tag, o)` (k8setcd3.go): the encoding `encodeWith tag o` (the tag, the namespace, name,
UID, node and app as length-prefixed fields, the value), in a new slice.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev encodeWith.spec : Prop :=
  ∀ (tag : GoString) (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeWith)) (Val #tag)) (Val #v))
  {{ (sl : GoSlice), RET #sl; sl ↦* encodeWith tag v }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
