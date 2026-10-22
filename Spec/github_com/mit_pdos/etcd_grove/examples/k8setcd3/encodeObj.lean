/- Lean-first (no Rocq counterpart).

`encodeObj(o)` (k8setcd3.go): the current encoding of the object at `o` (`encodeWith tagV1`).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev encodeObj.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (name val : GoString) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗
      p ↦{dq} github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk name val rv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.encodeObj)) (Val #p))
  {{ (sl : GoSlice), RET #sl; sl ↦* encodeWith tagV1 name val ∗
      p ↦{dq} github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk name val rv }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
