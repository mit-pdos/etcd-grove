/- Lean-first (no Rocq counterpart).

`versioner{}.ObjectResourceVersion(obj)` (k8setcd3.go) of a `*Obj`: its resource version.
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
abbrev versioner.ObjectResourceVersion.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (name val : GoString) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ p ↦{dq} github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk name val rv }}
    (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner.ty go!"ObjectResourceVersion" #(github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner.mk))) (Val #(interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.ty) #p)))
  {{ RET (PairV #rv #GoInterface.nil); p ↦{dq} github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk name val rv }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
