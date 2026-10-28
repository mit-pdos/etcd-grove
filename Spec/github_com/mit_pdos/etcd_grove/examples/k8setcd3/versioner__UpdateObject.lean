/- Lean-first (no Rocq counterpart).

`versioner{}.UpdateObject(obj, n)` (k8setcd3.go) of a `*Obj`: its resource version is `n`.
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
abbrev versioner.UpdateObject.spec : Prop :=
  ∀ (p : Loc) (name val : GoString) (rv n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ p ↦ github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk name val rv }}
    (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner.ty go!"UpdateObject" #(github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner.mk))) (Val #(interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.ty) #p))) (Val #n))
  {{ RET #GoInterface.nil; p ↦ github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk name val n }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
