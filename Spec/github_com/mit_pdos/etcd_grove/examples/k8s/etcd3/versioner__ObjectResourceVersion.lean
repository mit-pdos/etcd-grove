/- Lean-first (no Rocq counterpart).

`versioner{}.ObjectResourceVersion(obj)` (k8s_etcd3.go) of a `*Obj`: its resource version.
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
abbrev versioner.ObjectResourceVersion.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ p ↦{dq} v }}
    (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner.ty go!"ObjectResourceVersion" #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner.mk))) (Val #(interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p)))
  {{ RET (PairV #v.ResourceVersion' #GoInterface.nil); p ↦{dq} v }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
