/-
`getAttrs(&o)` of a `*Obj` held at any fraction: the label and field sets `labMapL o`, `fldMapL o`
(fresh, persisted), no error. Stage 7e-2 (`notes/k8s-7e-2-draft.md` §6). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Sel
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj labelSel fieldSel)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev getAttrs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (o : Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ p ↦{dq} o }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs))
      (Val #(interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p)))
  {{ (lm fm : Loc), RET (PairV (PairV #lm #fm) #GoInterface.nil); p ↦{dq} o ∗
      mapRO lm (labMapL o) ∗ mapRO fm (fldMapL o) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
