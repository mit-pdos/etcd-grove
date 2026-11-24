/-
Lean-first (no Rocq counterpart).

`meta.ListAccessor` of the k8s driver's `*ObjList` (any pointer, nil included), from its spec: the
same interface value and a nil error. `*ObjList` has `metav1.ListInterface`'s methods (`k8setcd3.go`),
so it is in `meta.List`'s type set (`go_type_set`). The callers are the maintainers' checker's
`Model.listResponseRV`, `Model.equalListResponse` and `Replay.validateList` (k8s 7g follow-up (B'),
`notes/k8s-7g-listaccessor-bprime.md`: this was the second row of the spec's former axiom).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.meta.ListAccessor
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [meta_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]

/-- `*ObjList` is in `meta.List`'s type set. -/
theorem objList_in_list :
    go.typeSetContains (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty)
      k8s_io.apimachinery.pkg.api.«meta».List''.ty = true := by
  go_type_set

/-- **`meta.ListAccessor` of an `*ObjList`** `l`: the same interface value, no error. -/
theorem ListAccessor_objList (wp_LA : apimeta.ListAccessor.spec (GF := GF) (hG := hG)) (l : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».ListAccessor))
      (Val #(interface.mkOk (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) #l)))
  {{ (m err : GoInterface), RET (PairV #m #err);
      ⌜m = interface.mkOk (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) #l ∧ err = interface.nil⌝ }} := by
  iintro %Φ #Hinit HΦ
  wp_apply (wp_LA ⟨go.GoType.PointerType
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty, #l⟩ objList_in_list) $$ [$Hinit]
  iapply HΦ
  ipureintro; exact ⟨rfl, rfl⟩

end lemmas

end k8s_correctness
end EtcdGrove
end Perennial
