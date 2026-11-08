/-
`(*storage.SelectionPredicate).Matches(obj)` (`k8s.io/apiserver/pkg/storage/selection_predicate.go`),
**for the k8s etcd3 driver's predicates** (`predV x`, `examples/k8s/etcd3`'s `predicate(in)`) on
one of its objects (`&o`, an `*Obj`): no error, and whether the driver's selectors select it
(`selOkL x o`: `labelSel.Matches` and `fieldSel.Matches` on `getAttrs(o)`; no sharding).

A hypothesis of the driver's `mlist` (k8s 7e-3b, Q7e-3b-2): not linked, no axiom; its statement
is 7e-2's Draft's to review (provable from the translated `Matches`, `MatchesSharding`,
`labelFieldEmpty` and the driver's selector and `getAttrs` specs). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KList

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open k8s_etcd3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.SelectionPredicate.Matches.spec : Prop :=
  ∀ (pp : Loc) (x : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Input) (op : Loc)
    (o : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ pp ↦ predV x ∗
      op ↦{dq} o }}
    (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty
      @!! go!"Matches")) (Val #(interface.mkOk
        (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #op)))
  {{ RET (PairV #(selOkL x o) #GoInterface.nil); pp ↦ predV x ∗ op ↦{dq} o }}

end spec

end EtcdGrove
end Perennial
