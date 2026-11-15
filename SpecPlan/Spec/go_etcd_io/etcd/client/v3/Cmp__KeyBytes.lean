/-
`(*clientv3.Cmp).KeyBytes` (`client/v3/compare.go`).

Users: leasing (`leasing/txn.go`, `leasing/util.go`: the keys of a transaction's comparisons).

Proof sketch: `cmpAt_unfold`; the message's getter (`Compare.GetKey`, 3h: `nil` for a nil message).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Cmp__KeyBytes.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: the code also accepts a nil `*Cmp` (it returns `nil`); no user passes one.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `cmp.KeyBytes()`: the comparison's key (`nil` for a zero `Cmp`). -/
def Cmp.KeyBytes.spec : Prop :=
  ∀ (cp : Loc) (c : go_etcd_io.etcd.client.v3.Cmp) (m : Option EtcdModel.Compare) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cp ↦{dq} c ∗ cmpAt c m }}
    (App (Val (cp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Cmp.ty @!! go!"KeyBytes")) (Val #()))
  {{ (s : GoSlice), RET #s; cp ↦{dq} c ∗
      (match m with
       | none => iprop(⌜s = slice.nil⌝)
       | some x => iprop(s ↦*□ x.key)) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
