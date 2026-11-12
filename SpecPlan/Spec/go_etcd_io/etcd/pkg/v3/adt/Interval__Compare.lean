/-
`(*Interval).Compare(c)`: `-1` if the receiver is left of `c` (a `*Interval`), `1` if right, `0` if
they overlap (`ivlCmp`).

**Users.** `intervalNode.visit`, `Intersects` (internal). **Proof sketch.** Three comparisons of the
key values (the kind's `Compare` spec). **Changes.** At a key kind `c` (was a key representation
`K` with its comparison contract). **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.adt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

def Interval.Compare.spec : Prop :=
  ∀ (c : Cmp) (p : Loc) (dq : DFrac) (vb ve : val) (db de : DFrac) (b e : GoString)
    (q : Loc) (dq' : DFrac) (vb' ve' : val) (db' de' : DFrac) (b' e' : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ p ↦{dq} c.ivl vb ve ∗ keyAt c db vb b ∗ keyAt c de ve e ∗
      q ↦{dq'} c.ivl vb' ve' ∗ keyAt c db' vb' b' ∗ keyAt c de' ve' e' }}
    (App (Val (p @!! go.GoType.PointerType Interval.ty @!! go!"Compare"))
      (Val #(interface.mkOk (go.GoType.PointerType Interval.ty) #q)))
  {{ RET #(W64 (ivlCmp (b, e) (b', e')));
      p ↦{dq} c.ivl vb ve ∗ keyAt c db vb b ∗ keyAt c de ve e ∗
      q ↦{dq'} c.ivl vb' ve' ∗ keyAt c db' vb' b' ∗ keyAt c de' ve' e' }}

end spec

end Adt
end EtcdGrove
end Perennial
