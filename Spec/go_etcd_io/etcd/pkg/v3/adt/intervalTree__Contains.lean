/-
`intervalTree.Contains` (`interval_tree.go`) over string-affine keys: the generic `Contains_gen.spec`
instantiated (the auth plan's S2b, 2026-10-23). Lean-first; see `Contains.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Contains

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `t.Contains(ivl)`: `containsRes` (`Contains.lean`) for a query whose begin is the top `""` or
below its end (`Visit`'s premise); some boolean otherwise. At any fraction of the tree. -/
abbrev adt.intervalTree.Contains.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoString) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvt t L q }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Contains"))
      (Val #(adt.affIvl b e)))
  {{ (r : Bool), RET #r; adt.ownIvt t L q ∗
      ⌜(b = go!"" ∨ adt.affLt b e) → r = adt.containsRes (b, e) L⌝ }}

end spec

end EtcdGrove
end Perennial
