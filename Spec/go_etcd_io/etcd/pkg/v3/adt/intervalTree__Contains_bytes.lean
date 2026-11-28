/-
`intervalTree.Contains` (`interval_tree.go`) over bytes-affine keys: the generic
`Contains_gen.spec` instantiated (the auth plan's S2b, 2026-10-23; until then an axiom of
`BytesIvl.lean`, the auth plan's S2, stated as here). Lean-first; see `BytesIvl.lean`, `Contains.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.BytesIvl

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

/-- **`t.Contains(ivl)` over bytes-affine keys** (`intervalTree.Contains_gen.spec` with
`bytesKey`), on the exact tree (`ownIvtTB`), for any query: `containsT` (`Contains.lean`: the greedy
scan over the entries `Visit` visits). -/
abbrev adt.intervalTree.Contains_bytes.spec : Prop :=
  ∀ (t : Loc) (T : adt.RbT adt.Entry) (b e : GoSlice) (bs es : GoString) (db de dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvtTB t T dq ∗
      b ↦*{db} bs ∗ e ↦*{de} es }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Contains"))
      (Val #(adt.bytesIvl b e)))
  {{ (r : Bool), RET #r; adt.ownIvtTB t T dq ∗ b ↦*{db} bs ∗ e ↦*{de} es ∗
      ⌜r = adt.containsT (bs, es) T⌝ }}

end spec

end EtcdGrove
end Perennial
