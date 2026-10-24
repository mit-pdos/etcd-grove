/-
`intervalTree.Intersects` (`interval_tree.go`) over bytes-affine keys: the generic
`Intersects_gen.spec` instantiated (the auth plan's S2b, 2026-10-23; until then an axiom of
`BytesIvl.lean`, the auth plan's S2, stated as here). Lean-first; see `BytesIvl.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.BytesIvl

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- **`t.Intersects(ivl)` over bytes-affine keys** (`intervalTree.Intersects.spec` with
`bytesIvl`): whether some entry overlaps the query. -/
abbrev adt.intervalTree.Intersects_bytes.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoSlice) (bs es : GoString) (db de dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvtB t L dq ∗
      b ↦*{db} bs ∗ e ↦*{de} es }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Intersects"))
      (Val #(adt.bytesIvl b e)))
  {{ RET #(decide (adt.stab (bs, es) L ≠ [])); adt.ownIvtB t L dq ∗ b ↦*{db} bs ∗ e ↦*{de} es }}

end spec

end EtcdGrove
end Perennial
