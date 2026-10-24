/-
`intervalTree.Insert` (`interval_tree.go`) over bytes-affine keys: the generic `Insert_gen.spec`
instantiated (the auth plan's S2b, 2026-10-23; until then an axiom of `BytesIvl.lean`, the auth
plan's S2, stated as here). Lean-first; see `BytesIvl.lean`.
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

/-- **`t.Insert(ivl, v)` over bytes-affine keys** (`intervalTree.Insert.spec` with `bytesIvl`:
the slices read-only, the keys their contents). -/
abbrev adt.intervalTree.Insert_bytes.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoSlice) (bs es : GoString) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvtB t L (DFrac.own 1) ∗
      b ↦*□ bs ∗ e ↦*□ es ∗ ⌜L.length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Insert"))
      (Val #(adt.bytesIvl b e))) (Val #v))
  {{ RET #(); adt.ownIvtB t (adt.ivtInsert ((bs, es), v) L) (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
