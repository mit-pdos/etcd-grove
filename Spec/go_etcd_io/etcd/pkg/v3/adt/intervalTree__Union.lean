/-
`intervalTree.Union` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
Pending: specified, not proved yet; the tree's unit 4d proves it (`Union` is `Visit` of the other
tree with a closure inserting into this one), until then a hypothesis of every result that
reaches it (`?` in `etc/link-lean-first-adt.txt`). Added 2026-10-12 for the server's request
path (`v3rpc.checkIntervals` unions the nested transactions' delete trees into its own),
restated in the contract's style at the merge into `mvcc` (the fractions, the count bound, the
query premise of `Stab`/`Visit`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs

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

/-- `t.Union(t', ivl)` of another tree `t'` (an `IntervalTree` holding an `*intervalTree`):
inserts into `t`, one by one (`Insert`, in `Visit`'s order: some order of them), the entries of
`t'` the interval overlaps (`stab`); `t'` unchanged. As `Insert`, no premise that the inserted
intervals are new (`checkIntervals` unions trees that may hold an interval `t` already has, the
same range deleted at two levels), and the count bound: `t` holds the whole tree (fraction `1`),
`t'` any fraction (so the two are distinct trees), together below `2^63` entries. The query is
not degenerate (`Stab`'s and `Visit`'s premise; `checkIntervals` passes `["\x00", +∞)`). -/
abbrev adt.intervalTree.Union.spec : Prop :=
  ∀ (t t' : Loc) (L L' : List adt.Entry) (q' : Qp) (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvt t L 1 ∗
      adt.ownIvt t' L' q' ∗ ⌜L.length + L'.length < 2 ^ 63⌝ ∗ ⌜b = go!"" ∨ adt.affLt b e⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Union"))
      (Val #(interface.mkOk (go.GoType.PointerType intervalTree.ty) #t')))
      (Val #(adt.affIvl b e)))
  {{ RET #(); ∃ zs : List adt.Entry, ⌜zs.Perm (adt.stab (b, e) L')⌝ ∗
      adt.ownIvt t (zs.foldl (fun acc z => adt.ivtInsert z acc) L) 1 ∗ adt.ownIvt t' L' q' }}

end spec

end EtcdGrove
end Perennial
