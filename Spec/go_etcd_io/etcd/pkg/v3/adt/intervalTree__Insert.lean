/-
`(*intervalTree).Insert(ivl, val)`: adds an entry (CLRS 14.3.5: split on the begin, then the end;
then `insertFixup`).

**Users.** `watcherGroup.add` (3f: a new range's watcher set), `checkIntervals` (2a: a level's
deletes), `getMergedPerms` (3d: read and write permissions, byte intervals and points), `Union`.
Snippets: `adt/watchers.go` `ReqRangeWatchers`, `adt/perms.go` `ReqPermCover`, `adt/dups.go`.

**Proof sketch.** `createIntervalNode`; the descent to the leaf position (`ivlLt` order: left when
below, right otherwise, so after equal intervals); the parent link; `insertFixup` (rotations,
recolouring, `updateMax` up the path: `Internal.lean`'s red-black model keeps the in-order list);
`count++` (below `ivtCountMax`: the premise).

**Changes** from `specs-ref`'s `Insert_gen` (the generic spec, now the only one: the string and
bytes instances were separate specs): at a key kind `c`; the count bound named.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.Api

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

/-- **`t.Insert(ivl, v)`**: the entry inserted in the tree's order, after the equal intervals.
The interval's key values are kept by the new node (read-only). -/
def intervalTree.Insert.spec : Prop :=
  ∀ (c : Cmp) (t : Loc) (L : List Entry) (vb ve : val) (b e : GoString) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ivt c t L (DFrac.own 1) ∗ keyAt c DFrac.discard vb b ∗ keyAt c DFrac.discard ve e ∗
      ⌜L.length < ivtCountMax⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Insert")) (Val #(c.ivl vb ve))) (Val #v))
  {{ RET #(); ivt c t (ivtInsert ((b, e), v) L) (DFrac.own 1) }}

end spec

end Adt
end EtcdGrove
end Perennial
