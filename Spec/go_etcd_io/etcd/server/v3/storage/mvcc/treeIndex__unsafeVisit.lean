/-
`treeIndex.unsafeVisit` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- The triple of the visitor `f` of `unsafeVisit`, over the entries `vis` it may visit: on the
`i`-th, lent its key index (`ownEntry`, given back) with its item fact, under an invariant
`P i`; it returns whether to go on (`Q` once it stops). -/
def mvcc.visitSpec (f : GoFunc) (vis : List mvcc.IdxEntry) (q : Qp) (P : Nat → IProp GF)
    (Q : IProp GF) : IProp GF :=
  iprop(∀ (i : Nat) (z : mvcc.IdxEntry), ⌜vis[i]? = some z⌝ -∗
    {{ P i ∗ mvcc.ownEntry z q ∗ mvcc.kiItemIs z.1 (z.1, z.2.1) }}
      (App (Val #f) (Val #z.1))
    {{ (cont : Bool), RET #cont; mvcc.ownEntry z q ∗ if cont then P (i + 1) else Q }})

instance mvcc.visitSpec_persistent (f : GoFunc) (vis : List mvcc.IdxEntry) (q : Qp)
    (P : Nat → IProp GF) (Q : IProp GF) : Persistent (mvcc.visitSpec f vis q P Q) := by
  unfold mvcc.visitSpec; infer_instance

/-- `ti.unsafeVisit(key, end, f)` (under the lock, on the tree at any fraction): `f` is called
on the entries of `[key, end)` (no bound if `end` is empty) in key order, until it stops. -/
abbrev mvcc.treeIndex.unsafeVisit.spec : Prop :=
  ∀ (ti t : Loc) (L : List mvcc.IdxEntry) (q : Qp) (key endk : GoSlice) (k e : GoString)
    (f : GoFunc) (P : Nat → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ti.[treeIndex, go!"tree"] ↦□ t ∗ mvcc.ownTree t L q ∗ key ↦*□ k ∗ endk ↦*□ e ∗ P 0 ∗
      mvcc.visitSpec f (mvcc.rangeEntries L k e) q P Q }}
    (App (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"unsafeVisit")) (Val #key))
      (Val #endk)) (Val #f))
  {{ RET #(); mvcc.ownTree t L q ∗ (Q ∨ P (mvcc.rangeEntries L k e).length) }}

end spec

end EtcdGrove
end Perennial
