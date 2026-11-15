/-
`(*watcherGroup).watcherSetByKey(key)` (internal): the watchers of `key` (its key's set, the range
sets the key's point stabs), as one set: the group's own (lent) when there is one source, else a
fresh union.

**Proof sketch.** The key's set; `ranges.Stab` of the point (`Adt.intervalTree.Stab.spec`); the
zero-copy cases return a set of the group, lent at the group's fraction; else `watcherSet.union`s
into a fresh set (the sets disjoint: each watcher is in one place).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def watcherGroup.watcherSetByKey.spec : Prop :=
  ∀ (wg : Loc) (v : watcherGroup) (dq dq' : DFrac) (G : List (Loc × MRange)) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wg ↦{dq} v ∗ wgOwn v dq' G }}
    (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"watcherSetByKey")) (Val #k))
  {{ (m : GoMap), RET #m; wg ↦{dq} v ∗ ∃ (S : List Loc) (dm : DFrac),
      ⌜S.Perm ((G.filter (fun y => decide (y.2.watchMem k))).map Prod.fst)⌝ ∗ wsetOwn m dm S ∗
      (wsetOwn m dm S -∗ wgOwn v dq' G) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
