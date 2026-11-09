/-
`(*watcherGroup).chooseAll(curRev, compactRev)` (internal; under `s.mu`): each member above
`curRev` must be restoring (its flag cleared; else `panic`: the premise); each member below
`compactRev` is sent its compaction response without blocking (sent: marked compacted, removed from
the group; full: kept, retried by the next sync); the least `minRev` of the others.

**Proof sketch.** The records; for a member below `compactRev`, a `select` with a `default` on its
channel (`wsSendable` of its compaction response, given for each such member).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import Spec.go_uber_org.zap.Api

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

def watcherGroup.chooseAll.spec : Prop :=
  ∀ (wg : Loc) (v : watcherGroup) (dq : DFrac) (G : List (Loc × MRange)) (R : Loc → WRec)
    (curRev compactRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wg ↦{dq} v ∗ wgOwn v (DFrac.own 1) G ∗ ([∗list] x ∈ G, wRecAt x.1 (R x.1)) ∗
      ([∗list] x ∈ G, if decide ((R x.1).minRev < sint.Z compactRev) then
        wsCmpSendable x.1 compactRev else True) ∗
      ⌜∀ x ∈ G, (R x.1).minRev ≤ sint.Z curRev ∨ (R x.1).restore = true⌝ }}
    (App (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"chooseAll")) (Val #curRev)) (Val #compactRev))
  {{ (m : w64), RET #m; wg ↦{dq} v ∗ ∃ (Cm : List Loc) (R' : Loc → WRec),
      ⌜(∀ w ∈ Cm, ∃ x ∈ G, x.1 = w ∧ (R x.1).minRev < sint.Z compactRev) ∧
        (∀ x ∈ G, (R' x.1).minRev = (R x.1).minRev) ∧
        sint.Z m = minRevOf R G (sint.Z compactRev)⌝ ∗
      wgOwn v (DFrac.own 1) (G.filter (fun x => decide (x.1 ∉ Cm))) ∗
      ([∗list] x ∈ G, wRecAt x.1 (R' x.1)) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
