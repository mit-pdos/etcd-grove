/-
`(*watcherGroup).choose(maxWatchers, curRev, compactRev)` (internal; under `s.mu`): the group
itself when smaller than `maxWatchers`, else a fresh group of `maxWatchers` of its members; then
`chooseAll` on it. (On a copy, the compacted members leave only the copy: they stay in the source
and are sent their compaction again by a later sync, `issues/etcd-watch-compacted-resent.md`.)

**Proof sketch.** `newWatcherGroup`, `add` of the members (the map's iteration order), `chooseAll`.
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

def watcherGroup.choose.spec : Prop :=
  ∀ (wg : Loc) (v : watcherGroup) (dq : DFrac) (G : List (Loc × MRange)) (R : Loc → WRec)
    (maxW curRev compactRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wg ↦{dq} v ∗ wgOwn v (DFrac.own 1) G ∗ ([∗list] x ∈ G, wRecAt x.1 (R x.1)) ∗
      ([∗list] x ∈ G, if decide ((R x.1).minRev < sint.Z compactRev) then
        wsCmpSendable x.1 compactRev else True) ∗
      ⌜∀ x ∈ G, (R x.1).minRev ≤ sint.Z curRev ∨ (R x.1).restore = true⌝ }}
    (App (App (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"choose")) (Val #maxW)) (Val #curRev))
      (Val #compactRev))
  {{ (g : Loc) (m : w64), RET (PairV #g #m); wg ↦{dq} v ∗
      ∃ (C : List (Loc × MRange)) (R' : Loc → WRec),
        ⌜(∀ x ∈ C, x ∈ G) ∧ sint.Z m = minRevOf R C (sint.Z compactRev)⌝ ∗
        ([∗list] x ∈ G, wRecAt x.1 (R' x.1)) ∗
        ((⌜g = wg⌝ ∗ ∃ G' : List (Loc × MRange), ⌜List.Sublist G' G⌝ ∗ wgOwn v (DFrac.own 1) G') ∨
         (∃ (vc : watcherGroup) (C' : List (Loc × MRange)), g ↦ vc ∗ wgOwn vc (DFrac.own 1) C' ∗
            ⌜∀ x ∈ C', x ∈ C⌝ ∗ wgOwn v (DFrac.own 1) G)) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
