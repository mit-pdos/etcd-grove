/-
Proof of `Spec/.../mvcc/cohortsByRevision.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.cohortsByRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__add
public import Spec.sort.Slice

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.cohortsByRevision.wp_proof
    (hSlice : sort.Slice.spec (GF := GF) (hG := hG))
    (hNew : mvcc.newWatcherGroup.spec (GF := GF) (hG := hG))
    (hAdd : mvcc.watcherGroup.add.spec (GF := GF) (hG := hG)) :
    mvcc.cohortsByRevision.spec (GF := GF) (hG := hG) := by
  have hAddG := mvcc.watcherGroup.add.spec_group hAdd
  intro wg W ST cr
  wp_start as ⟨Hg, HST, %Hdom⟩
  icases mvcc.ownWatcherGroup_watchers wg W $$ Hg with ⟨%v, Hwg, Hws, Hback⟩
  iunfold mvcc.ownWatcherSet at Hws
  wp_auto
  done

end proof

end EtcdGrove
end Perennial
