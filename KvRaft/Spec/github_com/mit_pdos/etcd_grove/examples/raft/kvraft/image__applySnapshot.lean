-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/image__applySnapshot.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

`m.applySnapshot(snap)` (storage.go): `MemoryStorage.ApplySnapshot` of the snapshot `sv` (at `sp`,
not `nil`, only read) on the image: refused with `ErrSnapOutOfDate` (`eood`), the image unchanged,
when its snapshot is at a non-zero index at least `sv`'s (`imgSnapStale`); otherwise `nil`, and the
image holds `imgApplySnapshot I sv` (a copy of the snapshot, the log starting at it, empty).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Image

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev image.applySnapshot.spec : Prop :=
  ∀ (p : Loc) (I : StorFile) (sp : Loc) (dq : DFrac) (sv : SnapshotM) (eood : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      ownImage p I ∗ ownSnapM sp dq sv ∗ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (p @!! go.GoType.PointerType kImageTy @!! go!"applySnapshot")) (Val #sp))
  {{ (err : GoInterface), RET #err; ownSnapM sp dq sv ∗
      (if imgSnapStale I sv then iprop(⌜err = eood⌝ ∗ ownImage p I)
       else iprop(⌜err = interface.nil⌝ ∗ ownImage p (imgApplySnapshot I sv))) }}

end spec

end kvraft
end EtcdGrove
end Perennial
