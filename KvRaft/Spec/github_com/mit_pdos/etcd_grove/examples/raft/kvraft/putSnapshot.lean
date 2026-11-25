-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/putSnapshot.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

`putSnapshot(buf, snap)` (storage.go): `buf` with the snapshot at `p` appended (`encSnap`: its
index and term, its configuration, then its data), the snapshot only read.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Codec
public import KvRaft.Proof.go_etcd_io.raft.v3.InvPb

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

/-- See the file header. -/
abbrev putSnapshot.spec : Prop :=
  ∀ (buf : GoSlice) (B : List w8) (p : Loc) (dq : DFrac) (s : SnapshotM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ buf ↦* B ∗ ownSliceCap w8 buf (DFrac.own 1) ∗ ownSnapM p dq s }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putSnapshot)) (Val #buf)) (Val #p))
  {{ (sl : GoSlice), RET #sl; sl ↦* (B ++ encSnap s) ∗ ownSliceCap w8 sl (DFrac.own 1) ∗
      ownSnapM p dq s }}

end spec

end kvraft
end EtcdGrove
end Perennial
