-- The copy for the part `KvNet/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/getSnapshot.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

`getSnapshot(b)` (storage.go): what `putSnapshot` wrote at the start of `b` (`encSnap s`, of Go
slices' lengths, `SnapWf`), read back into a fresh snapshot, owned (its data a slice of `b`: the
snapshot's bytes go into it, as `MemoryStorage.CreateSnapshot` takes them, owned), the rest, and
`ok`. Stated of bytes `putSnapshot` wrote, so `ok` is `true`. (2026-11-01, openStorage's proof: the
snapshot with every pointer field set, `ownSnapS` -- its metadata, the metadata's conf state, with its
`AutoLeave`, index and term, as `getSnapshot` builds them: `openStorage` hands the conf state to
`MemoryStorage.CreateSnapshot`, which needs it non-`nil`, and applies the snapshot read-only.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Codec
public import KvNet.Proof.go_etcd_io.raft.v3.InvPbSnapSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- See the file header. -/
abbrev getSnapshot.spec : Prop :=
  ∀ (b : GoSlice) (s : SnapshotM) (r : List w8),
  SnapWf s →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ b ↦* (encSnap s ++ r) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getSnapshot)) (Val #b))
  {{ (p : Loc) (rest : GoSlice), RET (PairV (PairV #p #rest) #true);
      ownSnapS p (DFrac.own 1) s ∗ rest ↦* r }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
