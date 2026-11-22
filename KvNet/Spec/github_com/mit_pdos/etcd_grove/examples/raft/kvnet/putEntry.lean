-- The copy for the part `KvNet/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/putEntry.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

`putEntry(buf, e)` (storage.go): `buf` with the entry at `l` appended (`encEntry`: its term, index
and type, then its data), the entry only read (at any fraction: a log entry is read-only,
`entRO`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Codec
public import KvNet.Proof.go_etcd_io.raft.v3.InvPb

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
abbrev putEntry.spec : Prop :=
  ∀ (buf : GoSlice) (B : List w8) (l : Loc) (dq : DFrac) (e : EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ buf ↦* B ∗ ownSliceCap w8 buf (DFrac.own 1) ∗ entPts l dq e }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putEntry)) (Val #buf)) (Val #l))
  {{ (s : GoSlice), RET #s; s ↦* (B ++ encEntry e) ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      entPts l dq e }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
