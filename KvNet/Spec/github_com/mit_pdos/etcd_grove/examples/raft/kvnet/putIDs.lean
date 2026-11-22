-- The copy for the part `KvNet/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/putIDs.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

`putIDs(buf, ids)` (storage.go): `buf` with the ids appended (`encIDs`: their number, then each).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Codec

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
abbrev putIDs.spec : Prop :=
  ∀ (buf ids : GoSlice) (B : List w8) (xs : List w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ buf ↦* B ∗ ownSliceCap w8 buf (DFrac.own 1) ∗ ids ↦*{dq} xs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putIDs)) (Val #buf)) (Val #ids))
  {{ (s : GoSlice), RET #s; s ↦* (B ++ encIDs xs) ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      ids ↦*{dq} xs }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
