/-
`PutConfChange(buf, cc)` (`examples/raft/kvraft/client.go`): appends `encCC o` (`ConfCodec.lean`) to `buf`
for a change `cc` holding `o` (a `ConfChange` or a `ConfChangeV2`, `ownConfChangeI`), which it gives back.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.ConfCodec

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
abbrev PutConfChange.spec : Prop :=
  ∀ (buf : GoSlice) (B : List w8) (cc : GoInterface) (dq : DFrac) (o : ConfChangeIM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      buf ↦* B ∗ ownSliceCap w8 buf (DFrac.own 1) ∗ ownConfChangeI cc dq (some o) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.PutConfChange)) (Val #buf))
      (Val #cc))
  {{ (s : GoSlice), RET #s; s ↦* (B ++ encCC o) ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      ownConfChangeI cc dq (some o) }}

end spec

end kvraft
end EtcdGrove
end Perennial
