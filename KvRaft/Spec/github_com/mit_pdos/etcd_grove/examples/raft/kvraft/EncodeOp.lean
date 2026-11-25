/-
`EncodeOp(id, kind, key, val)` (`examples/raft/kvraft/client.go`): `encode`'s bytes, the operation's
encoding as the store's log entry and `ReqPropose`'s payload (`encodeOp`, kvreconf's pure model,
`kvreconf/Pure.lean`), a fresh slice with its capacity.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Pure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI go_etcd_io.raft.v3 raft_kvreconf

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- See the file header. -/
abbrev EncodeOp.spec : Prop :=
  ∀ (id : w64) (kind : w8) (key val : List w8),
  (key.length : Int) < 2 ^ 61 → (val.length : Int) < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.EncodeOp))
      (Val #id)) (Val #kind)) (Val #key)) (Val #val))
  {{ (b : GoSlice), RET #b; b ↦* encodeOp id kind key val ∗ ownSliceCap w8 b (DFrac.own 1) }}

end spec

end kvraft
end EtcdGrove
end Perennial
