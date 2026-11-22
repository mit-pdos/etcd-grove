/-
`PutStatus(buf, s)` (`examples/raft/kvnet/client.go`): the status `s` appended to `buf` (here
`nil`): some bytes, of a length a reply frame takes. (Its proof, over `putConfState`, `putMap` and
`putUint64`, is not yet written.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev PutStatus.spec : Prop :=
  ∀ (s : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Status),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.PutStatus)) (Val #slice.nil)) (Val #s))
  {{ (sl : GoSlice), RET #sl; ∃ bs : List w8, sl ↦* bs ∗ ⌜bs.length < 2 ^ 61⌝ }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
