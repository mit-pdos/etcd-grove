/-
`listen(addr)` (`examples/raft/kvnet/node.go`): a listener on `addr`, retried until `net.Listen`
succeeds (a failed `Listen` is never a panic: the net extension lets any one fail). `addr` is a
valid address with the library's protocols (`addrProto`, whose listening token each `Listen` takes:
`listen_au`). Partial correctness: if it returns, it returns this node's listener at `addr`.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import GooseLang.Ext.Net.Proto

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev listen.spec : Prop :=
  ∀ (a : GoString) (P Q : Net.Proto GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      addrProto a P Q }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.listen)) (Val #a))
  {{ (li : GoInterface), RET #li; ∃ (l : w64), net.isListener li l ∗
      netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
      netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
