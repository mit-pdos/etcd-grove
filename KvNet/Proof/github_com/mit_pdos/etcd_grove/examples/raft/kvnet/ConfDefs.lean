/- Lean-first (no Rocq counterpart).

# A `ReqConf` payload's change, read back (2026-11-22)

`kvConfRead c pl` (`GetConfChange.spec`'s `cf`, at the store): what `GetConfChange` reads back from any
payload `pl` it accepts, a conf change `c` owned whole (`ownConfChangeI`, a `ConfChange` or a
`ConfChangeV2`) of a defined transition (`ccTransOk`: `node.ProposeConfChange` takes it; a decoded
transition is one of the three defined ones). Nothing about `pl`: the server proposes whatever change
a client asks for, and the store's conf policy (`confPolicy`, `kvrRule`) decides at the commit which
take effect, so the protocol needs no fact of a `ReqConf` payload (`kvFacts`' `confOk` is `True`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Pure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def kvConfRead (c : GoInterface) (_pl : List w8) : IProp GF :=
  iprop(∃ o : ConfChangeIM, ownConfChangeI c (DFrac.own 1) (some o) ∗ ⌜raft_kvreconf.ccTransOk o⌝)

end defs

end raft_kvnet
end EtcdGrove
end Perennial
