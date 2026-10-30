/- Lean-first (no Rocq counterpart).

`copyMsg(m)` (cluster.go): a fresh copy of the message `m` holding `st` (at any fractions), as the
wire delivers it: a message holding `st` without its responses, owned, with its `Entries` slice's
elements and capacity (what `stepIn_intro` takes); `m` is given back. The copy shares `m`'s field
cells, entries and `Context` bytes (all read-only), and deep-copies the snapshot
(`proto.CloneSnapshot`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base
public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- See the file header. -/
abbrev copyMsg.spec : Prop :=
  ∀ (l : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
      msgPtsC l dq dqe cap st }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.copyMsg)) (Val #l))
  {{ (l' : Loc), RET #l'; msgPtsC l dq dqe cap st ∗
      msgPtsC l' (DFrac.own 1) (DFrac.own 1) true { st with resps := [] } }}

end spec

end kvreconf
end EtcdGrove
end Perennial
