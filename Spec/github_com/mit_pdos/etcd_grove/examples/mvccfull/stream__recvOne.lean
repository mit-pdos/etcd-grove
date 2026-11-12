/- Lean-first (no Rocq counterpart).

`s.recvOne()` (`examples/mvccfull/mvccfull.go`): the receiver's step, with its resources
(`rcvOwn`, `Streams.lean`: after the responses `rs`, its `wsRecv` and its half of `σs.rcv`). Under
`s.mu`, a non-blocking receive (`wsChan_recv.law`'s second form, at `wsSentLb ι n` for `n` the
registry's largest `k`): a response is checked (`receive`); the channel closed and drained ends the
loop (`false`); the channel empty (`n ≤ |rs|`) stamps every registered watcher (`stamp_ok`). Then,
in the empty case, a blocking receive without the lock, its response checked under the lock. Every
check passes; `false` only once the channel is closed and drained.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Streams

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev stream.recvOne.spec : Prop :=
  ∀ (T : Strm) (q : Qp) (rs : List WResp),
  {{ streamCtx (GF := GF) T ∗ rcvOwn T q rs }}
    (App (T.s @!! go.GoType.PointerType stream.ty @!! go!"recvOne") (Val #()))
  {{ (b : Bool), RET #b; ∃ rs' : List WResp, rcvOwn T q rs' }}

end spec

end mvccfull
end EtcdGrove
end Perennial
