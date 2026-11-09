/- Lean-first (no Rocq counterpart). The proof of `stream.recvOne`: Draft, to come (`sorry`).

The callees in call order: `Chan` (through `shapes.law`), the channel's receives
(`wsChan_recv.law`, the poll's bound from a registration's `wsSentLb` or `wsSentLb_zero.law`),
`receive`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__recvOne
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__receive

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem stream.recvOne.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hrecv : mvcc.api.wsChan_recv.law (GF := GF) (hG := hG))
    (hzero : mvcc.api.wsSentLb_zero.law (GF := GF) (hG := hG))
    (wp_stream_receive : stream.receive.spec (GF := GF) (hG := hG)) :
    stream.recvOne.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
