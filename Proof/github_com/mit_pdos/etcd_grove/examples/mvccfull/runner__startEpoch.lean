/- Lean-first (no Rocq counterpart). The proof of `runner.startEpoch`: Draft, to come (`sorry`).

The callees in call order: `NewWatchStream` (through `shapes.law`), the receiver's loop
(`recvOne`, `time.Sleep`), the registrar's (`act`, `time.Sleep`); `sync`'s join idiom and atomics are
Perennial's linked results.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startEpoch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__recvOne
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__act
public import Perennial.Spec.time.Sleep

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

theorem runner.startEpoch.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_stream_recvOne : stream.recvOne.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG))
    (wp_stream_act : stream.act.spec (GF := GF) (hG := hG)) :
    runner.startEpoch.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
