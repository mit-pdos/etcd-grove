/- Lean-first (no Rocq counterpart). The proof of `runner.restart`: Draft, to come.

The outline: `stopReaders` (the stock back, `rdStock`), `endEpoch` (the epoch's `epochTok`s back),
the shares joined (`lentOk`: the whole retirement token, `kv` field and `mvccReaderN` tokens),
`inc_retire`, `memberState_split`; `shut` (the lessor's and backend's parts from `memCore`); `open`;
the counter; `startEpoch` (new shares `qs'`, tokens), `startReaders` (`rdStock` at the members' current
incarnations, `rdStock_split`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__restart
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__stopReaders
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__endEpoch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__shut
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__open
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startEpoch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startReaders

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
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.restart.wp_proof
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_stopReaders : runner.stopReaders.spec (GF := GF) (hG := hG))
    (wp_endEpoch : runner.endEpoch.spec (GF := GF) (hG := hG))
    (wp_shut : runner.shut.spec (GF := GF) (hG := hG))
    (wp_open : runner.open.spec (GF := GF) (hG := hG))
    (wp_startEpoch : runner.startEpoch.spec (GF := GF) (hG := hG))
    (wp_startReaders : runner.startReaders.spec (GF := GF) (hG := hG)) :
    runner.restart.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
