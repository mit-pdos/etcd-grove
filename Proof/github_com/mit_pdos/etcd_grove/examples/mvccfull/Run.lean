/- Lean-first (no Rocq counterpart). The proof of `Run`: Draft, to come.

The outline: `normalize`; `walkKeys` (`keysOf`, sorted, not empty); `zap.NewNop`; the history
(`hist0`, its names); the runner's fields persisted (`writerCtx`: `rnCtx`, `runnerCfg`, the weights,
the counters' invariants, `rdShared`); `memberPath`, `newMember` twice (the files `filePathsM`'s
first two); `startEpoch` of each (the members' shares split, `lentOk`); `startReaders`; `write`;
`stopReaders`; `hashing(cfg.Mix.Read)`, false under `runCfgOk`'s `readMixOk`
(`hashingM_of_readMixOk`), so `x.hashes()` is skipped; for each member `endEpoch`,
`inc_retire`, `shut`, `open`, `checkAll`, `inc_retire`, `shut`; the counters' `Load`s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.normalize
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.walkKeys
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.memberPath
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__newMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startEpoch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startReaders
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__write
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__stopReaders
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.hashing
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__endEpoch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__shut
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__open
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkAll

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

theorem Run.wp_proof
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_normalize : normalize.spec (GF := GF) (hG := hG))
    (wp_walkKeys : walkKeys.spec (GF := GF) (hG := hG))
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_memberPath : memberPath.spec (GF := GF) (hG := hG))
    (wp_newMember : runner.newMember.spec (GF := GF) (hG := hG))
    (wp_startEpoch : runner.startEpoch.spec (GF := GF) (hG := hG))
    (wp_startReaders : runner.startReaders.spec (GF := GF) (hG := hG))
    (wp_write : runner.write.spec (GF := GF) (hG := hG))
    (wp_stopReaders : runner.stopReaders.spec (GF := GF) (hG := hG))
    (wp_hashing : hashing.spec (GF := GF) (hG := hG))
    (wp_endEpoch : runner.endEpoch.spec (GF := GF) (hG := hG))
    (wp_shut : runner.shut.spec (GF := GF) (hG := hG))
    (wp_open : runner.open.spec (GF := GF) (hG := hG))
    (wp_checkAll : runner.checkAll.spec (GF := GF) (hG := hG)) :
    Run.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
