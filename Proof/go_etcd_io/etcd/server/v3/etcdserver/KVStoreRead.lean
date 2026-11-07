/-
**The server's read path over mvcc's API** (strict M1, 2026-11-05; the frozen draft
`notes/mvcc-api-clients/ServerSpecs.lean` §6's read-path conjuncts, apart from `KVStoreApi.lean` so
that the store invariant imports no read-loop module): the client model's server log `srvLogA`,
the applied floor, the claims' floor facts, a served read's call resources, a range's and a
header's outcomes with their receipts, client/v3's `idxCert_logOk` restated (`logOk_of_receipt`,
proved), the compactor's revision lower bound.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace Perennial
namespace EtcdGrove
namespace srvApi
open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api

section server
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The client model's server log** (v3rpc's `srvLog`, restated over `histLb`). -/
def srvLogA (γr : ReadNames) (on : Bool) (γs : KVSNames) (log : mvcc.Log) : IProp GF :=
  iprop(histLb γr on γs log ∗ ⌜txn.LogSmall log ∧ mvcc.LogPutsLe etcdKeyMax log⌝)

/-- `srvAppliedBody`'s changed conjunct: the applied log a floor (was `mvcc.idxCert E.γ.idx L`). -/
def appliedFloorA (E : AEnvA GF) (L : mvcc.Log) : IProp GF := kvLogLb E.γs L

/-- **The claims' floor facts** (`srvFloorFacts`, restated). -/
def srvFloorFactsA (slog : GName) (_id : w64) (_d : List w8) (γf : GName) : IProp GF :=
  iprop(∃ F : mvcc.Log, floorAt γf F ∗ monoListLbOwn slog F)

/-- **A served read's call resources** (`srvRdCall`, restated): the thread's token in place of the
store's reader slot. -/
def srvRdCallA (s : Loc) (E : AEnvA GF) (γr : ReadNames) (c : w64) : IProp GF :=
  iprop(threadTok ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvLgReader s ∗ committedAtLeast γr c ∗
    srvReadReader s γr ∗ E.RD)

/-- **A successful `Range`'s outcome, restated** (`rangeReadOkM`; xreview §5): the log read is a
floor, the model of a committed raft log, well formed, with its receipt (from `kvReadAt`), read
after the read index unless serializable, the caller's result as today. -/
def rangeReadOkA (on : Bool) (E : AEnvA GF) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (o : OpFull) (resp : Loc) (Q : List EntryModel → IProp GF) : IProp GF :=
  iprop(∃ (log : mvcc.Log) (crev : Int), kvLogLb E.γs log ∗ kvNx γr on log ∗
    ⧖ (mvcc.logCh log) ∗ ⌜mvcc.LogWf' log ∧ 2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧ F <+: log⌝ ∗
    (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
    (if o.base.serializable then iprop(True) else
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModelM on γr.kv L = log⌝ ∗ □ Q L) ∗
    txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) crev o true ∗
    txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.RangeResponse go!"Header" resp))

/-- `newHeader`'s post, restated (xreview §5): a floor, the model's, well formed, its receipt. -/
def newHeaderPostA (E : AEnvA GF) (γr : ReadNames) (on : Bool) (log : mvcc.Log) (rev : w64) :
    IProp GF :=
  iprop(kvLogLb E.γs log ∗ kvNx γr on log ∗ ⧖ (mvcc.logCh log) ∗
    ⌜mvcc.LogWf' log ∧ log ≠ [] ∧ rev = W64 ((log.length : Int) - 1)⌝)

/-- **client/v3's `idxCert_logOk` (`KVService.lean:1515`), restated** over what `rangeReadOkA` and
`newHeaderPostA` give: proved (as today's, by `preceipt_lt`). -/
theorem logOk_of_receipt (log : mvcc.Log) (hrb : receiptBound GF ≤ 2 ^ 62) :
    ⧖ (mvcc.logCh log) ∗ ⌜mvcc.LogWf' log ∧ log.length + 3 ≤ 2 ^ 63⌝ ⊢
      (⌜mvcc.LogWf' log ∧ log.length < 2 ^ 63 ∧ txn.LogSmall log⌝ : IProp GF) := by
  iintro ⟨Hr, %Hp⟩
  ihave %Hm := preceipt_lt _ $$ Hr
  ipureintro
  refine ⟨Hp.1, by omega, ?_⟩
  unfold txn.LogSmall txn.logChanges; unfold mvcc.logCh at Hm; omega

/-- **The compactor's revision lower bound** (`srvRevLb`, restated): raft-only. -/
def srvRevLbA (γr : ReadNames) (on : Bool) (n : Int) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γr.raft A ∗ ⌜n < (kvModelM on γr.kv A).length⌝)

end server

end srvApi
end EtcdGrove
end Perennial
