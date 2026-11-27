/-
**`compactChan.law`, linked** (mvccfull's Prove, 2026-11-10): `Api/CompactChan.lean`'s proof
instantiated with the internal results of `Link.lean`, as `ApiResults.lean` does for
`KV.Compact.contract` (in a module of its own, so that `ApiResults`' importers are unchanged). A
linking file (exempt from `etc/api-check.py`'s rules).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CompactChan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

namespace mvcc
namespace api

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

theorem mvccApi_compactChan_law_holds : compactChan.law (GF := GF) :=
  compactChan.law_holds (mvcc.store.Compact.core_proof
    mvcc.store.wp_checkPrevCompactionCompleted mvcc.store.wp_updateCompactRev traceutil.Trace.wp_Step
    mvcc.store.wp_compact)

end results

end api
end mvcc

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.mvcc.api.mvccApi_compactChan_law_holds
