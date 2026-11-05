/-
**The apply package's compaction arm: the glue** (M2, the apply side, the switch; drafted in
`M2ApplyDraft.lean`, `notes/m2-apply-plan.md`). Lean-first (no Rocq counterpart). The vocabulary
(`chainCompacts`, `cmpRevAfter`, `cmpAdmitRev`, `cmpOwn`, `cmpAnswerIs`, the chain's `cmpTriple`) is
`Chain.lean`'s; here `cmp_store_pre`: the backend's `Compaction` meets `store.Compact.spec`'s
precondition from the apply thread's KV and compaction resources.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LockArm

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

namespace apply

/-! (Strict M1, 2026-11-05: the glue of the backend's `Compaction` over today's `store.Compact`,
`cmp_store_pre`, is gone with mvcc's internals; the chain's compaction resources are mvcc's API's,
`cmpOwn`, and `Compaction`'s proof calls `KV.Compact.contract` directly.) -/

end apply

end EtcdGrove
end Perennial
