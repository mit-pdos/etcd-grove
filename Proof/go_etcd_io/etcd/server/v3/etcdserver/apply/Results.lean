/-
The results of the server's apply package (`server/v3/etcdserver/apply`), restated at top level,
with the trust base of each printed in the build log (`#print axioms`). Each unit's results are
in a section of their own, in unit order (plan: `notes/decisions.md`, "The server's apply").

Unit 0 (translation and scaffolding) proved no function of the package; its `Link.lean` links
the trust-boundary axioms (`pbutil.MustUnmarshalMessage` per message type, semver, zap, the
txn package's loggers, prometheus, `context.WithValue`, the quota's constructor and `Cost`) and
imports the txn package's and mvcc's results the package calls (`Put`, `DeleteRange`, `Range`,
`Txn`, `store.Rev`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

/-! ## Unit 1: the layers (`backend.go`, `quota.go`, `capped.go`, `corrupt.go`, `auth.go`)

To come: the backend's KV methods as the txn package's results (`Put`, `DeleteRange`, `Range`,
`Txn` at `context.TODO()`, the sole writer), `newHeader` (`store.Rev`), the one-liners over the
components' contracts; each wrapper's methods over its inner applier's (`applierSpec`), the
constructors' packaging lemmas; `chainStep` finished. -/

/-! ## Unit 2: the uber-applier and `Apply` (`uber_applier.go`, `apply.go`)

To come: `apply_kv` (a KV entry: applied by the txn model or rejected without a write),
`apply_readonly_no_write`, `apply_rejected_no_write`; `apply.Apply`'s spec, the server's
contract (`applierFor` a definition) with what the entry does to the log. -/

/-! ## Unit 0: the trust boundary and the callees linked elsewhere -/

#print axioms Perennial.EtcdGrove.apply.pbutil.wp_MustUnmarshalMessage
#print axioms Perennial.EtcdGrove.apply.semver.wp_MustParse
#print axioms Perennial.EtcdGrove.mvcc.store.wp_Rev
#print axioms Perennial.EtcdGrove.txn.wp_Txn

end apply
end EtcdGrove
end Perennial
