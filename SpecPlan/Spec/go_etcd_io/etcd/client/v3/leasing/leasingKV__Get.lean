/-
`(*leasingKV).Get` (`client/v3/leasing/kv.go`).

Users: the integration tests (`lkv.Get(ctx, "k")`, with `WithSerializable`, `WithRev`, `WithPrefix`,
`WithKeysOnly`, `WithCountOnly`, revision filters: `TestLeasingGetWithOpts`, `TestLeasingRevGet`,
`TestLeasingGetSerializable`); the proxy goes through `Do` (`leasingKV.Do.spec`). Snippets:
`leasing/reads.go` (`ReqGetKey`, `ReqGetThenPlainGet`), `leasing/unmet.go` (`UnmetReadYourWrite`,
`UnmetGetOptions`).

Proof sketch: `OpGet.spec` (W0) builds `opAt op (opGetM key gs)` (its premise
`¬ prefixAndFromKey gs`; the options given back); then `leasingKV.get.spec` at that `op` (a range,
`.range (opGetM key gs).rangeReq`), which takes the caller's update unchanged.

Changes: the old specs (`specs-ref`'s `leasingKV__*.lean`) took the old client's
contracts at prefix `[]` (`isEtcdKV`, `isEtcdTxnKVO`), a revision certificate `etcdReached lo`, a
size bound (`OpShape`), and returned implementation outcomes (`getCached`, `getAcquired`,
`getNotAcquired`, `putCommitted`, `opCommitted`: the cache's states, its log, the history premise
`LeasingProtocol`); restated over W0's `etcdState` as a weakening of the KV contract (`Api.lean`'s
header): the caller's update persistent and over `lstep` (`LStep` with the marks of the keys
written through the KV: a cached answer is W0's serializable one for an unmarked key, the old proof's
"Theorem 1"), an error settling nothing; no size bound
(W0: the gRPC boundary fails on an oversized message), no certificate (the answer's revision is in
the update's state), no history premise (the contract claims nothing a protocol violation could
break). Also: the open token and the thread token as before (`leasingOpen`,
`threadTok`); the outcomes `getCached`/`getAcquired`/`getNotAcquired` are now one cached-answer
step (`CachedAns`), the server's answers W0's `getReply`.

Margin: an answer from a member is linearized (or serializable as asked); a cached answer (only
for a single key at revision `0`) is W0's serializable answer for a key never written through this
KV (unmarked: the program holds its `lkvClean`), up to a keys-only answer's lease, and only shaped
(`CachedRange`) for a marked key (`issues/leasing-update-stale.md`); a failed acquisition answers
a plain get, ignoring the options.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `lkv.Get` meets the leasing contract's `Get` (`LKV.GetTriple`). -/
def leasingKV.Get.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (q : Qp),
  LKV.GetTriple (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"Get")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ lkvOpen γL q)) γ who pfx γL

end spec

end Leasing
end EtcdGrove
end Perennial
