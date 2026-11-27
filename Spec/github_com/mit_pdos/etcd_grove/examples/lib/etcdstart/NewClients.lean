/-
`NewClients(eps, lg)` (`examples/lib/etcdstart/common.go`; 2026-10-23, `notes/client-timeouts-plan.md` D-T1;
linkv3p's `newClient` until then, D27-D29): `clientv3.New` of a configuration with the endpoints
`eps`, the logger `lg`, the examples' timeouts (`DialTimeout`, the keepalive pair `KeepAliveTime`/
`KeepAliveTimeout`: etcdctl's defaults), etcd's default retries and no proxy (`grpc.WithNoProxy()`,
since 2026-11-24, `notes/putget-dist-plan.md` §12, finding F1). Lean-first (no Rocq counterpart).

**The triple:** for plain endpoints (`plainEndpoints`, `clientv3.New`'s premise: at least one, each
plain), read-only, and a logger, from the package's fact: the client of those endpoints
(`isNewClient` at any watch environment `V`, the caller's choice; its `KV` a `*kv` over its
connection whose attempts carry the context's own token only, `clientTokAt` at `False`: the
client has no user name, 2026-10-29 for authkv's anonymous principals) that dials with no proxy
(`clientNoProxy`: its configuration's one dial option is `WithNoProxy()`'s; what the
cross-machine axioms of `examples/etcd/dist` take) and `nil`, or an error and `null`
(`clientv3.New`'s two cases). A write through it is sent at most once when the endpoints are
refusal-free (`clientWriteOnce`, D29), which the caller establishes. The timeouts are no premise:
`clientCfgOk` leaves `DialTimeout` free (`newClient`'s proof covers it) and takes any keepalive
(D28, `kaOpts`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Base
public import Spec.go_etcd_io.etcd.client.v3.New
public import Spec.google_golang_org.grpc.WithNoProxy

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- See the file header. -/
abbrev NewClients.spec : Prop :=
  ∀ (eps : GoSlice) (addrs : List GoString) (lg : Loc) (V : client.WEnv GF),
  threadBound GF ≤ 2 ^ 30 → plainEndpoints addrs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗ levelTok 0 ∗ (-- (sweep repairs 1, R1-2) the logger a zap logger (until then `lg ≠ null`)
      zapLoggerOk lg ∗
      eps ↦*□ addrs) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClients)) (Val #eps))
      (Val #lg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ isNewClient cl addrs V ∗
        clientTokAt cl addrs (fun _ => iprop(False)) ∗ clientNoProxy cl ∗
        -- (F7 S5, 2026-11-26) its configuration sets no token, user or password
        ∃ cfg : go_etcd_io.etcd.client.v3.Config, clientF cl go!"cfg" ↦□ cfg ∗
          ⌜cfg.Token' = [] ∧ cfg.Username' = go!"" ∧ cfg.Password' = go!""⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ cl = null⌝) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
