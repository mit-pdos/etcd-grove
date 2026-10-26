/-
`NewClients(eps, lg)` (`examples/common/common.go`; 2026-10-23, `notes/client-timeouts-plan.md` D-T1;
linkv3p's `newClient` until then, D27-D29): `clientv3.New` of a configuration with the endpoints
`eps`, the logger `lg`, the examples' timeouts (`DialTimeout`, the keepalive pair `KeepAliveTime`/
`KeepAliveTimeout`: etcdctl's defaults) and etcd's default retries. Lean-first (no Rocq counterpart).

**The triple:** for plain endpoints (`plainEndpoints`, `clientv3.New`'s premise: at least one, each
plain), read-only, and a logger, from the package's fact: the client of those endpoints
(`isNewClient` at any watch environment `V`, the caller's choice) and `nil`, or an error and `null`
(`clientv3.New`'s two cases). A write through it is sent at most once when the endpoints are
refusal-free (`clientWriteOnce`, D29), which the caller establishes. The timeouts are no premise:
`clientCfgOk` leaves `DialTimeout` free (`newClient`'s proof covers it) and takes any keepalive
(D28, `kaOpts`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Base
public import Spec.go_etcd_io.etcd.client.v3.New

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev NewClients.spec : Prop :=
  ∀ (eps : GoSlice) (addrs : List GoString) (lg : Loc) (V : client.WEnv GF),
  threadBound GF ≤ 2 ^ 31 → lg ≠ null → plainEndpoints addrs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      eps ↦*□ addrs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.NewClients)) (Val #eps))
      (Val #lg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err);
      (⌜err = GoInterface.nil⌝ ∗ isNewClient cl addrs V) ∨
      ⌜err ≠ GoInterface.nil ∧ cl = null⌝ }}

end spec

end common
end EtcdGrove
end Perennial
