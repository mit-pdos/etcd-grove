/-
`types.NewURLs` (`client/pkg/v3/types/urls.go`).

Users: `cluster.memberAdd`, `cluster.MemberUpdate` (the URLs' check); the server (membership, 2e).

Proof sketch: per string `url.Parse` (trusted: `net/url`), the scheme and `host:port` checks
(`net.SplitHostPort`), the path check; the result sorted (`sort.Sort`). `urlsValid`'s meaning.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/pkg/v3/types/NewURLs.lean` (plain peer URLs only,
the URLs' parse described): any strings, the error case included; the parsed values not described.

Integration (I1): the result described by `urlsStrs`/`urlsAt` over `urlsNorm`/`urlsHosts` (2e's
and 2f's requests), made read-only for good (no caller writes it).

Margin: the URLs' other fields (scheme) are not described.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.pkg.v3.types.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Types

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

/-- `NewURLs(strs)`: the parsed URLs, read-only for good (their hosts and `String()` forms), or an
error exactly when they are not `urlsValid` (`urlsHosts ss = none`). -/
def NewURLs.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (ss : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ sl ↦*{dq} ss }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.types.NewURLs)) (Val #sl))
  {{ (us : GoSlice) (err : GoInterface), RET (PairV #us #err); sl ↦*{dq} ss ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ hs, ⌜urlsHosts ss = some hs⌝ ∗ urlsStrs us (urlsNorm ss) ∗
          urlsAt us hs) ∨
       ⌜err ≠ GoInterface.nil ∧ urlsHosts ss = none⌝) }}

end spec

end Types
end EtcdGrove
end Perennial
