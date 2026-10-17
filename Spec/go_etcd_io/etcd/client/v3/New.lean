/-
`clientv3.New(cfg)` (`client/v3/client.go`), the exported constructor: `ErrNoAvailableEndpoints`
for no endpoints, else `newClient(&cfg)` (pr-verify etcd#21714: the API through which the PR's
change reaches users). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvNewClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (errorStringSpec)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `New(cfg)`, for a configuration `cv` whose endpoints `xs` and dial options `ds` are read-only (the
caller does not write them after: the client keeps the slices) and whose `Context` is none or a context: a client
built (`clientBuiltAt`, `retryClientOk`), or no client and an error whose `Error()` returns some
string: `ErrNoAvailableEndpoints` itself for no endpoints, else one of `newClient`'s
(`newClientErr`: for a failed dial or token request, an error wrapping the callee's). -/
abbrev clientv3.New.spec : Prop :=
  ∀ (cv : go_etcd_io.etcd.client.v3.Config) (xs : List GoString) (ds : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ newClientVars ∗
      cv.Endpoints' ↦*□ xs ∗ cv.DialOptions' ↦*□ ds ∗ cfgCtxOk cv.Context' }}
    (App (Val (@! go_etcd_io.etcd.client.v3.New)) (Val #cv))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = GoInterface.nil⌝ ∗ clientBuiltAt c ∗ retryClientOk c) ∨
      (⌜c = null⌝ ∗ ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errorStringSpec e ∗
        ((⌜xs = []⌝ ∗
          globalAddr go_etcd_io.etcd.client.v3.ErrNoAvailableEndpoints ↦□ (GoInterface.ok e)) ∨
          newClientErr cv xs e)) }}

end spec

end EtcdGrove
end Perennial
