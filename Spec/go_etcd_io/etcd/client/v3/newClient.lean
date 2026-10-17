/-
`clientv3.newClient(cfg)` (`client/v3/client.go`, behind `New`) as PR etcd-io/etcd#21714 changes it:
its dial error and its token error are wrapped with the endpoints
(`fmt.Errorf("etcdclient: dialing [%s] failed: %w", strings.Join(cfg.Endpoints, ";"), err)`,
`communicating with` for the token), where it returned the callee's error itself. Lean-first (no
Rocq counterpart); see `Proof/go_etcd_io/etcd/client/v3/InvNewClient.lean`.

The spec of the old code differs in two of `newClientErr`'s disjuncts only: where the new code
returns an error `e` wrapping the dial's (or `getToken`'s) error `inner` (`fmt.wrapsErr e inner`),
the old returned `inner` itself (`e = inner`). A caller that compares the error with `==` (or
type-asserts it, `err.(rpctypes.EtcdError)`) sees a different error; one that uses `errors.Is`
sees the same (`errorIsTree_wrap`); one that prints it sees a longer message.
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

/-- `newClient(cfg)`, for a configuration `cv` read-only at `cfg` (the caller's, never written:
`New`'s copy) whose endpoints `xs` are read-only too, and whose `Context` is none or a context
(`cfgCtxOk`), with the package's variables (`newClientVars`): either
* no error and a client `c` built (`clientBuiltAt`: its fields fixed, its logger non-nil, a token
  with a credential bundle, its connection and services set) that the retry interceptor can use
  (`retryClientOk`, which the interceptor's proofs assume of a client `New` built), or
* no client and an error `e` whose `Error()` returns some string, of one of the origins
  `newClientErr` lists: in particular, for a failed dial or token request, **an error wrapping the
  callee's error** (`fmt.wrapsErr`, what the PR changes). -/
abbrev newClient.spec : Prop :=
  ∀ (cfgp : Loc) (cv : go_etcd_io.etcd.client.v3.Config) (xs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ newClientVars ∗
      cfgp ↦□ cv ∗ cv.Endpoints' ↦*□ xs ∗ cfgCtxOk cv.Context' }}
    (App (Val (@! go_etcd_io.etcd.client.v3.newClient)) (Val #cfgp))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = GoInterface.nil⌝ ∗ clientBuiltAt c ∗ retryClientOk c) ∨
      (⌜c = null⌝ ∗ ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errorStringSpec e ∗
        newClientErr cv xs e) }}

end spec

end EtcdGrove
end Perennial
