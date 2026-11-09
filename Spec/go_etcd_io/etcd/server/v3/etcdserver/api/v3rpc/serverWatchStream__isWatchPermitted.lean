/-
`(*serverWatchStream).isWatchPermitted(wcr)` (`watch.go`): the permission check of a create.

**Users.** `recvLoop` (`watch.go:289`), on each create with a non-negative start revision, its key
already normalized (`"\x00"` for an empty one) and its range end as received.

**Proof sketch.** `sws.gRPCStream.Context()` (`srvWatchStreamAt_context`: a context with
`srvCtxPrin ctx who`); `sws.ag.AuthInfoFromCtx(ctx)` (`ag` the member as `AuthGetter`,
`watchMemberAt`'s triple, 2c over 3d: an error, or `nil`, or an `*AuthInfo` naming `who`'s user
with its token's auth revision; with `ClientCertAuthEnabled` and no token, `AuthInfoFromTLS`'s:
the TLS peer's CN, which `srvCtxPrin` must then name, `req/go_etcd_io_etcd_server_v3_auth.md`); `nil` is replaced by `&auth.AuthInfo{}` (no user, revision `0`);
`sws.ag.AuthStore()` (the member's auth store), `IsRangePermitted(info, wcr.Key, wcr.RangeEnd)`
(3d, with the thread token as the store's reader slot: `nil` only if a reached state `σa` has auth
off, or has `info`'s user, of the root role or with read permission over the range: `σa.permits
who [(.read, ⟨key, end⟩)] []`, the model's `KeyRange.mem` reading `"\x00"` as from-key as
`rangePermCache` does). `req/go_etcd_io_etcd_server_v3_auth.md` and
`req/go_etcd_io_etcd_server_v3_etcdserver.md`, `## from 2b`.

**Changes** from `specs-ref`'s file: the auth store's reader resource (`r.srv.E.RD`), the lower
bound check (`srvAuthLb`), the published-index bound `n` (`authPubLbM`) and the apply package's
class (`apply.classResFrom`, `principalBoundI`, `applyErrIs`) replaced by the cluster's model: a
reached state `σa` that permits the stream's principal (`etcdLb γ σa`, `State.permits`), one
statement for auth on and off; the key-length premise (`k.length < 2 ^ 63 - 1`) dropped (a slice's
length fits by construction); the thread token in place of the reader resource.

**Margin.** A refusal's error is not classified here (`recvLoop` maps it with `errors.Is`, any
error being one of auth's or not).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchInternal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`sws.isWatchPermitted(wcr)`**: `nil` only if a state the cluster reached permits the stream's
principal to read the range `[Key, RangeEnd)`. -/
def serverWatchStream.isWatchPermitted.spec : Prop :=
  ∀ (sws : Loc) (γ : EtcdModel.Cluster) (who : Principal) (st : GoInterface) (g : WatchStreamNames)
    (wcr : Loc) (ks es : GoSlice) (k e : GoString) (dk de : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      swsAt sws γ who st g ∗ threadTok ∗
      wcr.[etcdserverpb.WatchCreateRequest, go!"Key"] ↦{dk} ks ∗ ks ↦*□ k ∗
      wcr.[etcdserverpb.WatchCreateRequest, go!"RangeEnd"] ↦{de} es ∗ es ↦*□ e }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"isWatchPermitted"))
      (Val #wcr))
  {{ (err : GoInterface), RET #err; threadTok ∗
      wcr.[etcdserverpb.WatchCreateRequest, go!"Key"] ↦{dk} ks ∗
      wcr.[etcdserverpb.WatchCreateRequest, go!"RangeEnd"] ↦{de} es ∗
      (⌜err ≠ GoInterface.nil⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ σa : State, etcdLb γ σa ∗
          ⌜σa.permits who [(.read, { key := k, rangeEnd := e })] []⌝)) }}

end spec

end V3rpc
end EtcdGrove
end Perennial
