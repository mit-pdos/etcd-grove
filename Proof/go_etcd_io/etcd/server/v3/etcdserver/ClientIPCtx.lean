/-
**The request path's contexts answer `Value(ClientIPContextKey{})`** (PR etcd#22259,
`pr-verify/etcd-22259`): a trust-boundary axiom. Lean-first (no Rocq counterpart).

Since the PR, the auth store's `AuthInfoFromCtx` logs `ClientIPFromContext(ctx)` on an invalid
token, which calls `ctx.Value(ClientIPContextKey{})` (`auth.ctxClientIPOk`). The server reaches
`AuthInfoFromCtx` (through `isReqAuth`) with a context described by `mvcc.txnCtx` only: an
`isContext` (Perennial's, which specifies `Value` for the key `&cancelCtxKey` only) or one whose
`Done()` is `nil`. Neither says what `Value` does at another key, so the fact is assumed here:
every context that reaches `AuthInfoFromCtx` is built by Go's `context` package (`Background`,
`TODO`, `WithValue`, `WithCancel`, `WithTimeout`) over grpc's server context, whose `Value`
methods return at every comparable key (a `valueCtx` returns its value at an equal key and asks
its parent otherwise; grpc's stream context is such a chain). What it returns is not assumed
(`ctxClientIPOk` holds for any result: the type assertion `.(string)` decides it). The same
assumption is already implicit in `metadata.FromIncomingContext.spec` (an axiom over any
context), which `AuthInfoFromCtx` called before the PR. The general fix would be a `Value`
clause for every comparable key in Perennial's `isContext` (`notes/STATUS.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.ClientIP
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3

section ax
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A request-path context answers `Value(ClientIPContextKey{})`** (see the file header). -/
axiom auth.ctxClientIPOk_of_txnCtx (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    mvcc.txnCtx ctx cd ⊢ auth.ctxClientIPOk (GF := GF) (GoInterface.ok ctx)

end ax

end EtcdGrove
end Perennial
