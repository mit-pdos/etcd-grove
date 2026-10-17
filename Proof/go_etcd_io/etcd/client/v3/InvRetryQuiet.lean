/-
**The retry interceptor's quiet path** (etcd-io/etcd#21739, pr-verify, 2026-10-17): the
vocabulary of the specs saying which of `retry_interceptor.go`'s failure logs the interceptors do
not write when an attempt fails with a context status (`codes.Canceled`, `codes.DeadlineExceeded`:
what grpc returns for a call whose context is canceled, e.g. by `client.Close()`).

Logging has no effect in this repository's model of zap (`Spec/go_uber_org/zap/Logger__Warn.lean`,
`Logger__Error.lean`), so no postcondition can say a log was not written. The specs here say it
by what their proofs are given instead: `Client.unaryClientInterceptor.wp_proof_quiet` is proved
without any spec of `zap.Logger.Warn` (nor of `isSafeRetry`, `shouldRefreshToken`, `refreshToken`,
which follow the warning), so the proof cannot step over a call of `Warn`: every `Warn` call the
code makes on these inputs is unreachable. (`Client.streamClientInterceptor.wp_proof_quiet`, the
same without `zap.Logger.Error`.)

**A status code** (`statusCodeIs err c`): grpc's `status.Code(err)` returns `c`. Defined as that
triple (no assumption about grpc): a premise of the specs, which an invoker contract
(`grpcInvokerCtxErr`) or a caller supplies.

**A context status** (`ctxCodeErr err`): `status.Code(err)` is `DeadlineExceeded` (4) or
`Canceled` (1), what `isContextError` tests.

**A done context** (`ctxErrDone ci`): its `Err()` returns a non-nil error, for good (Go's contract
of `Context.Err`): the context of a client after `client.Close()`.

**The stream interceptor** (`etcdStreamInterceptorOk`, `etcdStreamInterceptorQuiet`): the contract
of what `Client.streamClientInterceptor` returns, over a streamer (grpc's `Streamer`, the next
stream interceptor or `ClientConn.newClientStream`) that returns (`grpcStreamerOk`), or that fails
only with context statuses (`grpcStreamerCtxErr`). The stream it returns is not specified.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`status.Code(err)` returns `c`** (persistent). -/
def statusCodeIs (err : GoInterface) (c : w32) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #c -∗
    WP (App (Val (@! google_golang_org.grpc.status.Code)) (Val #err)) {{ Φ }})

instance statusCodeIs_persistent (err : GoInterface) (c : w32) :
    Persistent (statusCodeIs (GF := GF) err c) := by
  unfold statusCodeIs; infer_instance

/-- **A context status** (persistent): `status.Code(err)` is `DeadlineExceeded` or `Canceled`. -/
def ctxCodeErr (err : GoInterface) : IProp GF :=
  iprop(statusCodeIs err (W32 4) ∨ statusCodeIs err (W32 1))

instance ctxCodeErr_persistent (err : GoInterface) : Persistent (ctxCodeErr (GF := GF) err) := by
  unfold ctxCodeErr; infer_instance

/-- **An invoker that fails only with context statuses** (persistent): `grpcInvokerOk`'s contract,
whose errors are moreover context statuses (`ctxCodeErr`): grpc's `invoke` on a context that is
canceled (`client.Close()` cancels the client's context) or past its deadline. -/
def grpcInvokerCtxErr (conn : Loc) (addr : GoString) (inv : GoFunc) : IProp GF :=
  iprop(□ ∀ (method : GoString) (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep) (m : Req.M)
      (Φ : Rep.M → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
      (inp out : Loc) (opts : GoSlice) (vs : List GoInterface) (ps : List Loc),
    {{ isGrpcRpc addr method Spec ∗ □ ▷ Spec m Φ ∗ ctxOk ctx cd ∗ Req.send inp m ∗
        Rep.own out ∗ opts ↦*□ vs ∗ ⌜∀ v ∈ vs, grpcOptOk ps v⌝ ∗ ([∗list] p ∈ ps, grpcPeerBuf p) }}
      (invokerCall inv #(GoInterface.ok ctx) #method
        #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)
        #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface) #conn #opts)
    {{ (err : GoInterface), RET #err; Req.send inp m ∗ ([∗list] p ∈ ps, grpcPeerBuf p) ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ statusErrOk err ∗ ctxCodeErr err ∗
            Rep.own out)) }})

instance grpcInvokerCtxErr_persistent (conn : Loc) (addr : GoString) (inv : GoFunc) :
    Persistent (grpcInvokerCtxErr (GF := GF) conn addr inv) := by
  unfold grpcInvokerCtxErr; infer_instance

/-- **The retry interceptor's quiet contract** (persistent): `etcdInterceptorOk`'s call, over an
invoker that fails only with context statuses (`grpcInvokerCtxErr`), with the same result. Proved
without a spec of `zap.Logger.Warn` (see the file header): such a call writes no warning. -/
def etcdInterceptorQuiet (ic : GoFunc) : IProp GF :=
  iprop(□ ∀ (conn : Loc) (addr : GoString) (ics : List GoFunc) (dopts : List GoInterface)
      (inv : GoFunc) (method : GoString) (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep)
      (m : Req.M) (Φ : Rep.M → IProp GF) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (inp out : Loc) (opts : GoSlice)
      (vs : List GoInterface),
    {{ grpcConn conn addr ics dopts ∗ grpcInvokerCtxErr conn addr inv ∗ isGrpcRpc addr method Spec ∗
        □ ▷ Spec m Φ ∗ ctxOk ctx cd ∗ Req.send inp m ∗ Rep.blank out ∗
        opts ↦*□ vs ∗ callOptsOk vs }}
      (interceptorCall ic #(GoInterface.ok ctx) #method
        #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)
        #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface) #conn inv #opts)
    {{ (err : GoInterface), RET #err; Req.send inp m ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ statusErrOk err)) }})

instance etcdInterceptorQuiet_persistent (ic : GoFunc) :
    Persistent (etcdInterceptorQuiet (GF := GF) ic) := by
  unfold etcdInterceptorQuiet; infer_instance

/-- **A done context** (persistent): `Err()` returns a non-nil error. -/
def ctxErrDone (ci : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ e : GoInterfaceOk, Φ #(GoInterface.ok e)) -∗
    WP (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #())) {{ Φ }})

instance ctxErrDone_persistent (ci : GoInterfaceOk) : Persistent (ctxErrDone (GF := GF) ci) := by
  unfold ctxErrDone; infer_instance

/-- A streamer's call `st(ctx, desc, cc, method, opts...)` (`grpc.Streamer`). -/
abbrev streamerCall (st : GoFunc) (ctx desc cc method opts : val) : Expr :=
  App (App (App (App (App (Val #st) (Val ctx)) (Val desc)) (Val cc)) (Val method)) (Val opts)

/-- A stream interceptor's call `ic(ctx, desc, cc, method, streamer, opts...)`
(`grpc.StreamClientInterceptor`). -/
abbrev cliStreamInterceptorCall (ic : GoFunc) (ctx desc cc method : val) (st : GoFunc) (opts : val) :
    Expr :=
  App (App (App (App (App (App (Val #ic) (Val ctx)) (Val desc)) (Val cc)) (Val method))
    (Val #st)) (Val opts)

/-- **A streamer** (persistent): on a context a client call takes, it returns a stream and an
error grpc's `status` accepts. -/
def grpcStreamerOk (st : GoFunc) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (desc cc : Loc)
      (method : GoString) (opts : GoSlice) (vs : List GoInterface),
    {{ ctxOk ctx cd ∗ opts ↦*□ vs }}
      (streamerCall st #(GoInterface.ok ctx) #desc #cc #method #opts)
    {{ (cs err : GoInterface), RET (PairV #cs #err); statusErrOk err }})

instance grpcStreamerOk_persistent (st : GoFunc) : Persistent (grpcStreamerOk (GF := GF) st) := by
  unfold grpcStreamerOk; infer_instance

/-- **A streamer failing only with context statuses** (persistent): `grpcStreamerOk`, whose
errors are moreover `nil` or context statuses (`ctxCodeErr`): grpc's `newClientStream` on a
canceled context. -/
def grpcStreamerCtxErr (st : GoFunc) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (desc cc : Loc)
      (method : GoString) (opts : GoSlice) (vs : List GoInterface),
    {{ ctxOk ctx cd ∗ opts ↦*□ vs }}
      (streamerCall st #(GoInterface.ok ctx) #desc #cc #method #opts)
    {{ (cs err : GoInterface), RET (PairV #cs #err); statusErrOk err ∗
        (⌜err = GoInterface.nil⌝ ∨ ctxCodeErr err) }})

instance grpcStreamerCtxErr_persistent (st : GoFunc) :
    Persistent (grpcStreamerCtxErr (GF := GF) st) := by
  unfold grpcStreamerCtxErr; infer_instance

/-- **The retry stream interceptor's contract** (persistent): called on a context a client call
takes, a read-only stream descriptor, a streamer that returns, and the client's call options, it
returns (a stream and an error, unspecified). -/
def etcdStreamInterceptorOk (ic : GoFunc) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (desc : Loc)
      (dv : google_golang_org.grpc.StreamDesc) (cc : Loc) (method : GoString) (st : GoFunc)
      (opts : GoSlice) (vs : List GoInterface),
    {{ ctxOk ctx cd ∗ desc ↦□ dv ∗ grpcStreamerOk st ∗ opts ↦*□ vs ∗ callOptsOk vs }}
      (cliStreamInterceptorCall ic #(GoInterface.ok ctx) #desc #cc #method st #opts)
    {{ (cs err : GoInterface), RET (PairV #cs #err); True }})

instance etcdStreamInterceptorOk_persistent (ic : GoFunc) :
    Persistent (etcdStreamInterceptorOk (GF := GF) ic) := by
  unfold etcdStreamInterceptorOk; infer_instance

/-- **The retry stream interceptor's quiet contract** (persistent): `etcdStreamInterceptorOk`'s
call on a done context (`ctxErrDone`) over a streamer failing only with context statuses. Proved
without a spec of `zap.Logger.Error`: such a call logs no error, given that `getToken` fails only
with context statuses on a done context (`Client.getToken.spec_ctx`, a hypothesis: false, see
`Spec/go_etcd_io/etcd/client/v3/Client__getToken.lean`). -/
def etcdStreamInterceptorQuiet (ic : GoFunc) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (desc : Loc)
      (dv : google_golang_org.grpc.StreamDesc) (cc : Loc) (method : GoString) (st : GoFunc)
      (opts : GoSlice) (vs : List GoInterface),
    {{ ctxOk ctx cd ∗ ctxErrDone ctx ∗ desc ↦□ dv ∗ grpcStreamerCtxErr st ∗ opts ↦*□ vs ∗
        callOptsOk vs }}
      (cliStreamInterceptorCall ic #(GoInterface.ok ctx) #desc #cc #method st #opts)
    {{ (cs err : GoInterface), RET (PairV #cs #err); True }})

instance etcdStreamInterceptorQuiet_persistent (ic : GoFunc) :
    Persistent (etcdStreamInterceptorQuiet (GF := GF) ic) := by
  unfold etcdStreamInterceptorQuiet; infer_instance

end defs

end EtcdGrove
end Perennial
