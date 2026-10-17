/-
What `clientv3.NewCtxClient` (`client/v3/client.go`) needs and gives (PR etcd-io/etcd#21809, which
makes it set the client's call options to `defaultCallOpts`, as `newClient` does). Lean-first (no
Rocq counterpart); on the verification branch `pr-verify/etcd-21809` only.

**The default call options** (`defaultCallOptsVar dsl`): an assumption about the package's
initialization (axiomatized: `defaultCallOpts.init`), as `clientWatchVars`: the package variable
`defaultCallOpts` holds, never written, the slice `dsl` of `options.go`'s three options
(`grpc.WaitForReady(true)`, `grpc.MaxCallSendMsgSize(2 MiB)`, `grpc.MaxCallRecvMsgSize(MaxInt32)`,
`defaultCallOptVals`: grpc option values that hold only scalars, so `callOptsAt dsl`), full
(`len = cap`, a composite literal's slice). Nothing in etcd writes `defaultCallOpts` after
initialization (its only uses: `options.go`, `client.go`'s `newClient` and `NewCtxClient`); every
`append` to a client's call options (`lease.go`, `maintenance.go`, `retryKVClient.Range`) copies,
the slice being full.

**The options** (`ctxClientOptOk f`): a `NewCtxClient` `Option` (`func(*Client)`) is called on the
new client before it is returned, in the caller's goroutine; the contract assumed of one is that it
writes only the client's logger (`c.lg`, an `atomic.Pointer[zap.Logger]`), to any value, `nil`
included. The package's only `Option`, `WithZapLogger(lg)`, does exactly that (its proof). The contract is
narrower than Go's: an `Option` from outside the package cannot write `callOpts` (an unexported
field), but may write the exported fields (`c.KV = ...`); a wider contract, every field but
`callOpts`, would cover those callers too.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvClient

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`options.go`'s three default call options**, as grpc builds them:
`grpc.WaitForReady(true)` is `FailFastCallOption{FailFast: false}`,
`grpc.MaxCallSendMsgSize(2 * 1024 * 1024)` and `grpc.MaxCallRecvMsgSize(math.MaxInt32)` the
size options with those values. -/
def defaultCallOptVals : List GoInterface :=
  [interface.mkOk google_golang_org.grpc.FailFastCallOption.ty
      #(google_golang_org.grpc.FailFastCallOption.mk false),
    interface.mkOk google_golang_org.grpc.MaxSendMsgSizeCallOption.ty
      #(google_golang_org.grpc.MaxSendMsgSizeCallOption.mk (W64 (2 * 1024 * 1024))),
    interface.mkOk google_golang_org.grpc.MaxRecvMsgSizeCallOption.ty
      #(google_golang_org.grpc.MaxRecvMsgSizeCallOption.mk (W64 2147483647))]

/-- **The package variable `defaultCallOpts`** (persistent; an assumption about the package's
initialization, see the file header): it holds `dsl`, a full read-only slice of the three
default call options (`defaultCallOptVals`). -/
def defaultCallOptsVar (dsl : GoSlice) : IProp GF :=
  iprop(globalAddr go_etcd_io.etcd.client.v3.defaultCallOpts ↦□ dsl ∗
    dsl ↦*□ defaultCallOptVals ∗ ⌜dsl.len = dsl.cap⌝)

instance defaultCallOptsVar_persistent (dsl : GoSlice) :
    Persistent (defaultCallOptsVar (GF := GF) dsl) := by
  unfold defaultCallOptsVar; infer_instance

/-- The default call options are ones the client passes (`callOptsAt`: what `NewKV`'s and the KV
path's proofs need of a client's call options). -/
theorem defaultCallOptsVar_callOptsAt (dsl : GoSlice) :
    defaultCallOptsVar (GF := GF) dsl ⊢ callOptsAt dsl := by
  unfold defaultCallOptsVar
  iintro #⟨-, #Hsl, %Hcap⟩
  unfold callOptsAt
  iexists defaultCallOptVals
  iframe #
  isplitl []
  · ipureintro; exact Hcap
  have Hok : ∀ (t : go.GoType) (x : val), t ∈ grpcScalarOptTys →
      ⊢ callOptOk (GF := GF) (interface.mkOk t x) := by
    intro t x Ht
    unfold callOptOk
    iintro
    ileft
    ipureintro
    exact ⟨t, x, rfl, Ht⟩
  ihave #H1 := Hok google_golang_org.grpc.FailFastCallOption.ty
    #(google_golang_org.grpc.FailFastCallOption.mk false) (by simp [grpcScalarOptTys])
  ihave #H2 := Hok google_golang_org.grpc.MaxSendMsgSizeCallOption.ty
    #(google_golang_org.grpc.MaxSendMsgSizeCallOption.mk (W64 (2 * 1024 * 1024)))
    (by simp [grpcScalarOptTys])
  ihave #H3 := Hok google_golang_org.grpc.MaxRecvMsgSizeCallOption.ty
    #(google_golang_org.grpc.MaxRecvMsgSizeCallOption.mk (W64 2147483647))
    (by simp [grpcScalarOptTys])
  unfold callOptsOk defaultCallOptVals
  iapply BigSepL.bigSepL_cons.2
  isplitl []
  · iexact H1
  iapply BigSepL.bigSepL_cons.2
  isplitl []
  · iexact H2
  iapply BigSepL.bigSepL_singleton.2
  iexact H3

/-- **A `NewCtxClient` option `f`** (persistent; see the file header): `f(c)` writes only `c.lg`. -/
def ctxClientOptOk (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (c lg : Loc),
    {{ sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger) (clientLgAddr c)
        (DFrac.own 1) lg }}
      (App (Val #f) (Val #c))
    {{ RET #(); ∃ lg' : Loc,
        sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger) (clientLgAddr c)
          (DFrac.own 1) lg' }})

instance ctxClientOptOk_persistent (f : GoFunc) : Persistent (ctxClientOptOk (GF := GF) f) := by
  unfold ctxClientOptOk; infer_instance

/-- **The `[]Option` slice `sl`** (read-only): every option one of `ctxClientOptOk`. -/
def ctxClientOptsAt (sl : GoSlice) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ [∗list] f ∈ fs, ctxClientOptOk f)

instance ctxClientOptsAt_persistent (sl : GoSlice) :
    Persistent (ctxClientOptsAt (GF := GF) sl) := by
  unfold ctxClientOptsAt; infer_instance

/-- The client's logger, owned, made the invariant `isClientLogger` (what `GetLogger` needs). -/
theorem isClientLogger_alloc (c lg : Loc) (Hnn : lg ≠ null) :
    sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger) (clientLgAddr c)
      (DFrac.own 1) lg ⊢ |={⊤}=> isClientLogger (GF := GF) c := by
  iintro Hp
  unfold isClientLogger
  iapply inv_alloc
  inext
  iexists lg
  iframe Hp
  ipureintro; exact Hnn

end defs

end EtcdGrove
end Perennial
