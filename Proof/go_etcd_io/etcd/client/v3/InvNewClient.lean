/-
What `clientv3.newClient` (`client/v3/client.go`, behind `clientv3.New`) needs and gives:
pr-verify etcd#21714, which makes it wrap its dial and token errors with the endpoints
(`fmt.Errorf("etcdclient: dialing [%s] failed: %w", strings.Join(cfg.Endpoints, ";"), err)`, and
`communicating with` for the token). Lean-first (no Rocq counterpart); on the verification branch
`pr-verify/etcd-21714` only.

**The package variables** (`newClientVars`): an assumption about the package's initialization
(axiomatized: `ErrMutuallyExclusiveCfg.init`, ...), as `clientWatchVars`: the error variables
`ErrMutuallyExclusiveCfg` and `ErrNoAvailableEndpoints` hold fixed non-nil errors whose `Error()`
returns some string (`errors.New`'s), and `defaultCallOpts`, `defaultWaitForReady`,
`defaultMaxCallSendMsgSize`, `defaultMaxCallRecvMsgSize` fixed values (`options.go`). Nothing in
etcd writes them after initialization.

**The client as it is built.** `newClient` allocates the `*Client`, writes its fields, and from
the dial on writes only `conn` and the six service interfaces; its callees (names only: the dial,
`SetEndpoints`, `NewLease`, ..., `Close`, `checkVersion`, `autoSync`) and the gRPC connection's
interceptors read the fields it no longer writes. So the proof makes them read-only at the dial
(`clientFixed c cl`: `cfg`, `creds`, `resolver`, `epMu`, `ctx`, `cancel`, `Username`, `Password`,
`Token`, `authTokenBundle`, `callOpts` are `cl`'s, read-only; the logger the invariant
`isClientLogger`; a token comes with a bundle), then `conn` (`clientConnAt`), then the services
(`clientBuiltAt`), which is what the callees' contracts take. `endpoints` is protected by `epMu`
(`SetEndpoints` takes it; not modeled). The slices the fields hold (the endpoints, the dial
options, the call options) are never written: the caller's `Config` is read-only (an assumption on
`New`'s caller, which Go does not check: `newClient` keeps `cfg.Endpoints` itself, not a copy).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry
public import Spec.fmt.ErrorfWrap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (errorStringSpec)

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The package variables `newClient` and `New` read** (persistent; see the file header). -/
def newClientVars : IProp GF :=
  iprop((∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.client.v3.ErrMutuallyExclusiveCfg ↦□ (GoInterface.ok e) ∗
      errorStringSpec e) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.client.v3.ErrNoAvailableEndpoints ↦□ (GoInterface.ok e) ∗
      errorStringSpec e) ∗
    (∃ sl : GoSlice, globalAddr go_etcd_io.etcd.client.v3.defaultCallOpts ↦□ sl) ∗
    (∃ o : GoInterface, globalAddr go_etcd_io.etcd.client.v3.defaultWaitForReady ↦□ o) ∗
    (∃ o : GoInterface, globalAddr go_etcd_io.etcd.client.v3.defaultMaxCallSendMsgSize ↦□ o) ∗
    (∃ o : GoInterface, globalAddr go_etcd_io.etcd.client.v3.defaultMaxCallRecvMsgSize ↦□ o))

instance newClientVars_persistent : Persistent (newClientVars (GF := GF)) := by
  unfold newClientVars; infer_instance

/-- **The fields of the client `c` fixed from the dial on** (persistent): those of the record
`cl`, read-only; the logger (`isClientLogger`); a token comes with a credential bundle. -/
def clientFixed (c : Loc) (cl : go_etcd_io.etcd.client.v3.Client) : IProp GF :=
  iprop(⌜c ≠ null⌝ ∗ isClientLogger c ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"cfg" c ↦□ cl.cfg' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"creds" c ↦□ cl.creds' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"resolver" c ↦□ cl.resolver' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" c ↦□ cl.epMu' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" c ↦□ cl.ctx' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"cancel" c ↦□ cl.cancel' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Username" c ↦□ cl.Username' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Password" c ↦□ cl.Password' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Token" c ↦□ cl.Token' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"authTokenBundle" c ↦□ cl.authTokenBundle' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"callOpts" c ↦□ cl.callOpts' ∗
    ⌜cl.Token' ≠ go!"" → cl.authTokenBundle' ≠ GoInterface.nil⌝)

instance clientFixed_persistent (c : Loc) (cl : go_etcd_io.etcd.client.v3.Client) :
    Persistent (clientFixed (GF := GF) c cl) := by
  unfold clientFixed; infer_instance

/-- **The client `c` at its dial** (persistent): its fixed fields. -/
def clientDialAt (c : Loc) : IProp GF :=
  iprop(∃ cl : go_etcd_io.etcd.client.v3.Client, clientFixed c cl)

instance clientDialAt_persistent (c : Loc) : Persistent (clientDialAt (GF := GF) c) := by
  unfold clientDialAt; infer_instance

/-- **The client `c` once dialed** (persistent): its fixed fields and its connection. -/
def clientConnAt (c : Loc) : IProp GF :=
  iprop(∃ cl : go_etcd_io.etcd.client.v3.Client, clientFixed c cl ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" c ↦□ cl.conn')

instance clientConnAt_persistent (c : Loc) : Persistent (clientConnAt (GF := GF) c) := by
  unfold clientConnAt; infer_instance

/-- **The client `c` built** (persistent): its fixed fields, its connection and its six service
interfaces, all read-only (what `Close`, `checkVersion` and `autoSync` read; what `New` returns). -/
def clientBuiltAt (c : Loc) : IProp GF :=
  iprop(∃ cl : go_etcd_io.etcd.client.v3.Client, clientFixed c cl ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" c ↦□ cl.conn' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Cluster" c ↦□ cl.Cluster' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" c ↦□ cl.KV' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Lease" c ↦□ cl.Lease' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Watcher" c ↦□ cl.Watcher' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Auth" c ↦□ cl.Auth' ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Maintenance" c ↦□ cl.Maintenance')

instance clientBuiltAt_persistent (c : Loc) : Persistent (clientBuiltAt (GF := GF) c) := by
  unfold clientBuiltAt; infer_instance

/-- A client with its fixed fields is what the retry interceptor (and `getToken`) take of it:
**`newClient` establishes `retryClientOk`**, which the interceptor's proofs assume of a client
`clientv3.New` built. -/
theorem retryClientOk_of_clientFixed (c : Loc) (cl : go_etcd_io.etcd.client.v3.Client) :
    clientFixed (GF := GF) c cl ⊢ retryClientOk c := by
  unfold clientFixed retryClientOk
  iintro #⟨%Hc, #Hlg, -, -, -, -, -, -, -, -, #Htok, #Hatb, -, %Hta⟩
  iframe #
  isplitl []
  · ipureintro; exact Hc
  ipureintro; exact Hta

/-- **The `Context` of the caller's `Config`**: none (`nil`: `newClient` uses `context.TODO()`),
or a context of Perennial's model (`isContext`). -/
def cfgCtxOk (ctx : GoInterface) : IProp GF :=
  iprop(⌜ctx = GoInterface.nil⌝ ∨
    ∃ (ci : GoInterfaceOk) (s : context.ContextDesc (IProp GF)), ⌜ctx = GoInterface.ok ci⌝ ∗
      context.isContext ci s)

instance cfgCtxOk_persistent (ctx : GoInterface) : Persistent (cfgCtxOk (GF := GF) ctx) := by
  unfold cfgCtxOk; infer_instance

/-- **Where an error of `newClient(cfg)` comes from** (persistent), for the configuration `cv`
whose endpoints are `xs`:
* `ErrMutuallyExclusiveCfg` itself, for a token with a user name or password;
* the logger's construction (`cfg.LogConfig.Build()`, `logutil.CreateDefaultZapLogger`), when the
  configuration gives no logger;
* the size check (`fmt.Errorf` of the two limits), when the receive limit is set and below the
  send limit;
* the endpoints check (`errors.New`), when there are none;
* **the dial** (`dialWithBalancer`): an error wrapping (`fmt.wrapsErr`) the dial's own error
  `inner` (one whose `Error()` returns some string), **the PR's first change**: before it, the
  error was `inner` itself;
* **the token** (`getToken`): an error wrapping a client error `inner` (`clientErrOk`: a leaf
  error grpc's `status` accepts, an `rpctypes.EtcdError` when typed), **the PR's second change**:
  before it, the error was `inner` itself;
* the version check (`checkVersion`), when `RejectOldCluster` is set.
The message (with the endpoints, `strings.Join(xs, ";")`) is not stated: the model of `fmt`
does not format. -/
def newClientErr (cv : go_etcd_io.etcd.client.v3.Config) (xs : List GoString)
    (e : GoInterfaceOk) : IProp GF :=
  iprop((⌜cv.Token' ≠ go!"" ∧ (cv.Username' ≠ go!"" ∨ cv.Password' ≠ go!"")⌝ ∗
      globalAddr go_etcd_io.etcd.client.v3.ErrMutuallyExclusiveCfg ↦□ (GoInterface.ok e)) ∨
    ⌜cv.Logger' = null⌝ ∨
    ⌜0 < sint.Z cv.MaxCallRecvMsgSize' ∧ sint.Z cv.MaxCallRecvMsgSize' < sint.Z cv.MaxCallSendMsgSize'⌝ ∨
    ⌜xs = []⌝ ∨
    (∃ inner : GoInterfaceOk, errorStringSpec inner ∗ fmt.wrapsErr e inner) ∨
    (∃ inner : GoInterfaceOk, clientErrOk (GoInterface.ok inner) ∗ fmt.wrapsErr e inner) ∨
    ⌜cv.RejectOldCluster' = true⌝)

instance newClientErr_persistent (cv : go_etcd_io.etcd.client.v3.Config) (xs : List GoString)
    (e : GoInterfaceOk) : Persistent (newClientErr (GF := GF) cv xs e) := by
  unfold newClientErr; infer_instance

/-- The client's logger, owned, made the invariant `isClientLogger` (what `GetLogger` needs; the
same lemma as `InvCtxClient.lean`'s on `pr-verify/etcd-21809`). -/
theorem isClientLogger_alloc' (c lg : Loc) (Hnn : lg ≠ null) :
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
