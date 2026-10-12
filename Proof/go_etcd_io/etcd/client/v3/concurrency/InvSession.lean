/-
`client/v3/concurrency`'s `Session` (`session.go`): the vocabulary of
`Spec/go_etcd_io/etcd/client/v3/concurrency/`. Lean-first (no Rocq counterpart).

**Options.** A `SessionOption` is a closure on `(*sessionOptions, *zap.Logger)`;
`sessionOptSpec f g` says that `f` changes options modelled by `o` (`SessionOpts`: the TTL, the
lease ID, the context) into `g o`, given a non-nil logger; `sessOptsAt sl gs` that the
read-only slice `sl` holds closures with the transformers `gs`. `NewSession` starts from
`{ttl: 60, ctx: client.Ctx()}` (`SessionOpts.init`) and applies them in order
(`sessOptsFold`). `WithTTL(ttl)` keeps the TTL (and logs a warning) unless `ttl > 0`.

**The client** (`isEtcdSessionClient client cctx`): its `ctx` field holds `cctx` for good, its
`Lease` field a lease client (`isEtcdLeaseClient`, `InvEtcdTxn.lean`), its logger is non-nil
(`isClientLogger`, `InvClient.lean`).

**The session** (`isSession s γ client id`, persistent): its fields, read-only: the client, the
options (whose context is a context), the lease `id` (not `NoLease`), the session's context (a
child of the options' context, `WithCancel`), its cancel function (callable any number of
times), and its done channel `donec` (a broadcast channel, `Perennial`'s `Broadcast` idiom,
closed by the keep-alive goroutine once the keep-alive stream ends, which then cancels the
session's context). `sessionDone s γ` (persistent) says that `donec` is closed: what `Orphan`
and `Close` return. Nothing about the lease's liveness: the keep-alive stream is
`isChanAny` (any response or the close), so a session may end at any time.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.Base
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Proof.go_etcd_io.etcd.client.v3.InvClient
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency

/-! ## Options -/

section model
variable [ext : FfiSyntax]

/-- `sessionOptions`: the lease's TTL (seconds), an existing lease (`0`: none), the context. -/
structure SessionOpts where
  ttl : w64
  leaseID : w64
  ctx : GoInterface

/-- What `NewSession` starts from: `&sessionOptions{ttl: defaultSessionTTL, ctx: client.Ctx()}`. -/
def SessionOpts.init (cctx : GoInterface) : SessionOpts :=
  { ttl := W64 60, leaseID := W64 0, ctx := cctx }

/-- The options' transformers applied in order (`NewSession`'s loop). -/
def sessOptsFold (gs : List (SessionOpts → SessionOpts)) (o : SessionOpts) : SessionOpts :=
  gs.foldl (fun o g => g o) o

/-- `WithTTL(ttl)`: the TTL, if positive (otherwise it is kept, and a warning logged). -/
def withTTLM (ttl : w64) (o : SessionOpts) : SessionOpts :=
  if 0 < sint.Z ttl then { o with ttl := ttl } else o

/-- `WithLease(id)` -/
def withLeaseSM (id : w64) (o : SessionOpts) : SessionOpts := { o with leaseID := id }

/-- `WithContext(ctx)` -/
def withContextM (c : GoInterface) (o : SessionOpts) : SessionOpts := { o with ctx := c }

/-- The `sessionOptions` value modelled by `o`. -/
def SessionOpts.val (o : SessionOpts) : sessionOptions :=
  { ttl' := o.ttl, leaseID' := o.leaseID, ctx' := o.ctx }

/-- The session's lease `id`, for the options `o`: not `NoLease`, and the options' lease if they
name one (otherwise a granted one). -/
def sessionLeaseOk (o : SessionOpts) (id : w64) : Prop :=
  id ≠ W64 0 ∧ (o.leaseID ≠ W64 0 → id = o.leaseID)

theorem sessOptsFold_take_succ (gs : List (SessionOpts → SessionOpts)) (o : SessionOpts)
    (n : Nat) (g : SessionOpts → SessionOpts) (h : gs[n]? = some g) :
    sessOptsFold (gs.take (n + 1)) o = g (sessOptsFold (gs.take n) o) := by
  unfold sessOptsFold
  rw [List.take_add_one, h]
  simp

end model

/-- The ghost names of a session: its done channel's. -/
structure SessionNames where
  done : ChanNames

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `TypeRepr` of `clientv3.Client` and `zap.Logger` (named and underlying types), straight from
their `TypeAssumptions`, as `InvNew.lean` does for `Client`: without these, a load of a client's
field or of a `*zap.Logger` finds `TypeRepr` through the struct's `IntoValTyped` instance, built
from the `sorry` instances ("axiomatized type") of names-only field types (`Client.cfg`, zap's
`zapcore.Clock`, ...), putting them in the trust base for nothing. -/
instance (priority := high) session_client_typeRepr :
    TypeRepr go_etcd_io.etcd.client.v3.Client.ty go_etcd_io.etcd.client.v3.Client :=
  go.type_repr_underlying (u := go_etcd_io.etcd.client.v3.Client.underlying)

instance (priority := high) session_client_typeRepr_u :
    TypeRepr go_etcd_io.etcd.client.v3.Client.underlying go_etcd_io.etcd.client.v3.Client :=
  go.type_repr_underlying (u := go_etcd_io.etcd.client.v3.Client.underlying)

instance (priority := high) session_zapLogger_typeRepr :
    TypeRepr go_uber_org.zap.Logger.ty go_uber_org.zap.Logger :=
  go.type_repr_underlying (u := go_uber_org.zap.Logger.underlying)

instance (priority := high) session_zapLogger_typeRepr_u :
    TypeRepr go_uber_org.zap.Logger.underlying go_uber_org.zap.Logger :=
  go.type_repr_underlying (u := go_uber_org.zap.Logger.underlying)

/-- The `SessionOption` closure `f` changes options modelled by `o` into `g o` (given a non-nil
logger, which `WithTTL` may warn on). -/
def sessionOptSpec (f : GoFunc) (g : SessionOpts → SessionOpts) : IProp GF :=
  iprop(□ ∀ (p : Loc) (o : SessionOpts) (lg : Loc),
    {{ p ↦ o.val ∗ ⌜lg ≠ null⌝ }} (App (App (Val #f) (Val #p)) (Val #lg))
    {{ RET #(); p ↦ (g o).val }})

instance sessionOptSpec_persistent (f : GoFunc) (g : SessionOpts → SessionOpts) :
    Persistent (sessionOptSpec (GF := GF) f g) := by
  unfold sessionOptSpec; infer_instance

/-- The `[]SessionOption` slice `sl` (read-only) holds closures with the transformers `gs`. -/
def sessOptsAt (sl : GoSlice) (gs : List (SessionOpts → SessionOpts)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ ⌜fs.length = gs.length⌝ ∗
    □ ∀ (i : Nat) (f : GoFunc) (g : SessionOpts → SessionOpts), ⌜fs[i]? = some f⌝ -∗
      ⌜gs[i]? = some g⌝ -∗ sessionOptSpec f g)

instance sessOptsAt_persistent (sl : GoSlice) (gs : List (SessionOpts → SessionOpts)) :
    Persistent (sessOptsAt (GF := GF) sl gs) := by
  unfold sessOptsAt; infer_instance

/-! ## The client and the session -/

/-- **The client, as a session uses it** (persistent): its `ctx` field holds `cctx` for good,
its `Lease` a lease client, its logger is non-nil. -/
def isEtcdSessionClient (client : Loc) (cctx : GoInterface) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" client ↦□ cctx ∗
    isEtcdLeaseClient client ∗ isClientLogger client)

instance isEtcdSessionClient_persistent (client : Loc) (cctx : GoInterface) :
    Persistent (isEtcdSessionClient (GF := GF) client cctx) := by
  unfold isEtcdSessionClient; infer_instance

/-- A cancel function that may be called any number of times (and returns). -/
def cancelSpec (cancel : GoFunc) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, □ (True : IProp GF) -∗ ▷ (True -∗ Φ #()) -∗
    WP (App (Val #cancel) (Val #())) {{ Φ }})

instance cancelSpec_persistent (cancel : GoFunc) : Persistent (cancelSpec (GF := GF) cancel) := by
  unfold cancelSpec; infer_instance

/-- **Receiving** from a channel with no promise (`isChanAny`, the client's keep-alive stream):
some value, or the close. -/
theorem chanAny_recv_au (γ : ChanNames) (ch : Loc) (Φ : Loc → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isChanAny γ ch -∗ (▷ ∀ v ok, Φ v ok) -∗ recvAu γ Loc Φ := by
  unfold isChanAny recvAu
  iintro ⟨Hlc1, Hlc2⟩ ⟨#Hch, #Hinv⟩ HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑(nroot .@ "etcd_anychan")) $$ Hlc1 Hi with Hi
  icases Hi with ⟨%s, Hoc0⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hoc0
  rcases s with (_ | ⟨v0, buff'⟩) | _ | v | _ | v | _ | (_ | ⟨v1, rest⟩)
  all_goals dsimp only
  case Idle =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .RcvPending; iexact Hoc
    imodintro
    unfold recvNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑(nroot .@ "etcd_anychan")) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%s, Hoc1⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hoc1
    rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | v | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    all_goals first
      | itrivial
      | (iintro Hoc
         imod Hmask with -
         imod Hclose $$ [Hoc] with -
         · inext; iexists _; iexact Hoc
         imodintro
         iapply HΦ)
  all_goals first
    | itrivial
    | (iintro Hoc
       imod Hmask with -
       imod Hclose $$ [Hoc] with -
       · inext; iexists _; iexact Hoc
       imodintro
       iapply HΦ)

/-- The session's done channel `donec`: a broadcast channel (nothing is sent; its close is
`Session.Done`'s signal). -/
def sessionDoneChan (donec : GoChan) (γ : SessionNames) : IProp GF :=
  ownBroadcastChan donec γ.done iprop(True) .Unknown

instance sessionDoneChan_persistent (donec : GoChan) (γ : SessionNames) :
    Persistent (sessionDoneChan (GF := GF) donec γ) := by
  unfold sessionDoneChan; infer_instance

/-- **The session** `s` of the client `client` with the lease `id` (persistent; see the module
docstring). -/
def isSession (s : Loc) (γ : SessionNames) (client : Loc) (id : w64) : IProp GF :=
  iprop(∃ (ops : Loc) (o : SessionOpts) (octx : GoInterfaceOk)
      (ocs : context.ContextDesc (IProp GF)) (ctx : GoInterfaceOk)
      (cs : context.ContextDesc (IProp GF)) (cancel : GoFunc) (donec : GoChan),
    structFieldRef Session go!"client" s ↦□ client ∗
    structFieldRef Session go!"opts" s ↦□ ops ∗
    structFieldRef Session go!"id" s ↦□ id ∗
    structFieldRef Session go!"ctx" s ↦□ GoInterface.ok ctx ∗
    structFieldRef Session go!"cancel" s ↦□ cancel ∗
    structFieldRef Session go!"donec" s ↦□ donec ∗
    ops ↦□ o.val ∗ ⌜o.ctx = GoInterface.ok octx ∧ id ≠ W64 0⌝ ∗ context.isContext octx ocs ∗
    context.isContext ctx cs ∗ cancelSpec cancel ∗ sessionDoneChan donec γ ∗
    isEtcdLeaseClient client)

set_option synthInstance.maxSize 512 in
set_option synthInstance.maxHeartbeats 200000 in
instance isSession_persistent (s : Loc) (γ : SessionNames) (client : Loc) (id : w64) :
    Persistent (isSession (GF := GF) s γ client id) := by
  unfold isSession; infer_instance

/-- **The session has ended** (persistent): its done channel is closed (the keep-alive stream
ended, or the session was orphaned; its context is then canceled). -/
def sessionDone (s : Loc) (γ : SessionNames) : IProp GF :=
  iprop(∃ donec : GoChan, structFieldRef Session go!"donec" s ↦□ donec ∗
    ownBroadcastChan donec γ.done iprop(True) .Done)

instance sessionDone_persistent (s : Loc) (γ : SessionNames) :
    Persistent (sessionDone (GF := GF) s γ) := by
  unfold sessionDone; infer_instance

end defs

end concurrency
end EtcdGrove
end Perennial
