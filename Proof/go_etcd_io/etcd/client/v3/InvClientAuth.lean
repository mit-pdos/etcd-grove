/-
**A client's authentication** (the auth plan's C1, 2026-10-28; `notes/c1-plan.md`): what
`getToken` needs to fetch and store a token, and the readiness gate on the retry interceptor's
contract. Lean-first (no Rocq counterpart).

**`Authenticate`'s messages**: the request's model is the user name and the password, the
response's the token (`AuthenticateResponse.Token`, which `getToken` stores in the bundle).

**What the token fetch needs** (`clientAuthAt c eps P`, persistent; set before the dial): the
client's token bundle, if any, holding `""` or tokens meeting `P` (`tokenBundleInv`, the
credentials' invariant); its `Token`, `""` or meeting `P`; and, for a client with a user name and
a password (then with a bundle), `Authenticate` registered at its endpoints with a spec whose reply
to that user and password is a token meeting `P` (`authTokReg`). `newClient` chooses `P`; `C1`'s
is `auth.tokIssued γa · u`.

**The readiness gate** (`notes/c1-plan.md`, finding 1, decision (A)): the retry interceptor's
refresh path calls `getToken`, which calls `c.Auth.Authenticate`; `c.Auth` is set only after the
dial. The interceptor's contract is given under `clientReady c conn eps` (`c.Auth` set, over the
connection `conn`, with `clientAuthAt c eps P`), which `newClient` mints after `NewAuth`:
`etcdInterceptorOkG c ic` (the interceptor's, from the dial's setup) and `isEtcdConnG c conn eps`
(the dial's connection), `isEtcdConnG_ready` the ungated `isEtcdConn`. The objects `newClient`
builds before `NewAuth` (its `KV`, `Lease`, `Auth`) are given by their constructors without the
connection's fact (`clientKVAtS`, `kvObjS`, `lessorAtS`, `authObjS`: what `clientKVAt`, `kvObjAt`,
`lessorAt`, `authObjAt` hold but `isEtcdConn`), which `newClient` attaches once the client is ready
(`clientKVAt_of`, `kvObjAt_of`, `lessorAt_of`, `authObjAt_of`): a persistent `kvObjAt` from
`NewKV` would claim the interceptor's contract while a refresh would still find `c.Auth` nil.

**The connection's tokens** (`connTokOk conn P`): what the per-RPC credentials returned to the
connection's attempts is none, or the one key `token` with a token meeting `P` (from
`grpc.NewClient`'s `connCredsOk`, `connTokOk_none`, `connTokOk_one`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn
public import Proof.go_etcd_io.etcd.client.v3.credentials.Defs
public import Proof.go_etcd_io.etcd.client.v3.InvLessor
public import Perennial.Ghost.DGhostVar

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk errCellOk)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-! ## `Authenticate`'s messages -/

/-- **A `*pb.AuthenticateRequest`** on the wire: the user's name and password; a decoded copy's
`Password` the handler's own (`EtcdServer.Authenticate` clears it when it returns, the fix of
CVE-2021-28235; C1's review, F1). -/
def pbAuthenticateRequest : ProtoMsg GF where
  ty := etcdserverpb.AuthenticateRequest.ty
  M := GoString × GoString
  send inp m := iprop(∃ req : etcdserverpb.AuthenticateRequest, inp ↦ req ∗
    ⌜req.Name' = m.1 ∧ req.Password' = m.2⌝)
  recv r m := iprop(⌜r ≠ null⌝ ∗
    structFieldRef etcdserverpb.AuthenticateRequest go!"Name" r ↦□ m.1)
  recv_persistent _ _ := inferInstance
  recvOwn r m := iprop(structFieldRef etcdserverpb.AuthenticateRequest go!"Password" r ↦ m.2)
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthenticateRequest))
  own l := iprop(∃ v : etcdserverpb.AuthenticateRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.AuthenticateResponse`** on the wire: its token. -/
def pbAuthenticateResponse : ProtoMsg GF where
  ty := etcdserverpb.AuthenticateResponse.ty
  M := GoString
  send r t := iprop(∃ v : etcdserverpb.AuthenticateResponse, r ↦ v ∗ ⌜v.Token' = t⌝)
  recv r t := iprop(⌜r ≠ null⌝ ∗
    structFieldRef etcdserverpb.AuthenticateResponse go!"Token" r ↦□ t)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.AuthenticateResponse))
  own l := iprop(∃ v : etcdserverpb.AuthenticateResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- `Authenticate`'s method name. -/
def authnMethod : GoString := go!"/etcdserverpb.Auth/Authenticate"

/-- **The outcome of an `Authenticate` call** (the retry client's, the `*authClient`'s): `nil`
and a response whose token `t` meets `Q t`; or a client error that grpc's `status` accepts and no
response (as `authCallOut`). -/
def authnCallOut (Q : GoString → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ t, pbAuthenticateResponse.recv resp t ∗ Q t) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err ∗ errCellOk err))

/-- **`Authenticate` gives `u`'s tokens meeting `P`** at the endpoints `eps` (persistent): the
method is registered there with a spec whose reply to `(u, pw)`, at any attempt, is a token
meeting `P`. -/
def authTokReg (eps : List GoString) (u pw : GoString) (P : GoString → IProp GF) : IProp GF :=
  iprop(∃ Spec : GrpcSpec (GF := GF) pbAuthenticateRequest pbAuthenticateResponse,
    isGrpcRpcs eps authnMethod Spec ∗ □ ▷ Spec (u, pw) (fun t => iprop(□ P t)))

instance authTokReg_persistent (eps : List GoString) (u pw : GoString) (P : GoString → IProp GF) :
    Persistent (authTokReg eps u pw P) := by
  unfold authTokReg; infer_instance

/-! ## What the token fetch needs -/

/-- **What `getToken` reads of the `*Client` `c` and relies on** (persistent; see the file
header). -/
def clientAuthAt (c : Loc) (eps : List GoString) (P : GoString → IProp GF) : IProp GF :=
  iprop(∃ (u pw tok : GoString) (atb : GoInterface),
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Username" c ↦□ u ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Password" c ↦□ pw ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Token" c ↦□ tok ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"authTokenBundle" c ↦□ atb ∗
    (⌜atb = GoInterface.nil⌝ ∨ tokenBundleInv atb P) ∗ (⌜tok = go!""⌝ ∨ □ P tok) ∗
    (⌜u = go!"" ∨ pw = go!""⌝ ∨
      ⌜atb ≠ GoInterface.nil⌝ ∗ client.ctxErrClientAll ∗ authTokReg eps u pw P))

instance clientAuthAt_persistent (c : Loc) (eps : List GoString) (P : GoString → IProp GF) :
    Persistent (clientAuthAt c eps P) := by
  unfold clientAuthAt; infer_instance

theorem tokenBundleInv_nn (atb : GoInterface) (P : GoString → IProp GF) :
    tokenBundleInv (GF := GF) atb P ⊢ ⌜atb ≠ GoInterface.nil⌝ := by
  unfold tokenBundleInv
  iintro ⟨%b, %rc, %h, -⟩
  ipureintro
  subst h
  simp [interface.mkOk]

/-- **The `*authClient` `api`'s structure** over the connection `conn` (`authObjAt` without the
connection's fact). -/
def authObjS (api conn : Loc) : IProp GF :=
  iprop(∃ (rac : Loc) (sl : GoSlice),
    structFieldRef go_etcd_io.etcd.client.v3.authClient go!"remote" api ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryAuthClient.ty) #rac :
        GoInterface) ∗
    retryAuthAt rac conn ∗
    structFieldRef go_etcd_io.etcd.client.v3.authClient go!"callOpts" api ↦□ sl ∗ callOptsAt sl)

instance authObjS_persistent (api conn : Loc) : Persistent (authObjS (GF := GF) api conn) := by
  unfold authObjS; infer_instance

theorem authObjAt_split (api : Loc) (addr : List GoString) :
    authObjAt (GF := GF) api addr ⊣⊢ ∃ conn, authObjS api conn ∗ isEtcdConn conn addr := by
  unfold authObjAt authObjS
  constructor
  · iintro ⟨%rac, %conn, %sl, #Hr, #Hra, #Hc, #Hco, #Hok⟩
    iexists conn
    iframe Hc
    iexists rac, sl
    iframe #
  · iintro ⟨%conn, ⟨%rac, %sl, #Hr, #Hra, #Hco, #Hok⟩, #Hc⟩
    iexists rac, conn, sl
    iframe #

theorem authObjAtC_of (api conn : Loc) (addr : List GoString) :
    authObjS (GF := GF) api conn ∗ isEtcdConn conn addr ⊢ authObjAtC api conn addr := by
  unfold authObjS authObjAtC
  iintro ⟨⟨%rac, %sl, #Hr, #Hra, #Hco, #Hok⟩, #Hc⟩
  iexists rac, sl
  iframe #

theorem authObjAt_of (api conn : Loc) (addr : List GoString) :
    authObjS (GF := GF) api conn ∗ isEtcdConn conn addr ⊢ authObjAt api addr := by
  iintro ⟨#Ha, #Hc⟩
  iapply (authObjAt_split api addr).2
  iexists conn
  iframe #

/-- **The `*Client` `cl`'s connection and call options** (`clientKVAt` without the connection's
fact). -/
def clientKVAtS (cl conn : Loc) : IProp GF :=
  iprop(⌜cl ≠ null⌝ ∗ ∃ sl : GoSlice,
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" cl ↦□ conn ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"callOpts" cl ↦□ sl ∗ callOptsAt sl)

instance clientKVAtS_persistent (cl conn : Loc) : Persistent (clientKVAtS (GF := GF) cl conn) := by
  unfold clientKVAtS; infer_instance

theorem clientKVAt_of (cl conn : Loc) (addr : List GoString) :
    clientKVAtS (GF := GF) cl conn ∗ isEtcdConn conn addr ⊢ clientKVAt cl addr := by
  unfold clientKVAtS clientKVAt
  iintro ⟨⟨%Hne, %sl, #Hc, #Hco, #Hok⟩, #He⟩
  isplitr
  · ipureintro; exact Hne
  iexists conn, sl
  iframe #

/-- **The `*kv` `api`'s structure** over the connection `conn` (`kvObjAtC` without the connection's
fact). -/
def kvObjS (api conn : Loc) : IProp GF :=
  iprop(∃ (rkv : Loc) (sl : GoSlice),
    structFieldRef go_etcd_io.etcd.client.v3.kv go!"remote" api ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty) #rkv :
        GoInterface) ∗
    retryKVAt rkv conn ∗
    structFieldRef go_etcd_io.etcd.client.v3.kv go!"callOpts" api ↦□ sl ∗ callOptsAt sl)

instance kvObjS_persistent (api conn : Loc) : Persistent (kvObjS (GF := GF) api conn) := by
  unfold kvObjS; infer_instance

theorem kvObjAtC_of (api conn : Loc) (addr : List GoString) :
    kvObjS (GF := GF) api conn ∗ isEtcdConn conn addr ⊢ kvObjAtC api conn addr := by
  unfold kvObjS kvObjAtC
  iintro ⟨⟨%rkv, %sl, #Hr, #Hrkv, #Hco, #Hok⟩, #He⟩
  iexists rkv, sl
  iframe #

theorem kvObjAt_of (api conn : Loc) (addr : List GoString) :
    kvObjS (GF := GF) api conn ∗ isEtcdConn conn addr ⊢ kvObjAt api addr := by
  iintro H
  iapply (kvObjAt_conn api addr).2
  iexists conn
  iapply kvObjAtC_of
  iexact H

/-- **The `*lessor` `l`'s structure** over the connection `conn` (`lessorAt` without the
connection's fact). -/
def lessorAtS (l conn : Loc) : IProp GF :=
  iprop(∃ (dc : GoChan) (γd : ChanNames) (sc : GoInterfaceOk)
      (scd : context.ContextDesc (IProp GF)) (lg : Loc) (d : time.Duration) (γr : GName)
      (rlc : Loc) (sl : GoSlice),
    lsF go!"donec" l ↦□ dc ∗ ownBroadcastChan dc γd (iprop(True) : IProp GF) .Unknown ∗
    lsF go!"stopCtx" l ↦□ GoInterface.ok sc ∗ context.isContext sc scd ∗
    lsF go!"lg" l ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    lsF go!"firstKeepAliveTimeout" l ↦□ d ∗
    structFieldRef go_etcd_io.etcd.client.v3.lessor go!"remote" l ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty) #rlc :
        GoInterface) ∗
    retryLeaseAt rlc conn ∗
    structFieldRef go_etcd_io.etcd.client.v3.lessor go!"callOpts" l ↦□ sl ∗ callOptsAt sl ∗
    sync.isMutex (lsF go!"mu" l) (lessorInv l γr) ∗
    sync.isOnce (lsF go!"firstKeepAliveOnce" l) (ownBroadcastChan dc γd (iprop(True) : IProp GF) .Pending)
      iprop(True))

instance lessorAtS_persistent (l conn : Loc) : Persistent (lessorAtS (GF := GF) l conn) := by
  unfold lessorAtS; infer_instance

theorem lessorAt_of (l conn : Loc) (addr : List GoString) :
    lessorAtS (GF := GF) l conn ∗ isEtcdConn conn addr ⊢ lessorAt l addr := by
  unfold lessorAtS lessorAt lessorRemoteAt
  iintro ⟨⟨%dc, %γd, %sc, %scd, %lg, %d, %γr, %rlc, %sl, #H1, #H2, #H3, #H4, #H5, %H6, #H7, #H8,
    #H9, #H10, #H11, #H12, #H13⟩, #He⟩
  iexists dc, γd, sc, scd, lg, d, γr
  iframe H1 H2 H3 H4 H5 H7 H12 H13
  isplitr
  · ipureintro; exact H6
  iexists rlc, conn, sl
  iframe #

/-- **The client `c` is ready** (persistent; see the file header): its `Auth` a `*authClient` over
its connection `conn`, and what the token fetch needs, at some `P`. -/
def clientReady (c conn : Loc) (eps : List GoString) : IProp GF :=
  iprop(∃ (api : Loc) (P : GoString → IProp GF),
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Auth" c ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty) #api :
        GoInterface) ∗
    authObjS api conn ∗ clientAuthAt c eps P)

instance clientReady_persistent (c conn : Loc) (eps : List GoString) :
    Persistent (clientReady (GF := GF) c conn eps) := by
  unfold clientReady; infer_instance

/-! ## The gate -/

/-- **The retry interceptor `ic` of the client `c`, once `c` is ready** (persistent; see the file
header): on a connection `conn` to `eps` whose one interceptor `ic` is, with `clientReady c conn
eps`, the contract in both modes. -/
def etcdInterceptorOkG (c : Loc) (ic : GoFunc) : IProp GF :=
  iprop(□ ∀ (conn : Loc) (eps : List GoString),
    clientReady c conn eps -∗ grpcConn conn eps [ic] [] -∗
      etcdInterceptorOk ic ∗ etcdInterceptorOkW ic)

instance etcdInterceptorOkG_persistent (c : Loc) (ic : GoFunc) :
    Persistent (etcdInterceptorOkG (GF := GF) c ic) := by
  unfold etcdInterceptorOkG; infer_instance

/-- **The dial's connection of the client `c`** (persistent; see the file header): `isEtcdConn`,
its interceptor's contract gated on `clientReady`. -/
def isEtcdConnG (c conn : Loc) (eps : List GoString) : IProp GF :=
  iprop(∃ ic : GoFunc, grpcConn conn eps [ic] [] ∗ etcdInterceptorOkG c ic)

instance isEtcdConnG_persistent (c conn : Loc) (eps : List GoString) :
    Persistent (isEtcdConnG (GF := GF) c conn eps) := by
  unfold isEtcdConnG; infer_instance

theorem isEtcdConnG_ready (c conn : Loc) (eps : List GoString) :
    isEtcdConnG (GF := GF) c conn eps ∗ clientReady c conn eps ⊢ isEtcdConn conn eps := by
  unfold isEtcdConnG etcdInterceptorOkG
  iintro ⟨⟨%ic, #Hg, #Hok⟩, #Hr⟩
  ihave ⟨#H1, #H2⟩ := Hok $$ %conn %eps Hr Hg
  unfold isEtcdConn
  iexists ic
  iframe #

/-! ## The connection's tokens -/

/-- **What the per-RPC credentials of the connection `conn` returned to its attempts is none, or
the one key `token` with a token meeting `P`** (persistent; see the file header). -/
def connTokOk (conn : Loc) (P : GoString → IProp GF) : IProp GF :=
  iprop(□ ∀ cm, ⌜credsYield conn cm⌝ -∗ tokMdOk P cm)

instance connTokOk_persistent (conn : Loc) (P : GoString → IProp GF) :
    Persistent (connTokOk conn P) := by
  unfold connTokOk; infer_instance

theorem connTokOk_none (conn : Loc) (Q : GrpcMd → IProp GF) (P : GoString → IProp GF) :
    connCredsOk conn [] Q ⊢ connTokOk conn P := by
  unfold connCredsOk connTokOk tokMdOk
  iintro %h
  iintro !> %cm %hy
  have := h cm hy
  subst this
  isplitl []
  · ipureintro; intro k _; rfl
  · ileft; ipureintro; rfl

theorem connTokOk_one (conn : Loc) (pc : GoInterface) (P : GoString → IProp GF) :
    connCredsOk conn [pc] (tokMdOk P) ⊢ connTokOk conn P := by
  unfold connCredsOk connTokOk
  iintro #H
  iintro !> %cm %hy
  ihave #Hq := H $$ %cm %hy
  iexact Hq

/-! ## The token of an attempt -/

/-- `auth.mdTokenOf` reads the keys `token` and `authorization` only. -/
theorem auth.mdTokenOf_eq (md : GrpcMd) :
    auth.mdTokenOf md =
      match mdGet md go!"token" with
      | some (v :: _) => some (strings.trimPrefix v go!"Bearer ")
      | some [] => none
      | none =>
        match mdGet md go!"authorization" with
        | some (v :: _) => some (strings.trimPrefix v go!"Bearer ")
        | _ => none := by
  cases md <;> rfl

theorem grpcReservedKey_token : ¬ grpcReservedKey go!"token" := by
  unfold grpcReservedKey; decide

theorem grpcReservedKey_authorization : ¬ grpcReservedKey go!"authorization" := by
  unfold grpcReservedKey; decide

/-- Metadata's values at a key with no empty list, from the key's value list. -/
theorem mdGet_of_vals (md : GrpcMd) (k : GoString) (h : mdGet md k ≠ some []) :
    mdGet md k = if metadata.mdVals md k = [] then none else some (metadata.mdVals md k) := by
  unfold metadata.mdVals
  unfold mdGet at h ⊢
  cases hm : md.bind (fun m => m k) with
  | none => simp
  | some vs =>
    rw [hm] at h
    cases vs with
    | nil => exact absurd rfl h
    | cons a l => simp

theorem mdGet_mdNorm (md : GrpcMd) (k : GoString) :
    mdGet (metadata.mdNorm md) k =
      if metadata.mdVals md k = [] then none else some (metadata.mdVals md k) := by
  unfold metadata.mdNorm metadata.mdVals mdGet
  cases md with
  | none => simp
  | some m =>
    simp only [Option.map_some, Option.bind_some]
    cases hm : m k with
    | none => simp
    | some vs => cases vs <;> simp

/-- The token of metadata grpc delivered (no key with no values), from its two keys' values. -/
theorem mdTokenOf_norm (md md' : GrpcMd) (hne : ∀ k, mdGet md k ≠ some [])
    (ht : metadata.mdVals md go!"token" = metadata.mdVals md' go!"token")
    (ha : metadata.mdVals md go!"authorization" = metadata.mdVals md' go!"authorization") :
    auth.mdTokenOf md = auth.mdTokenOf (metadata.mdNorm md') := by
  rw [auth.mdTokenOf_eq md, auth.mdTokenOf_eq (metadata.mdNorm md'),
    mdGet_of_vals md _ (hne _), mdGet_of_vals md _ (hne _), mdGet_mdNorm, mdGet_mdNorm, ht, ha]

/-- **Every attempt on the connection `conn` carries a token meeting `P`, or the context's own**
(persistent; the auth plan's C1, 2026-10-28; C1's review, Q1): the handler of an attempt of a call
with the context `ctx` sees a token meeting `P` (trimmed of `"Bearer "`, as the server reads it,
`auth.mdTokenOf`), or the token of the context's outgoing metadata as grpc delivers it
(`metadata.mdNorm`). -/
def attemptTokOk (conn : Loc) (P : GoString → IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterface) (md : GrpcMd), ⌜clientAttemptMd conn ctx md⌝ -∗
    (∃ t, ⌜auth.mdTokenOf md = some (strings.trimPrefix t go!"Bearer ")⌝ ∗ □ P t) ∨
    ⌜auth.mdTokenOf md = auth.mdTokenOf (metadata.mdNorm (metadata.outgoingOf ctx))⌝)

instance attemptTokOk_persistent (conn : Loc) (P : GoString → IProp GF) :
    Persistent (attemptTokOk conn P) := by
  unfold attemptTokOk; infer_instance

/-- **The attempts' tokens from the credentials'**: grpc sends the credentials' values first. -/
theorem attemptTokOk_of (conn : Loc) (P : GoString → IProp GF) :
    connTokOk conn P ⊢ attemptTokOk conn P := by
  unfold connTokOk attemptTokOk
  iintro #H
  iintro !> %ctx %md %h
  obtain ⟨c, v, hc, cm, hy, hvals, hne⟩ := h
  have hot : ∀ k, k ≠ go!"client-api-version" →
      metadata.mdVals (metadata.outgoingOf c) k = metadata.mdVals (metadata.outgoingOf ctx) k := by
    intro k hk
    unfold metadata.mdVals
    rw [hc, metadata.mdVals_mdSet_ne _ _ _ _ hk]
  have htok := hvals _ grpcReservedKey_token
  have hauth := hvals _ grpcReservedKey_authorization
  rw [hot _ (by decide)] at htok
  rw [hot _ (by decide)] at hauth
  ihave #Hq := H $$ %cm %hy
  unfold tokMdOk
  icases Hq with ⟨%hoth, (%hnone | ⟨%t, %ht, #Hp⟩)⟩
  · iright
    ipureintro
    have hc0 : metadata.mdVals cm go!"token" = [] := by
      unfold metadata.mdVals; unfold mdGet at hnone; rw [hnone]; rfl
    have ha0 : metadata.mdVals cm go!"authorization" = [] := by
      have := hoth go!"authorization" (by decide)
      unfold metadata.mdVals; unfold mdGet at this; rw [this]; rfl
    apply mdTokenOf_norm md _ hne
    · rw [htok, hc0, List.nil_append]
    · rw [hauth, ha0, List.nil_append]
  · ileft
    iexists t
    iframe Hp
    ipureintro
    have hc1 : metadata.mdVals cm go!"token" = [t] := by
      unfold metadata.mdVals; unfold mdGet at ht; rw [ht]; rfl
    rw [hc1] at htok
    rw [auth.mdTokenOf_eq md, mdGet_of_vals md _ (hne _), htok]
    simp

/-! ## A quiet context's errors -/

/-- A descriptor of a quiet context (never done): any names whose closed flag is `false` for
good (as `InvServerKV`'s `todoCd`). -/
abbrev quietCd (γ : context.ContextNames) : context.ContextDesc (IProp GF) :=
  ⟨∅, none, γ, iprop(True)⟩

/-- **A quiet context's `Err()` returns client errors** (`nil`, always), at a descriptor whose
closed flag is `false` for good (as `ctxErrClient_todo`; the auth plan's C1). -/
theorem ctxErrClient_quiet (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (ci : GoInterfaceOk) (γ : context.ContextNames) :
    ctxQuiet (GF := GF) ci ∗ dghostVar γ.closedGn DFrac.discard false ⊢
      ctxErrClient ci (quietCd γ) := by
  iintro ⟨#Hq, #Hf⟩
  unfold ctxErrClient
  imodintro
  iintro %cl %Φ Hcl HΦ
  cases cl with
  | Done =>
    iunfold context.ContextClosed at Hcl
    ihave %Hag := dghostVar_agree _ _ _ _ _ $$ Hf Hcl
    simp at Hag
  | _ =>
    iunfold ctxQuiet at Hq
    iapply Hq
    inext
    iapply HΦ
    · simp only [↓reduceIte]; itrivial
    · ipureintro
      exact ⟨hAs, fun ii h => by cases h⟩
    · iapply go_etcd_io.etcd.cache.v3.statusErrOk_nil
    · iapply go_etcd_io.etcd.cache.v3.errCellOk_nil

/-- **A descriptor for a quiet context**, with `ctxErrClient` (the auth plan's C1: the client's
token fetch calls `Authenticate` with a quiet caller's context at it). -/
theorem quiet_ctx (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (ci : GoInterfaceOk) :
    ctxQuiet (GF := GF) ci ⊢ |==> ∃ cd : context.ContextDesc (IProp GF),
      ctxOk ci cd ∗ ctxErrClient ci cd := by
  iintro #Hq
  imod dghostVar_alloc (GF := GF) false with ⟨%γc, Hc⟩
  imod dghostVar_persist γc 1 false $$ Hc with #Hc
  imodintro
  iexists (quietCd ⟨γc, γc⟩)
  isplitl []
  · unfold ctxOk
    iright
    iexact Hq
  iapply ctxErrClient_quiet hAs ci ⟨γc, γc⟩
  iframe #

/-! ## What `New` takes and gives -/

/-- **What `New` needs of a configuration's credentials** at the token predicate `P` (persistent;
`cfg.Token` is `""`, `clientCfgOk`): no user name or no password (no bundle, no call), or
`Authenticate` registered at the endpoints with the reply to them a token meeting `P`, the bound
on the credentials' readers (`authTokReg`, `credTokInv`), and every context's `Err()` returning
client errors (`client.ctxErrClientAll`: `Authenticate`'s `ContextError`; a top-level result
discharges it by `ctxErrClientAllW_of`; C1's review, F5). -/
def clientAuthPre (cfg : go_etcd_io.etcd.client.v3.Config) (eps : List GoString)
    (P : GoString → IProp GF) : IProp GF :=
  iprop(⌜cfg.Username' = go!"" ∨ cfg.Password' = go!""⌝ ∨
    ⌜threadBound GF ≤ 2 ^ 30⌝ ∗ client.ctxErrClientAll ∗
      authTokReg eps cfg.Username' cfg.Password' P)

instance clientAuthPre_persistent (cfg : go_etcd_io.etcd.client.v3.Config) (eps : List GoString)
    (P : GoString → IProp GF) : Persistent (clientAuthPre cfg eps P) := by
  unfold clientAuthPre; infer_instance

/-- An anonymous client (no user name) needs no registration. -/
theorem clientAuthPre_anon (cfg : go_etcd_io.etcd.client.v3.Config) (eps : List GoString)
    (P : GoString → IProp GF) (h : cfg.Username' = go!"") :
    ⊢ clientAuthPre cfg eps P := by
  unfold clientAuthPre
  ileft; ipureintro; exact Or.inl h

/-- **The client `cl`'s KV calls carry its credentials' tokens meeting `P`** (persistent; what
`New` gives at `clientAuthPre`'s `P`): its `KV` a `*kv` over a connection (`kvObjAtC`, the one
`isNewClient`'s `kvObjAt` names) whose attempts carry a token meeting `P` or the context's own
(`attemptTokOk`), and (5b) its `Auth` an `*authClient` over the same connection (`authObjAtC`), so
that an admin call's attempts are the connection's too. -/
def clientTokAt (cl : Loc) (eps : List GoString) (P : GoString → IProp GF) : IProp GF :=
  iprop(∃ api conn : Loc,
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api : GoInterface) ∗
    kvObjAtC api conn eps ∗ attemptTokOk conn P ∗
    -- (5b) its `Auth`, an `*authClient` over the same connection
    ∃ ap : Loc, structFieldRef go_etcd_io.etcd.client.v3.Client go!"Auth" cl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty) #ap :
          GoInterface) ∗
      authObjAtC ap conn eps)

instance clientTokAt_persistent (cl : Loc) (eps : List GoString) (P : GoString → IProp GF) :
    Persistent (clientTokAt cl eps P) := by
  unfold clientTokAt; infer_instance

end defs

end EtcdGrove
end Perennial
