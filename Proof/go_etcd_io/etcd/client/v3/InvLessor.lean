/-
**The client's lessor: its keep-alives** (item 1, branch `lease-client`, 2026-10-18): the
vocabulary of the proofs of `client/v3/lease.go`'s `KeepAlive` and of the goroutines it starts
(`keepAliveCtxCloser`, `recvKeepAliveLoop` with `resetRecv`, `recvKeepAlive` and
`sendKeepAliveLoop`, `deadlineLoop`), all to safety (no panic; the goroutines' postconditions
`True`). Lean-first (no Rocq counterpart).

**A keep-alive channel** (`KeepAlive`'s `ch`, a buffered channel of `*LeaseKeepAliveResponse`):
the caller gets `isChanAny γ ch` (`cache/v3/InvEtcdTxn.lean`: an invariant holding the channel's
state, and the close token `γc` once it is closed), the lessor the token (`chanTok ch`, exclusive:
`ghostVar γc 1 ()`). Holding the token, the lessor rules out the closed state, which its sends
(`recvKeepAlive`'s non-blocking `ch <- karesp`) and its close (`keepAlive.close`,
`keepAliveCtxCloser`, `closeRequireLeader`) need; closing puts the token in the
invariant. A channel is closed once: its token is in the lock invariant while the channel is in
some `ka.chs`, and every close removes the channel from it (`keepAlive.close` is called on a
keep-alive just removed from the map, or on all of them before the map is replaced).

**A keep-alive** (`kaOwn γr ka`, `*keepAlive`): its `chs` and `ctxs` slices, equally long and
**aligned** (`kaPaired`: for every `i`, `chs[i]` and `ctxs[i]` are a pair `KeepAlive` registered,
`kaReg`; `keepAliveCtxCloser` finds a context's index in `ctxs` and closes the channel at that
index in `chs`), each channel's token, each context a context (`kaCtxOk`: `ctxs` holds what
`KeepAlive` was given, wrapped by `context.WithValue`), its `deadline` and `nextKeepAlive`, and
its `donec` (read-only, a broadcast channel: nothing is sent; the right to close it, `.Pending`,
is the keep-alive's, used once by `keepAlive.close`; `kaDone`, persistent, for `KeepAlive` and
`keepAliveCtxCloser`, which read it outside the lock).

**The registry of keep-alive pairs** (`lessorReg γr`, in the lock invariant; added 2026-10-18 so
that the invariant checks `closeRequireLeader`'s fix, a7bd9a16e,
`issues/etcd-lease-close-require-leader-ctx-misaligned.md`): a ghost map from `KeepAlive`'s `&ctx`
(the variable its wrapped context is stored in, and the value the context holds at
`keepAliveCtxKey{}`) to the channel `KeepAlive` made in that call. `kaReg γr ch c` (persistent):
some `p ↦□ c` (`KeepAlive`'s variable holds `c`, for good: the context is anchored to `p` by the
heap) with `p ↦ ch` in the registry (the channel anchored to `p` by the ghost map, whose
persistent entries no one changes). A key is added only with the full points-to of a variable not
yet a key (the registry holds a persistent points-to of every key, `lessorReg_register`), so the
registered pairs are exactly `KeepAlive`'s `(ch, ctx)`: a pair of one call's channel and another
call's context is not one (`closeRequireLeader` at upstream's code, `ka.ctxs[newIdx]`, would need
`kaReg ka.chs[i] ka.ctxs[newIdx]`, which no proof can give).

**The lessor's lock invariant** (`lessorInv l γr`): the map of keep-alives with each one's `kaOwn`,
the registry, `stream`, `streamCancel` (`nil` or a cancel function) and `loopErr`. **The lessor** (`lessorAt l
addr`, persistent): what `NewLeaseFromLeaseClient` set and nobody writes again: `donec` (a
broadcast channel whose close is the receive loop's: the right is `firstKeepAliveOnce`'s resource,
handed to the loop the `Once` starts), `stopCtx` (a context), `lg` (non-nil),
`firstKeepAliveTimeout`, the unary calls' `remote` and `callOpts` (`lessorRemoteAt`), `mu` (with
`lessorInv`, at some registry `γr`) and `firstKeepAliveOnce`.

**The keep-alive stream** (`/etcdserverpb.Lease/LeaseKeepAlive`, `isGrpcStream`): requests carry
their `ID` (`pbLeaseKeepAliveRequest`), responses their `ID` and `TTL` and a header
(`pbLeaseKeepAliveResponse`); the lessor asks nothing of the server's stream specification and
promises nothing with its requests (`Up` is `True`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease
public import Proof.go_etcd_io.etcd.client.v3.InvRetry
public import Proof.google_golang_org.grpc.InvGrpcStream
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Proof.Lib.List

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- A field of the `*lessor` `l`. -/
abbrev lsF (f : GoString) (l : Loc) : Loc := structFieldRef go_etcd_io.etcd.client.v3.lessor f l

/-- A field of the `*keepAlive` `ka`. -/
abbrev kaF (f : GoString) (ka : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.client.v3.keepAlive f ka

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-! ## Keep-alive channels -/

/-- The namespace of a keep-alive channel's invariant (`isChanAny`'s). -/
abbrev chanAnyN : Namespace := nroot .@ "etcd_anychan"

/-- **The lessor's right to send on and close the keep-alive channel `ch`** (exclusive; see the
file header). -/
def chanTok (ch : Loc) : IProp GF :=
  iprop(∃ (γ : ChanNames) (γc : GName), isChan ch γ Loc ∗ inv chanAnyN (chanAnyInv γ γc) ∗
    ghostVar γc 1 ())

/-! ## The keep-alive stream's messages -/

/-- **The `*pb.LeaseKeepAliveResponse` `l` holds `(ID, TTL)`** (read-only, with some header). -/
def keepAliveRespMsg (l : Loc) (m : w64 × w64) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ h : Loc,
    structFieldRef etcdserverpb.LeaseKeepAliveResponse go!"Header" l ↦□ h ∗
    structFieldRef etcdserverpb.LeaseKeepAliveResponse go!"ID" l ↦□ m.1 ∗
    structFieldRef etcdserverpb.LeaseKeepAliveResponse go!"TTL" l ↦□ m.2)

instance keepAliveRespMsg_persistent (l : Loc) (m : w64 × w64) :
    Persistent (keepAliveRespMsg (GF := GF) l m) := by
  unfold keepAliveRespMsg; infer_instance

/-- **The keep-alive requests on the wire** (a trusted wire model): a request's `ID`, the owned
struct on both ends. -/
abbrev pbLeaseKeepAliveRequest : StreamMsg GF where
  ty := etcdserverpb.LeaseKeepAliveRequest.ty
  M := w64
  cnt := inferInstance
  send l m := iprop(∃ v : etcdserverpb.LeaseKeepAliveRequest, l ↦ v ∗ ⌜m = v.ID'⌝)
  recv l m := iprop(∃ v : etcdserverpb.LeaseKeepAliveRequest, l ↦ v ∗ ⌜m = v.ID'⌝)
  own l := iprop(∃ v : etcdserverpb.LeaseKeepAliveRequest, l ↦ v)

/-- **The keep-alive responses on the wire** (a trusted wire model): a response's `(ID, TTL)`,
read-only on both ends (`keepAliveRespMsg`). -/
abbrev pbLeaseKeepAliveResponse : StreamMsg GF where
  ty := etcdserverpb.LeaseKeepAliveResponse.ty
  M := w64 × w64
  cnt := inferInstance
  send := keepAliveRespMsg
  recv := keepAliveRespMsg
  own l := iprop(∃ v : etcdserverpb.LeaseKeepAliveResponse, l ↦ v)

/-- **The keep-alive stream is served at `addr`** (persistent): some stream specification, no
promise with a request. -/
def leaseKAStreamOk (addr : GoString) : IProp GF :=
  iprop(∃ Spec : StreamSpec (GF := GF) pbLeaseKeepAliveResponse,
    isGrpcStream (Req := pbLeaseKeepAliveRequest) (Rep := pbLeaseKeepAliveResponse) addr
      go!"/etcdserverpb.Lease/LeaseKeepAlive" (fun _ _ => iprop(True)) Spec)

instance leaseKAStreamOk_persistent (addr : GoString) :
    Persistent (leaseKAStreamOk (GF := GF) addr) := by
  unfold leaseKAStreamOk; infer_instance

/-- **The Lease service's stream descriptor** (persistent; `etcdserverpb`'s fact,
`etcdserverpbDescs`): `Lease_ServiceDesc.Streams[0]` is a client stream. -/
def leaseDescOk : IProp GF :=
  iprop(∃ (sl : GoSlice) (sds : List google_golang_org.grpc.StreamDesc),
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Streams"
      (globalAddr etcdserverpb.Lease_ServiceDesc) ↦□ sl ∗ sl ↦*□ sds ∗
    ⌜sds.map (·.ClientStreams') = [true]⌝)

instance leaseDescOk_persistent : Persistent (leaseDescOk (GF := GF)) := by
  unfold leaseDescOk; infer_instance

/-- **`context.Canceled` and `context.DeadlineExceeded` are targets `errors.Is` takes** (persistent;
`canceledByCaller` compares a stream's error with them): a pointer error and a comparable one.
Go's (`context.go`: `errors.New(...)`, `deadlineExceededError{}`); from `context`'s facts as the
read package states them (`EtcdGrove.ContextReadErrs`), `ctxErrTargets_of`. -/
def ctxErrTargets : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr _root_.Perennial.context.Canceled ↦□ GoInterface.ok e ∗
      ⌜_root_.Perennial.errors.IsPointerError e⌝) ∗
    (∃ e : GoInterfaceOk, globalAddr _root_.Perennial.context.DeadlineExceeded ↦□ GoInterface.ok e ∗
      ⌜SafeMapKey (GF := GF) go.error (GoInterface.ok e)⌝))

instance ctxErrTargets_persistent : Persistent (ctxErrTargets (GF := GF)) := by
  unfold ctxErrTargets; infer_instance

/-! ## Keep-alives -/

/-- A keep-alive's context (`ka.ctxs`'s element): a context. -/
def kaCtxOk (c : GoInterface) : IProp GF :=
  iprop(∃ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)), ⌜c = GoInterface.ok ci⌝ ∗
    context.isContext ci cd)

instance kaCtxOk_persistent (c : GoInterface) : Persistent (kaCtxOk (GF := GF) c) := by
  unfold kaCtxOk; infer_instance

/-- **The keep-alive `ka`'s `donec`** (persistent; read outside the lock). -/
def kaDone (ka : Loc) (kd : GoChan) (γkd : ChanNames) : IProp GF :=
  iprop(kaF go!"donec" ka ↦□ kd ∗ ownBroadcastChan kd γkd (iprop(True) : IProp GF) .Unknown)

instance kaDone_persistent (ka : Loc) (kd : GoChan) (γkd : ChanNames) :
    Persistent (kaDone (GF := GF) ka kd γkd) := by
  unfold kaDone; infer_instance

/-! ## The registry of keep-alive pairs -/

/-- **`ch` and `c` are a pair `KeepAlive` registered** in the registry `γr` (persistent; see the
file header): `KeepAlive`'s variable `p` (`&ctx`) holds `c` for good, and the registry maps `p` to
`ch`. -/
def kaReg (γr : GName) (ch : Loc) (c : GoInterface) : IProp GF :=
  iprop(∃ p : Loc, p ↦□ c ∗ p ↪[γr]□ ch)

instance kaReg_persistent (γr : GName) (ch : Loc) (c : GoInterface) :
    Persistent (kaReg (GF := GF) γr ch c) := by
  unfold kaReg; infer_instance

/-- **The registry** (in the lock invariant; see the file header): the ghost map, with a
persistent points-to of every key (which keeps a key from being added twice). -/
def lessorReg (γr : GName) : IProp GF :=
  iprop(∃ reg : GMap Loc Loc, ghostMapAuth γr 1 reg ∗ [∗map] p ↦ _ch ∈ reg, ∃ v : GoInterface, p ↦□ v)

/-- **A keep-alive's `chs` and `ctxs` are aligned** (persistent): every index's channel and context
are a registered pair. -/
def kaPaired (γr : GName) (chs : List GoChan) (ctxs : List GoInterface) : IProp GF :=
  iprop(□ ∀ (i : Nat) (ch : Loc) (c : GoInterface), ⌜chs[i]? = some ch⌝ -∗ ⌜ctxs[i]? = some c⌝ -∗
    kaReg γr ch c)

instance kaPaired_persistent (γr : GName) (chs : List GoChan) (ctxs : List GoInterface) :
    Persistent (kaPaired (GF := GF) γr chs ctxs) := by
  unfold kaPaired; infer_instance

/-- **The keep-alive `ka`** (see the file header). -/
def kaOwn (γr : GName) (ka : Loc) : IProp GF :=
  iprop(∃ (chsS ctxsS : GoSlice) (chs : List GoChan) (ctxs : List GoInterface)
      (dl nk : time.Time) (kd : GoChan) (γkd : ChanNames),
    kaF go!"chs" ka ↦ chsS ∗ chsS ↦* chs ∗ ownSliceCap GoChan chsS (DFrac.own 1) ∗
    kaF go!"ctxs" ka ↦ ctxsS ∗ ctxsS ↦* ctxs ∗ ownSliceCap GoInterface ctxsS (DFrac.own 1) ∗
    ⌜chs.length = ctxs.length⌝ ∗
    kaF go!"deadline" ka ↦ dl ∗ kaF go!"nextKeepAlive" ka ↦ nk ∗
    kaDone ka kd γkd ∗ ownBroadcastChan kd γkd (iprop(True) : IProp GF) .Pending ∗
    ([∗list] ch ∈ chs, chanTok ch) ∗ ([∗list] c ∈ ctxs, kaCtxOk c) ∗ kaPaired γr chs ctxs)

/-- A cancel function that may be called any number of times (and returns). -/
def cancelAny (sc : GoFunc) : IProp GF :=
  iprop(∃ γ : context.ContextNames, context.cancelSpec sc γ iprop(True))

instance cancelAny_persistent (sc : GoFunc) : Persistent (cancelAny (GF := GF) sc) := by
  unfold cancelAny; infer_instance

/-- **The lessor's lock invariant** (see the file header). -/
def lessorInv (l : Loc) (γr : GName) : IProp GF :=
  iprop(∃ (mref : Loc) (m : GMap w64 Loc) (st : GoInterface) (sc : GoFunc) (e : GoInterface),
    lsF go!"keepAlives" l ↦ mref ∗ mref ↦$ m ∗ ([∗map] _id ↦ ka ∈ m, kaOwn (GF := GF) γr ka) ∗
    lsF go!"stream" l ↦ st ∗ lsF go!"streamCancel" l ↦ sc ∗
    (⌜sc = func.nil⌝ ∨ cancelAny (GF := GF) sc) ∗
    lsF go!"loopErr" l ↦ e ∗ lessorReg (GF := GF) γr)

/-- **The `*lessor` `l`** over a connection to `addr` (persistent; see the file header). -/
def lessorAt (l : Loc) (addr : GoString) : IProp GF :=
  iprop(∃ (dc : GoChan) (γd : ChanNames) (sc : GoInterfaceOk)
      (scd : context.ContextDesc (IProp GF)) (lg : Loc) (d : time.Duration) (γr : GName),
    lsF go!"donec" l ↦□ dc ∗ ownBroadcastChan dc γd (iprop(True) : IProp GF) .Unknown ∗
    lsF go!"stopCtx" l ↦□ GoInterface.ok sc ∗ context.isContext sc scd ∗
    lsF go!"lg" l ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    lsF go!"firstKeepAliveTimeout" l ↦□ d ∗
    lessorRemoteAt l addr ∗
    sync.isMutex (lsF go!"mu" l) (lessorInv l γr) ∗
    sync.isOnce (lsF go!"firstKeepAliveOnce" l) (ownBroadcastChan dc γd (iprop(True) : IProp GF) .Pending)
      iprop(True))

instance lessorAt_persistent (l : Loc) (addr : GoString) :
    Persistent (lessorAt (GF := GF) l addr) := by
  unfold lessorAt; infer_instance

end defs

/-! ## Lemmas -/

/-- An element of a big separating conjunction over a list, and the rest's over the list without
it. -/
theorem bigSepL_eraseIdx {PROP : Type _} [BI PROP] {A : Type _} (Φ : A → PROP) :
    ∀ (l : List A) (i : Nat) (h : i < l.length),
      ([∗list] x ∈ l, Φ x) ⊢ Φ (l[i]'h) ∗ [∗list] x ∈ l.eraseIdx i, Φ x
  | [], _, h => absurd h (by simp)
  | x :: xs, 0, _ => by
    simp only [List.getElem_cons_zero, List.eraseIdx_cons_zero]
    exact BigSepL.bigSepL_cons.1
  | x :: xs, i + 1, h => by
    simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ]
    refine BigSepL.bigSepL_cons.1.trans ?_
    refine (sep_mono_right (bigSepL_eraseIdx Φ xs i (by simp at h; omega))).trans ?_
    exact sep_left_comm.1.trans (sep_mono_right (BigSepL.bigSepL_cons (Φ := fun _ y => Φ y)).2)

/-- An element of a big separating conjunction over a list, and the way back. -/
theorem bigSepL_get_acc {PROP : Type _} [BI PROP] {A : Type _} (Φ : A → PROP) (l : List A) (i : Nat)
    (h : i < l.length) :
    ([∗list] x ∈ l, Φ x) ⊢ Φ (l[i]'h) ∗ (Φ (l[i]'h) -∗ [∗list] x ∈ l, Φ x) := by
  have hl : l[i]? = some (l[i]'h) := List.getElem?_eq_getElem h
  refine (BigSepL.bigSepL_lookup_acc (Φ := fun _ x => Φ x) hl).1.trans (sep_mono_right ?_)
  refine (forall_elim (l[i]'h)).trans ?_
  rw [List.set_getElem_self]


section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`rpctypes`' fact gives `ErrNoLeader`** (an `EtcdError`). -/
theorem errNoLeader_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes ⊢
      ∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
        globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrNoLeader ↦□
          interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x := by
  iintro #Hp
  ihave Hi : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hp
  icases Hi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%x, #Hx⟩⟩
  iexists x
  iexact Hx

/-- **`etcdserverpb`'s fact gives the Lease service's stream descriptor** (`leaseDescOk`,
`etcdserverpbDescs`). -/
theorem leaseDescOk_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ⊢ leaseDescOk := by
  iintro #Hp
  ihave Hi : (go_etcd_io.etcd.cache.v3.etcdserverpbInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hp
  icases Hi with ⟨-, -, -, -, -, -, -, -, ⟨%ssl, %sds, #Hs, #Hsds, %Hc⟩⟩
  unfold leaseDescOk
  iexists ssl, sds
  iframe #
  ipureintro; exact Hc

/-- **`len(ch)`** of a keep-alive channel (`chan.wp_cap`'s companion). -/
theorem wp_kaChan_len {ty : go.GoType} {dir : go.ChanDir}
    [ty ↓u go.ChannelType dir (go.GoType.PointerType go_etcd_io.etcd.client.v3.LeaseKeepAliveResponse.ty)]
    (ch : Loc) (γ : ChanNames) :
    {{ isChan (GF := GF) ch γ Loc }}
      (App (Val #(functions go.len [ty])) (Val #ch))
    {{ (n : w64), RET #n; True }} := by
  wp_start as #Hch
  wp_apply wp_Len (V := Loc) ch γ $$ Hch as %n -
  iapply HΦ
  itrivial

/-- **A new keep-alive channel**: its invariant (the caller's `isChanAny`) and the lessor's
token. -/
theorem chanTok_alloc (ch : Loc) (γ : ChanNames) (buf : List Loc) :
    ⊢ isChan (GF := GF) ch γ Loc -∗ ownChan γ Loc (.Buffered buf) ={⊤}=∗
      chanTok ch ∗ isChanAny γ ch := by
  iintro #Hch Hoc
  imod ghostVar_alloc (GF := GF) () with ⟨%γc, Htok⟩
  imod inv_alloc chanAnyN ⊤ (chanAnyInv γ γc) $$ [Hoc] with #Hinv
  · inext
    unfold chanAnyInv
    iexists (.Buffered buf)
    iframe Hoc
  imodintro
  isplitl [Htok]
  · unfold chanTok
    iexists γ, γc
    iframe #
    iframe
  · unfold isChanAny
    iframe #
    try (iexists γc; iexact Hinv)

/-- **Closing a keep-alive channel with its token**: the token goes into the invariant. -/
theorem chanTok_close_au (γ : ChanNames) (γc : GName) (Φ : IProp GF) :
    ⊢ inv chanAnyN (chanAnyInv (GF := GF) γ γc) -∗ ghostVar γc 1 () -∗ ▷ Φ -∗ closeAu γ Loc Φ := by
  iintro #Hinv Htok HΦ
  unfold closeAu
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold chanAnyInv
  icases Hi with ⟨%s, Hoc, Ht⟩
  iexists s
  iframe Hoc
  rcases s with buf | _ | _ | _ | _ | _ | drain
  all_goals dsimp only
  case Buffered =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Htok] with -
    · inext; iexists (.Closed buf); iframe Hoc; iexact Htok
    imodintro
    iexact HΦ
  case Idle =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Htok] with -
    · inext; iexists (.Closed []); iframe Hoc; iexact Htok
    imodintro
    iexact HΦ
  case Closed =>
    icombine Htok Ht gives %Hv
    exfalso
    revert Hv
    grind
  all_goals itrivial

/-- **`close(ch)`** of a keep-alive channel, with its token. -/
theorem wp_chanTok_close {ty : go.GoType} {dir : go.ChanDir}
    [ty ↓u go.ChannelType dir (go.GoType.PointerType go_etcd_io.etcd.client.v3.LeaseKeepAliveResponse.ty)]
    (ch : Loc) :
    {{ chanTok (GF := GF) ch }}
      (App (Val #(functions go.close [ty])) (Val #ch))
    {{ RET #(); True }} := by
  iintro %Φ Htok HΦ
  unfold chanTok
  icases Htok with ⟨%γ, %γc, #Hch, #Hinv, Htok⟩
  iapply chan.wp_close (ct := ty) (V := Loc) ch γ $$ Hch
  iintro _
  iapply chanTok_close_au γ γc $$ Hinv Htok
  inext
  iapply HΦ
  itrivial

/-- **A non-blocking send on a keep-alive channel, with its token** (`recvKeepAlive`'s
`select { case ch <- karesp: default: }`): the token comes back with the send. -/
theorem chanTok_nonblockingSend (γ : ChanNames) (γc : GName) (v : Loc) (Φ : IProp GF) :
    ⊢ inv chanAnyN (chanAnyInv (GF := GF) γ γc) -∗ ghostVar γc 1 () -∗
      ▷ (ghostVar γc 1 () -∗ Φ) -∗ nonblockingSendAuInner γ v Φ := by
  iintro #Hinv Htok HΦ
  unfold nonblockingSendAuInner
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold chanAnyInv
  icases Hi with ⟨%s, Hoc, Ht⟩
  iexists s
  iframe Hoc
  rcases s with buf | _ | _ | _ | _ | _ | drain
  all_goals dsimp only
  case Buffered =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists (.Buffered (buf ++ [v])); iframe Hoc
    imodintro
    iapply HΦ $$ Htok
  case RcvPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists (.SndCommit v); iframe Hoc
    imodintro
    iapply HΦ $$ Htok
  case Closed =>
    icombine Htok Ht gives %Hv
    exfalso
    revert Hv
    grind
  all_goals itrivial

/-! ### The registry and the alignment -/

/-- A variable held whole is not a variable held persistently. -/
theorem ptsto_iface_ne_discard (p q : Loc) (v w : GoInterface) :
    (p ↦ v : IProp GF) ∗ q ↦□ w ⊢ ⌜p ≠ q⌝ := by
  by_cases hpq : p = q
  · subst hpq
    rw [typedPointsto_unseal]
    unfold typedPointstoWrap
    iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
    rw [typedPointstoDef_heap, typedPointstoDef_heap]
    icombine H1 H2 gives %Hv
    exfalso
    have : ((1 : Qp).val < 1) := Hv.1
    simp at this
  · iintro _
    ipureintro; exact hpq

/-- **A new registry.** -/
theorem lessorReg_alloc (E : CoPset) : ⊢ |={E}=> ∃ γr, lessorReg (GF := GF) γr := by
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Loc) with ⟨%γr, H⟩
  imodintro
  iexists γr
  unfold lessorReg
  iexists ∅
  iframe H
  iapply BigSepM.bigSepM_empty.2
  itrivial

/-- **`KeepAlive` registers the pair `(ch, c)`** at its variable `p` (held whole: not yet a key),
which it gives up for a persistent points-to. -/
theorem lessorReg_register (E : CoPset) (γr : GName) (p ch : Loc) (c : GoInterface) :
    lessorReg (GF := GF) γr ∗ p ↦ c ⊢ |={E}=> lessorReg γr ∗ kaReg γr ch c ∗ p ↦□ c := by
  iintro ⟨Hreg, Hp⟩
  unfold lessorReg
  icases Hreg with ⟨%reg, Hauth, #Hks⟩
  rcases Hlk : reg.lookup p with _ | v
  · imod ghost_map_insert_persist (GF := GF) p ch Hlk $$ Hauth with ⟨Hauth, #He⟩
    imod (typedPointsto_dfractional (GF := GF) p c).dfractional_persist _ $$ Hp with #Hp
    imodintro
    isplitl [Hauth]
    · iexists reg.insert p ch
      iframe Hauth
      iapply (BigSepM.bigSepM_insert (Φ := fun (p : Loc) (_ : Loc) =>
        iprop(∃ v : GoInterface, (p ↦□ v : IProp GF))) (m := reg) Hlk).2
      iframe #
    isplitl
    · unfold kaReg
      iexists p
      iframe #
    · iexact Hp
  · ihave ⟨%w, #Hw⟩ := BigSepM.bigSepM_lookup (Φ := fun (p : Loc) (_ : Loc) =>
      iprop(∃ v : GoInterface, (p ↦□ v : IProp GF))) Hlk $$ Hks
    ihave %Hne := ptsto_iface_ne_discard p p c w $$ [$Hp $Hw]
    exact absurd rfl Hne

/-- No channel, no context: aligned. -/
theorem kaPaired_nil (γr : GName) : ⊢ kaPaired (GF := GF) γr [] [] := by
  unfold kaPaired
  imodintro
  iintro %i %ch %c %H1 -
  simp at H1

/-- **A pair added at the end** (`KeepAlive`'s `append`s). -/
theorem kaPaired_snoc (γr : GName) (chs : List GoChan) (ctxs : List GoInterface) (ch : Loc)
    (c : GoInterface) (Hlen : chs.length = ctxs.length) :
    kaPaired (GF := GF) γr chs ctxs ∗ kaReg γr ch c ⊢ kaPaired γr (chs ++ [ch]) (ctxs ++ [c]) := by
  iintro ⟨#Hp, #Hr⟩
  unfold kaPaired
  imodintro
  iintro %i %ch' %c' %H1 %H2
  rcases Nat.lt_or_ge i chs.length with hi | hi
  · rw [List.getElem?_append_left hi] at H1
    rw [List.getElem?_append_left (by omega)] at H2
    iapply Hp $$ %i %ch' %c' %H1 %H2
  · rw [List.getElem?_append_right hi] at H1
    rw [List.getElem?_append_right (by omega)] at H2
    rcases Nat.lt_or_ge (i - chs.length) 1 with h1 | h1
    · have h0 : i - chs.length = 0 := by omega
      have h0' : i - ctxs.length = 0 := by omega
      rw [h0] at H1; rw [h0'] at H2
      simp only [List.getElem?_cons_zero, Option.some.injEq] at H1 H2
      subst H1 H2
      iexact Hr
    · rw [List.getElem?_eq_none (by simp; omega)] at H1
      cases H1

/-- **A keep-alive's first pair** (`KeepAlive` on a lease with none). -/
theorem kaPaired_singleton (γr : GName) (ch : Loc) (c : GoInterface) :
    kaReg (GF := GF) γr ch c ⊢ kaPaired γr [ch] [c] := by
  have h := kaPaired_snoc (GF := GF) γr [] [] ch c rfl
  simp only [List.nil_append] at h
  iintro #Hr
  ihave #H0 := kaPaired_nil (GF := GF) γr
  iapply h $$ [$H0 $Hr]

/-- **A pair removed** (`keepAliveCtxCloser`'s `append(s[:i], s[i+1:]...)` on both slices, at the
same index). -/
theorem kaPaired_eraseIdx (γr : GName) (chs : List GoChan) (ctxs : List GoInterface) (n : Nat) :
    kaPaired (GF := GF) γr chs ctxs ⊢ kaPaired γr (chs.eraseIdx n) (ctxs.eraseIdx n) := by
  iintro #Hp
  unfold kaPaired
  imodintro
  iintro %i %ch %c %H1 %H2
  rw [List.getElem?_eraseIdx] at H1 H2
  by_cases hi : i < n
  · rw [ite_eq_left hi] at H1 H2
    iapply Hp $$ %i %ch %c %H1 %H2
  · rw [ite_eq_right hi] at H1 H2
    iapply Hp $$ %(i + 1) %ch %c %H1 %H2

/-- **The pair at an index** (by lookups). -/
theorem kaPaired_get (γr : GName) (chs : List GoChan) (ctxs : List GoInterface) (i : Nat)
    (ch : Loc) (c : GoInterface) (h1 : chs[i]? = some ch) (h2 : ctxs[i]? = some c) :
    kaPaired (GF := GF) γr chs ctxs ⊢ kaReg γr ch c := by
  iintro #Hp
  unfold kaPaired
  iapply Hp $$ %i %ch %c %h1 %h2

/-- **The pair at an index.** -/
theorem kaPaired_lookup (γr : GName) (chs : List GoChan) (ctxs : List GoInterface) (i : Nat)
    (h1 : i < chs.length) (h2 : i < ctxs.length) :
    kaPaired (GF := GF) γr chs ctxs ⊢ kaReg γr (chs[i]'h1) (ctxs[i]'h2) := by
  iintro #Hp
  unfold kaPaired
  iapply Hp $$ %i %(chs[i]'h1) %(ctxs[i]'h2) %(List.getElem?_eq_getElem h1) %(List.getElem?_eq_getElem h2)

end lemmas

end EtcdGrove
end Perennial
