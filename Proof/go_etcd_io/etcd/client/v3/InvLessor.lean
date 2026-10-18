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
`keepAliveCtxCloser`; `closeRequireLeader`, names only) need; closing puts the token in the
invariant. A channel is closed once: its token is in the lock invariant while the channel is in
some `ka.chs`, and every close removes the channel from it (`keepAlive.close` is called on a
keep-alive just removed from the map, or on all of them before the map is replaced).

**A keep-alive** (`kaOwn ka`, `*keepAlive`): its `chs` and `ctxs` slices (equally long: a context
`i` is channel `i`'s, which `keepAliveCtxCloser` indexes `chs` by), each channel's token, each
context a context (`kaCtxOk`: `ctxs` holds what `KeepAlive` was given, wrapped by
`context.WithValue`), its `deadline` and `nextKeepAlive`, and its `donec` (read-only, a broadcast
channel: nothing is sent; the right to close it, `.Pending`, is the keep-alive's, used once by
`keepAlive.close`; `kaDone`, persistent, for `KeepAlive` and `keepAliveCtxCloser`, which read it
outside the lock).

**The lessor's lock invariant** (`lessorInv l`): the map of keep-alives with each one's `kaOwn`,
`stream`, `streamCancel` (`nil` or a cancel function) and `loopErr`. **The lessor** (`lessorAt l
addr`, persistent): what `NewLeaseFromLeaseClient` set and nobody writes again: `donec` (a
broadcast channel whose close is the receive loop's: the right is `firstKeepAliveOnce`'s resource,
handed to the loop the `Once` starts), `stopCtx` (a context), `lg` (non-nil),
`firstKeepAliveTimeout`, the unary calls' `remote` and `callOpts` (`lessorRemoteAt`), `mu` (with
`lessorInv`) and `firstKeepAliveOnce`.

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

/-- **The keep-alive `ka`** (see the file header). -/
def kaOwn (ka : Loc) : IProp GF :=
  iprop(∃ (chsS ctxsS : GoSlice) (chs : List GoChan) (ctxs : List GoInterface)
      (dl nk : time.Time) (kd : GoChan) (γkd : ChanNames),
    kaF go!"chs" ka ↦ chsS ∗ chsS ↦* chs ∗ ownSliceCap GoChan chsS (DFrac.own 1) ∗
    kaF go!"ctxs" ka ↦ ctxsS ∗ ctxsS ↦* ctxs ∗ ownSliceCap GoInterface ctxsS (DFrac.own 1) ∗
    ⌜chs.length = ctxs.length⌝ ∗
    kaF go!"deadline" ka ↦ dl ∗ kaF go!"nextKeepAlive" ka ↦ nk ∗
    kaDone ka kd γkd ∗ ownBroadcastChan kd γkd (iprop(True) : IProp GF) .Pending ∗
    ([∗list] ch ∈ chs, chanTok ch) ∗ ([∗list] c ∈ ctxs, kaCtxOk c))

/-- A cancel function that may be called any number of times (and returns). -/
def cancelAny (sc : GoFunc) : IProp GF :=
  iprop(∃ γ : context.ContextNames, context.cancelSpec sc γ iprop(True))

instance cancelAny_persistent (sc : GoFunc) : Persistent (cancelAny (GF := GF) sc) := by
  unfold cancelAny; infer_instance

/-- **The lessor's lock invariant** (see the file header). -/
def lessorInv (l : Loc) : IProp GF :=
  iprop(∃ (mref : Loc) (m : GMap w64 Loc) (st : GoInterface) (sc : GoFunc) (e : GoInterface),
    lsF go!"keepAlives" l ↦ mref ∗ mref ↦$ m ∗ ([∗map] _id ↦ ka ∈ m, kaOwn (GF := GF) ka) ∗
    lsF go!"stream" l ↦ st ∗ lsF go!"streamCancel" l ↦ sc ∗
    (⌜sc = func.nil⌝ ∨ cancelAny (GF := GF) sc) ∗
    lsF go!"loopErr" l ↦ e)

/-- **The `*lessor` `l`** over a connection to `addr` (persistent; see the file header). -/
def lessorAt (l : Loc) (addr : GoString) : IProp GF :=
  iprop(∃ (dc : GoChan) (γd : ChanNames) (sc : GoInterfaceOk)
      (scd : context.ContextDesc (IProp GF)) (lg : Loc) (d : time.Duration),
    lsF go!"donec" l ↦□ dc ∗ ownBroadcastChan dc γd (iprop(True) : IProp GF) .Unknown ∗
    lsF go!"stopCtx" l ↦□ GoInterface.ok sc ∗ context.isContext sc scd ∗
    lsF go!"lg" l ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    lsF go!"firstKeepAliveTimeout" l ↦□ d ∗
    lessorRemoteAt l addr ∗
    sync.isMutex (lsF go!"mu" l) (lessorInv l) ∗
    sync.isOnce (lsF go!"firstKeepAliveOnce" l) (ownBroadcastChan dc γd (iprop(True) : IProp GF) .Pending)
      iprop(True))

instance lessorAt_persistent (l : Loc) (addr : GoString) :
    Persistent (lessorAt (GF := GF) l addr) := by
  unfold lessorAt; infer_instance

end defs

/-! ## Lemmas -/

/-- The `i`th key of a list without duplicates is not among the keys before it. -/
theorem nodup_getElem?_not_mem_take {α : Type _} (l : List α) (hnd : l.Nodup) (i : Nat) (x : α)
    (h : l[i]? = some x) : x ∉ l.take i := by
  intro hm
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hm
  rw [List.getElem_take] at hjx
  have hjl : j < l.length := by
    have := List.length_take_le' i l; simp at hj; omega
  have hil : i < l.length := (List.getElem?_eq_some_iff.1 h).1
  have hji : j < i := by simp at hj; omega
  have := list_nodup_getElem?_inj l hnd i j x h (by rw [List.getElem?_eq_getElem hjl, hjx])
  omega

/-- The `i`th key is among the first `i + 1`. -/
theorem getElem?_mem_take_succ {α : Type _} (l : List α) (i : Nat) (x : α)
    (h : l[i]? = some x) : x ∈ l.take (i + 1) := by
  rw [List.take_add_one, h]; simp

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

end lemmas

end EtcdGrove
end Perennial
