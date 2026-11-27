/-
**grpc's streamer and the stream interceptor's contract** (phase7-s3-interceptor, S3.4, 2026-11-26;
`notes/phase7-endstate.md` §1.4, SpecPlan's `streamerOk`). Lean-first (no Rocq counterpart).

`(*ClientConn).NewStream` (grpc-go v1.84 `stream.go`) calls the connection's stream interceptor, if
one was dialed, with grpc's `newClientStream` as the streamer, and the streamer itself otherwise
(`ClientConn.NewStream`'s axiom, interceptor-generic since this branch, like `Invoke`'s). This
module states:

* `grpcStreamerOk Opts conn addrs Ok str`: what grpc's streamer `str` of the connection `conn` does
  (trusted text, the claim `NewStream`'s axiom makes of the streamer it passes): it opens one client
  stream of a streaming method registered at the addresses `addrs`, delivering the caller's outgoing
  metadata (`grpcAttemptMd`), its errors grpc's own shape (`grpcErrShape`). `Opts` is the call-option
  predicate the streamer accepts (the axiom fixes it at etcd's client's, `streamCallOptsOk`; a
  parameter here so that the client's own modules below `InvRetry` can name the contract);
* `streamIcOk Opts Ok F si`: a stream interceptor's contract over such a streamer (a definition: no
  trusted text): for a client-streaming descriptor it returns what grpc's streamer would, its attempt
  metadata `F`-related to the caller's (`streamAttemptMd`), its stream's errors anything, and its own
  failures client errors (`cliOpenErr`). etcd's (`Client.streamClientInterceptor`) is proved to meet
  it at `etcdVersionMd`;
* `cliOpenErr`: an error a stream's opening may return (`cliStreamErr` without `streamErr`: etcd's
  interceptor returns `getToken`'s errors and a status error of its own, of which no fact gives the
  error tree `streamErr` states; ledger, 2026-11-26).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A call of the streamer `str` (a `grpc.Streamer`): `str(ctx, desc, cc, method, opts...)`. -/
abbrev streamerCall (str : GoFunc) (ctx desc cc method opts : val) : Expr :=
  App (App (App (App (App (Val #str) (Val ctx)) (Val desc)) (Val cc)) (Val method)) (Val opts)

/-- A call of the stream interceptor `si` (a `grpc.StreamClientInterceptor`):
`si(ctx, desc, cc, method, streamer, opts...)`. -/
abbrev streamIcCall (si : GoFunc) (ctx desc cc method : val) (str : GoFunc) (opts : val) : Expr :=
  App (App (App (App (App (App (Val #si) (Val ctx)) (Val desc)) (Val cc)) (Val method)) (Val #str))
    (Val opts)

/-- **An error a stream's opening returns** (persistent): a non-nil client error (`clientErr`)
grpc's `status` accepts (`statusErrOk`), no caller's `errors.New` value (`errCellOk`). A stream
error (`cliStreamErr`) without the error tree (`streamErr`). -/
def cliOpenErr (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
    go_etcd_io.etcd.cache.v3.errCellOk err)

instance cliOpenErr_persistent (err : GoInterface) : Persistent (cliOpenErr (GF := GF) err) := by
  unfold cliOpenErr; infer_instance

theorem cliOpenErr_of_cliStreamErr (err : GoInterface) (E : GoInterface → IProp GF) :
    cliStreamErr (GF := GF) err E ⊢ cliOpenErr err := by
  unfold cliStreamErr cliOpenErr
  iintro ⟨%h, #Hs, #Hc, -⟩
  iframe Hs Hc
  ipureintro; exact h

/-- An opening error may close a client watch (`closeErrOk`), as a stream error. -/
theorem cliOpenErr_closeErrOk (err : GoInterface) : cliOpenErr (GF := GF) err ⊢ closeErrOk err := by
  unfold cliOpenErr
  iintro ⟨%h, #Hs, #Hc⟩
  ihave %hp := errPtrOk_of_cell err $$ Hc
  iapply (closeErrOk_intro err ⟨fun _ => h.2, hp⟩) $$ Hs

theorem cliStreamErr_mono (err : GoInterface) (E E' : GoInterface → IProp GF) :
    (□ ∀ e, E e -∗ E' e) ⊢ cliStreamErr (GF := GF) err E -∗ cliStreamErr err E' := by
  unfold cliStreamErr
  iintro #HE ⟨%h, #Hs, #Hc, #Ht, #He⟩
  iframe Hs Hc Ht
  isplitr
  · ipureintro; exact h
  imodintro
  iapply HE $$ He

/-- **A client end, weakened**: its dispatch family and its errors' refinement. -/
theorem cliStreamIs_mono (cs : GoInterface) (γ : StreamNames) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Md Md' : GoString → GrpcMd → IProp GF)
    (Dn : GoString → GrpcMd → Nat → Rep.M → IProp GF)
    (cd : context.ContextDesc (IProp GF)) (Ok : IProp GF → Prop) (E E' : GoInterface → IProp GF) :
    (□ ∀ a md, Md a md -∗ Md' a md) ⊢ (□ ∀ e, E e -∗ E' e) -∗
      cliStreamIs cs γ Req Rep Up Md Dn cd Ok E -∗ cliStreamIs cs γ Req Rep Up Md' Dn cd Ok E' := by
  iintro #HM #HE Hcs
  unfold cliStreamIs
  icases Hcs with ⟨%ci, %Hci, #Hs, #Hr, #Hc, #Hx⟩
  iexists ci
  isplitr
  · ipureintro; exact Hci
  isplitr
  · iintro !> %L %l %m %R %Φ !> Hpre HΦ
    iapply Hs $$ Hpre
    inext
    iintro %err ⟨HR, Hsend, Hres⟩
    iapply HΦ
    iframe HR Hsend
    icases Hres with (Hok | ⟨#Herr, Ht⟩)
    · ileft; iexact Hok
    · iright
      iframe Ht
      iapply cliStreamErr_mono err E E' $$ HE Herr
  isplitr
  · iintro !> %L %out %R %Φ !> Hpre HΦ
    iapply Hr $$ Hpre
    inext
    iintro %err ⟨HR, Hres⟩
    iapply HΦ
    iframe HR
    icases Hres with (⟨%Hn, %a, %md, %m, Hmd, Hrest⟩ | Heof | ⟨#Herr, Ht⟩)
    · ileft
      isplitr
      · ipureintro; exact Hn
      iexists a, md, m
      iframe Hrest
      iapply HM $$ Hmd
    · iright; ileft; iexact Heof
    · iright; iright
      iframe Ht
      iapply cliStreamErr_mono err E E' $$ HE Herr
  isplitr
  · iintro !> %L %R %Φ !> Hpre HΦ
    iapply Hc $$ Hpre
    inext
    iintro %err ⟨HR, Hup, Hres⟩
    iapply HΦ
    iframe HR Hup
    icases Hres with (Hn | #Herr)
    · ileft; iexact Hn
    · iright
      iapply cliStreamErr_mono err E E' $$ HE Herr
  iexact Hx

/-- **grpc's streamer `str` of the connection `conn`** (persistent; trusted text, what
`ClientConn.NewStream`'s axiom claims of the streamer, grpc's `newClientStream`, it passes the
connection's stream interceptor, or calls itself; phase7-s3-interceptor, 2026-11-26): called with a
context (`ctxOk`, outgoing metadata `om`), a client- or server-streaming descriptor, a streaming
method registered at every address of `addrs` with one client content `Up` and a stream
specification per address (`isGrpcStreamsMd`), and call options it accepts (`Opts`), lent the
caller's resource `R` of the connection's family (`Ok R`, for the per-RPC credentials), it returns `R`
and a client stream (`cliStreamIs`, both tokens at `[]`) whose responses carry the dispatch `(a, md)`
(`a ∈ addrs`, `md` an attempt's metadata for `om`: `grpcAttemptMd`), its errors grpc's own shape
(`grpcErrShape`), with the stream specification `Spec a md γ (Dn a md)` at every address of `addrs`
and every metadata `md`; or a `nil` stream and a stream error of grpc's shape (`cliStreamErr`).
True of grpc-go v1.84 on the connections `grpcConn` describes (`ClientConn.NewStream`'s docstring has
the evidence, as the axiom's text before this branch, which stated this of `NewStream` at no stream
interceptor): every attempt takes one transport and runs one handler, a transparent retry happens
only of an unprocessed first attempt and may re-pick the address and call the per-RPC credentials
again, so the dispatch is known only from the responses. The stream specification holds at every
metadata, not only at the attempts': the content `Dn a md` is the address's table's for the
dispatch (`grpcStreamSvcAt`'s `dn₀ md γ`), which meets its specification at every `md`
(`grpcStreamSvcAt`'s `□ ∀ md γ, spec₀ md γ (dn₀ md γ)`); until this branch the axiom stated it only
at the attempts' metadata, which a stream interceptor whose metadata is known up to a relation
(etcd's `withVersion`: some API version) cannot carry over to the caller's. -/
def grpcStreamerOk (Opts : List GoInterface → IProp GF) (conn : Loc) (addrs : List GoString)
    (Ok : IProp GF → Prop) (str : GoFunc) : IProp GF :=
  iprop(□ ∀ (method : GoString) (Req Rep : StreamMsgT GF)
      (_ : streamReqModelOf GF Req.ty = some Req) (_ : streamRepModelOf GF Rep.ty = some Rep)
      (Up : Nat → Req.M → IProp GF) (Spec : GoString → GrpcMd → StreamSpec Rep.toStreamMsg)
      (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (desc : Loc)
      (opts : GoSlice) (vs : List GoInterface) (R : IProp GF),
    {{ ⌜Ok R⌝ ∗ R ∗ isGrpcStreamsMd addrs method (fun _ => Up) Spec ∗ ctxOk ctx cd ∗
        metadata.outMD ctx om ∗
        (∃ sd : google_golang_org.grpc.StreamDesc, desc ↦□ sd ∗
          ⌜sd.ClientStreams' = true ∨ sd.ServerStreams' = true⌝) ∗
        opts ↦*□ vs ∗ Opts vs }}
      (streamerCall str #(GoInterface.ok ctx) #desc #conn #method #opts)
    {{ (cs err : GoInterface), RET (PairV #cs #err); R ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (γ : StreamNames)
            (Dn : GoString → GrpcMd → Nat → Rep.M → IProp GF) (cd' : context.ContextDesc (IProp GF)),
          cliStreamIs cs γ Req.toStreamMsg Rep.toStreamMsg Up
            (fun a md => iprop(⌜a ∈ addrs⌝ ∗ grpcAttemptMd conn om md)) Dn cd' Ok grpcErrShape ∗
          cliSendTok (Req := Req.toStreamMsg) γ [] ∗ cliRecvTok (Rep := Rep.toStreamMsg) γ [] ∗
          □ (∀ a md, ⌜a ∈ addrs⌝ -∗ Spec a md γ (Dn a md))) ∨
        (⌜cs = GoInterface.nil⌝ ∗ cliStreamErr err grpcErrShape)) }})

instance grpcStreamerOk_persistent (Opts : List GoInterface → IProp GF) (conn : Loc)
    (addrs : List GoString) (Ok : IProp GF → Prop) (str : GoFunc) :
    Persistent (grpcStreamerOk Opts conn addrs Ok str) := by
  unfold grpcStreamerOk; infer_instance

/-- **The stream interceptor `si`'s contract, at the metadata relation `F`** (persistent; a
definition, phase7-s3-interceptor, 2026-11-26): called on a connection `conn` to `addrs` with grpc's
streamer of it (`grpcStreamerOk`), a context (`ctxOk`, outgoing metadata `om`), a client-streaming
descriptor, a streaming method registered at `addrs`, call options `Opts` accepts, and the caller's
resource `R` (`Ok R`), it returns `R` and a client stream whose responses carry a dispatch `(a, md)`
of an attempt for some outgoing metadata `F`-related to `om` (`streamAttemptMd conn F om md`), its
errors anything, with the stream specification at every address and metadata; or a `nil` stream and
an opening error (`cliOpenErr`). What `etcdNewStream` derives `NewStream`'s etcd form from;
`Client.streamClientInterceptor` returns an interceptor meeting it at `etcdVersionMd`. -/
def streamIcOk (Opts : List GoInterface → IProp GF) (Ok : IProp GF → Prop)
    (F : GrpcMd → GrpcMd → Prop) (si : GoFunc) : IProp GF :=
  iprop(□ ∀ (conn : Loc) (addrs : List GoString) (method : GoString) (Req Rep : StreamMsgT GF)
      (_ : streamReqModelOf GF Req.ty = some Req) (_ : streamRepModelOf GF Rep.ty = some Rep)
      (Up : Nat → Req.M → IProp GF) (Spec : GoString → GrpcMd → StreamSpec Rep.toStreamMsg)
      (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (desc : Loc)
      (opts : GoSlice) (vs : List GoInterface) (R : IProp GF) (str : GoFunc),
    {{ grpcStreamerOk Opts conn addrs Ok str ∗ ⌜Ok R⌝ ∗ R ∗
        isGrpcStreamsMd addrs method (fun _ => Up) Spec ∗ ctxOk ctx cd ∗ metadata.outMD ctx om ∗
        (∃ sd : google_golang_org.grpc.StreamDesc, desc ↦□ sd ∗ ⌜sd.ClientStreams' = true⌝) ∗
        opts ↦*□ vs ∗ Opts vs }}
      (streamIcCall si #(GoInterface.ok ctx) #desc #conn #method str #opts)
    {{ (cs err : GoInterface), RET (PairV #cs #err); R ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (γ : StreamNames)
            (Dn : GoString → GrpcMd → Nat → Rep.M → IProp GF) (cd' : context.ContextDesc (IProp GF)),
          cliStreamIs cs γ Req.toStreamMsg Rep.toStreamMsg Up
            (fun a md => iprop(⌜a ∈ addrs⌝ ∗ streamAttemptMd conn F om md)) Dn cd' Ok ∗
          cliSendTok (Req := Req.toStreamMsg) γ [] ∗ cliRecvTok (Rep := Rep.toStreamMsg) γ [] ∗
          □ (∀ a md, ⌜a ∈ addrs⌝ -∗ Spec a md γ (Dn a md))) ∨
        (⌜cs = GoInterface.nil⌝ ∗ cliOpenErr err)) }})

instance streamIcOk_persistent (Opts : List GoInterface → IProp GF) (Ok : IProp GF → Prop)
    (F : GrpcMd → GrpcMd → Prop) (si : GoFunc) : Persistent (streamIcOk Opts Ok F si) := by
  unfold streamIcOk; infer_instance

end defs

end EtcdGrove
end Perennial
