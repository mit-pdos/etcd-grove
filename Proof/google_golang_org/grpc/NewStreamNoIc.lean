/-
**`ClientConn.NewStream` on a connection with no stream interceptor** (phase7-s3-interceptor,
2026-11-26): the Hoare triple `NewStream`'s axiom stated before it became interceptor-generic, at
`d.streamIc = none`, derived from the axiom (`grpc.ClientConn.NewStream.spec`) and grpc's streamer's
contract (`grpcStreamerOk`). What the gRPC driver's stubs (`examples/lib/grpcdriver/svc`) use.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.ClientConn__NewStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`conn.NewStream(ctx, desc, method, opts...)` with no stream interceptor** (`d.streamIc =
none`): grpc's streamer's post (`grpcStreamerOk`), its dispatch's metadata stated as
`streamAttemptMd` at equality and its errors `streamErrShape d` (grpc's own), the stream
specification at the attempts' metadata (the text of `NewStream`'s axiom until 2026-11-26 at
`streamMdOk d F`'s first case). -/
abbrev grpc.ClientConn.NewStreamNoIc.spec : Prop :=
  ∀ (conn : Loc) (addrs : List GoString) (ics : List GoFunc) (Ok : IProp GF → Prop)
    (d : GrpcConnOpts) (method : GoString) (Req Rep : StreamMsgT GF),
    streamReqModelOf GF Req.ty = some Req → streamRepModelOf GF Rep.ty = some Rep →
  ∀ (Up : Nat → Req.M → IProp GF)
    (Spec : GoString → GrpcMd → StreamSpec Rep.toStreamMsg) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (desc : Loc) (opts : GoSlice)
    (vs : List GoInterface) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcConn conn addrs ics [] Ok ∗
      grpcConnOpts conn d ∗ ⌜d.streamIc = none⌝ ∗ ⌜Ok R⌝ ∗ R ∗
      isGrpcStreamsMd addrs method (fun _ => Up) Spec ∗ ctxOk ctx cd ∗ metadata.outMD ctx om ∗
      (∃ sd : google_golang_org.grpc.StreamDesc, desc ↦□ sd ∗
        ⌜sd.ClientStreams' = true ∨ (sd.ServerStreams' = true ∧ d.streamIc = none)⌝) ∗
      opts ↦*□ vs ∗ streamCallOptsOk vs }}
    (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"NewStream"))
      (Val #(GoInterface.ok ctx))) (Val #desc)) (Val #method)) (Val #opts))
  {{ (cs err : GoInterface), RET (PairV #cs #err); R ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (γ : StreamNames) (Dn : GoString → GrpcMd → Nat → Rep.M → IProp GF)
          (cd' : context.ContextDesc (IProp GF)),
        cliStreamIs cs γ Req.toStreamMsg Rep.toStreamMsg Up
          (fun a md => iprop(⌜a ∈ addrs⌝ ∗ streamAttemptMd conn (fun om om' => om' = om) om md)) Dn cd'
          Ok (streamErrShape d) ∗
        cliSendTok (Req := Req.toStreamMsg) γ [] ∗ cliRecvTok (Rep := Rep.toStreamMsg) γ [] ∗
        □ (∀ a md, ⌜a ∈ addrs⌝ -∗ streamAttemptMd conn (fun om om' => om' = om) om md -∗
          Spec a md γ (Dn a md))) ∨
      (⌜cs = GoInterface.nil⌝ ∗ cliStreamErr err (streamErrShape d))) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem grpc.ClientConn.NewStreamNoIc_of
    (wp_NewStream : grpc.ClientConn.NewStream.spec (GF := GF) (hG := hG)) :
    grpc.ClientConn.NewStreamNoIc.spec (GF := GF) (hG := hG) := by
  intro conn addrs ics Ok d method Req Rep hreq hrep Up Spec ctx cd om desc opts vs R
  iintro %Ψ ⟨#Hpkg, #Hconn, #Hco, %Hnone, %HR, HRr, #Hreg, #Hctx, #Hom, Hdesc, #Hopts, #Hok⟩ HΨ
  have hE : streamErrShape (GF := GF) d = grpcErrShape := by
    funext err; unfold streamErrShape; rw [Hnone]
  rw [hE]
  iapply (wp_NewStream conn addrs ics Ok d (GoInterface.ok ctx) desc method opts)
  iframe Hpkg Hconn Hco
  iintro %str #Hstr
  simp only [Hnone]
  iunfold grpcStreamerOk at Hstr
  icases Hdesc with ⟨%sd, #Hsd, %Hsds⟩
  wp_apply Hstr $$ %method %Req %Rep %hreq %hrep %Up %Spec %ctx %cd %om %desc %opts %vs %R [HRr]
    as %cs %err ⟨HRr, Hres⟩
  · iframe HRr Hreg Hctx Hom Hopts Hok
    isplitr
    · ipureintro; exact HR
    iexists sd
    iframe Hsd
    ipureintro
    rcases Hsds with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  iapply HΨ
  iframe HRr
  icases Hres with (⟨%Herr, %γ, %Dn, %cd', #Hcs, Hst, Hrt, #Hsp⟩ | Herr)
  · ileft
    isplitr
    · ipureintro; exact Herr
    iexists γ, Dn, cd'
    iframe Hst Hrt
    isplitl []
    · iapply (cliStreamIs_mono cs γ Req.toStreamMsg Rep.toStreamMsg Up _ _ Dn cd' Ok grpcErrShape
        grpcErrShape) $$ [] [] Hcs
      · iintro !> %a %md ⟨%Ha, #Hmd⟩
        isplitr
        · ipureintro; exact Ha
        unfold streamAttemptMd
        iexists om
        iframe Hmd
        ipureintro; rfl
      · iintro !> %e #He; iexact He
    iintro !> %a %md %Ha -
    iapply Hsp $$ %a %md
    ipureintro; exact Ha
  · iright; iexact Herr

end proof

end EtcdGrove
end Perennial
