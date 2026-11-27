/-
**`ClientConn.NewStream` on an etcd client's connection** (phase7-s3-interceptor, S3.4, 2026-11-26):
the contract of a stream through the connection `clientv3.New` dials (etcd's stream interceptor,
`etcdConnStream`), derived from grpc's interceptor-generic contract (`grpc.ClientConn.NewStream.spec`,
the axiom: the interceptor over grpc's streamer) and the interceptor's contract (`etcdStreamIcOk`, what
`Client.streamClientInterceptor` returns, proved). It was `NewStream`'s axiom at etcd's relation
(`streamMdOk … etcdVersionMd`), with the interceptor inside the boundary. The stream interceptor's
analogue of `EtcdInvoke.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.ClientConn__NewStream
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

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

/-- **`conn.NewStream(ctx, desc, method, opts...)` on an etcd client's connection**
(`etcdWatchConn conn addrs ics`: no default call options, etcd's stream interceptor), for a
client-streaming descriptor, a streaming method registered at every address of `addrs`
(`isGrpcStreamsMd`), a context (`ctxOk`, outgoing metadata `om`) and the client's stream call options
(`streamCallOptsOk`), lent a resource of the connection's family (`clientRes`: a level-0 thread
token): a client stream (`cliStreamIs`, both tokens at `[]`) whose responses carry a dispatch of an
attempt on `withVersion`'s context (`clientAttemptMd conn om md`), with the stream specification at
every such dispatch; or a `nil` stream and an opening error (`cliOpenErr`: `getToken`'s, the
interceptor's `Unimplemented`, or grpc's). -/
abbrev etcdNewStream.spec : Prop :=
  ∀ (conn : Loc) (addrs : List GoString) (ics : List GoFunc) (method : GoString)
    (Req Rep : StreamMsgT GF),
    streamReqModelOf GF Req.ty = some Req → streamRepModelOf GF Rep.ty = some Rep →
  ∀ (Up : Nat → Req.M → IProp GF)
    (Spec : GoString → GrpcMd → StreamSpec Rep.toStreamMsg) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (om : GrpcMd) (desc : Loc) (opts : GoSlice)
    (vs : List GoInterface) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ etcdWatchConn conn addrs ics ∗
      ⌜clientRes R⌝ ∗ R ∗
      isGrpcStreamsMd addrs method (fun _ => Up) Spec ∗ ctxOk ctx cd ∗ metadata.outMD ctx om ∗
      (∃ sd : google_golang_org.grpc.StreamDesc, desc ↦□ sd ∗ ⌜sd.ClientStreams' = true⌝) ∗
      opts ↦*□ vs ∗ streamCallOptsOk vs }}
    (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"NewStream"))
      (Val #(GoInterface.ok ctx))) (Val #desc)) (Val #method)) (Val #opts))
  {{ (cs err : GoInterface), RET (PairV #cs #err); R ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (γ : StreamNames) (Dn : GoString → GrpcMd → Nat → Rep.M → IProp GF)
          (cd' : context.ContextDesc (IProp GF)),
        cliStreamIs cs γ Req.toStreamMsg Rep.toStreamMsg Up
          (fun a md => iprop(⌜a ∈ addrs⌝ ∗ clientAttemptMd conn om md)) Dn cd' clientRes ∗
        cliSendTok (Req := Req.toStreamMsg) γ [] ∗ cliRecvTok (Rep := Rep.toStreamMsg) γ [] ∗
        □ (∀ a md, ⌜a ∈ addrs⌝ -∗ clientAttemptMd conn om md -∗ Spec a md γ (Dn a md))) ∨
      (⌜cs = GoInterface.nil⌝ ∗ cliOpenErr err)) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem etcdNewStream_of (wp_NewStream : grpc.ClientConn.NewStream.spec (GF := GF) (hG := hG)) :
    etcdNewStream.spec (GF := GF) (hG := hG) := by
  intro conn addrs ics method Req Rep hreq hrep Up Spec ctx cd om desc opts vs R
  iintro %Ψ ⟨#Hpkg, #Hwc, %HR, HRr, #Hreg, #Hctx, #Hom, Hdesc, #Hopts, #Hok⟩ HΨ
  iunfold etcdWatchConn at Hwc
  icases Hwc with ⟨#Hconn, #Hcst⟩
  iunfold etcdConnStream at Hcst
  icases Hcst with ⟨%d, %si, #Hco, %Hsi, #Hic⟩
  iapply (wp_NewStream conn addrs ics clientRes d (GoInterface.ok ctx) desc method opts)
  iframe Hpkg Hconn Hco
  iintro %str #Hstr
  simp only [Hsi]
  iunfold etcdStreamIcOk at Hic
  iunfold streamIcOk at Hic
  wp_apply Hic $$ %conn %addrs %method %Req %Rep %hreq %hrep %Up %Spec %ctx %cd %om %desc %opts %vs %R
      %str [HRr Hdesc] as %cs %err ⟨HRr, Hres⟩
  · iframe Hstr HRr Hreg Hctx Hom Hopts Hok Hdesc
    ipureintro; exact HR
  iapply HΨ
  iframe HRr
  icases Hres with (⟨%Herr, %γ, %Dn, %cd', #Hcs, Hst, Hrt, #Hsp⟩ | Herr)
  · ileft
    isplitr
    · ipureintro; exact Herr
    unfold clientAttemptMd
    iexists γ, Dn, cd'
    iframe Hst Hrt
    isplitl []
    · iexact Hcs
    iintro !> %a %md %Ha -
    iapply Hsp $$ %a %md
    ipureintro; exact Ha
  · iright; iexact Herr

end proof

end EtcdGrove
end Perennial
