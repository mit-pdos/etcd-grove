/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: `Invoke` on a connection dialed with no interceptor

On a connection with no unary interceptor and no default call options (`grpcConn conn addrs [] []
anyRes`: the driver's, `grpc.NewClient` over a `passthrough` target), `ClientConn.Invoke`'s
interceptor chain is the final invoker itself (`chainWP R conn []`), so a call is one attempt, under
the attempt contract (`grpcInvokerOk`). `plain_Invoke` states it at the trivial resource: the
attempt's outcome (`invokeOut`, `grpcInvokerOk`'s post without the resource and peer buffers), and
`plain_Invoke_done` the at-once failures (`grpcInvokerDone`: a cancelled context, a closed
connection).
-/
module

public import Spec.google_golang_org.grpc.ClientConn__Invoke
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.ClientDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An attempt's outcome** (`grpcInvokerOk`'s post, at the trivial resource and no peer buffer). -/
def invokeOut (method : GoString) (addrs : List GoString) (Rep : ProtoMsgT GF) (out : Loc)
    (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Rep.recvOwn out m' ∗ Φ m') ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
      go_etcd_io.etcd.cache.v3.errCellOk err ∗ Rep.own out ∗ notLearnerErr err ∗
      (⌜go_etcd_io.etcd.cache.v3.hasGRPCStatus err⌝ ∨ eofIs err) ∗
      ∃ d : GoString, go_etcd_io.etcd.cache.v3.descIs err d ∗
      ⌜(kvMethod method ∧ ∀ a ∈ addrs, noRefusalAt a) →
        d ∉ go_etcd_io.etcd.cache.v3.refusalDescs⌝ ∗
      (⌜d ∈ handlerDescs⌝ -∗ Ψe d)))

/-- **`Invoke` on a connection with no interceptor** (see the file header). -/
theorem plain_Invoke (wp_Invoke : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG))
    (conn : Loc) (addrs : List GoString) (method : GoString) (Req Rep : ProtoMsgT GF)
    (hreq : grpcReqModelOf GF Req.ty = some Req) (hrep : grpcRepModelOf GF Rep.ty = some Rep)
    (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg) (m : Req.M) (Φ : Rep.M → IProp GF)
    (Ψe : GoString → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (om : GrpcMd) (inp out : Loc) (opts : GoSlice) (vs : List GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗
      grpcConn conn addrs [] [] anyRes ∗ isGrpcRpcsMd addrs method Spec ∗ metadata.outMD ctx om ∗
      ▷ (∀ md, grpcAttemptMd conn om md -∗ Spec md m Φ Ψe) ∗
      ctxOk ctx cd ∗ Req.send inp m ∗ ⌜Req.wireLen m < grpcMsgMax⌝ ∗
      Rep.own out ∗ opts ↦*□ vs ∗ ⌜∀ v ∈ vs, grpcOptOk [] v⌝ ⊢
    WP (App (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"Invoke"))
      (Val #(GoInterface.ok ctx))) (Val #method))
      (Val #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)))
      (Val #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface))) (Val #opts))
    {{ v, ∃ err : GoInterface, ⌜v = #err⌝ ∗ Req.send inp m ∗
        invokeOut method addrs Rep out Φ Ψe err }} := by
  iintro ⟨#Hg, #Hc, #Hrpc, #Hom, Hspec, #Hctx, Hsend, %Hw, Hown, #Hopts, %Hvs⟩
  iapply wp_true_sep
  iapply (wp_Invoke conn addrs [] [] anyRes (GoInterface.ok ctx) method
    (interface.mkOk (go.GoType.PointerType Req.ty) #inp)
    (interface.mkOk (go.GoType.PointerType Rep.ty) #out) opts vs iprop(True))
  iframe #
  isplitr
  · ipureintro; trivial
  isplitr
  · itrivial
  iintro %inv %opts' #Hinv #Hopts'
  simp only [List.nil_append, chainWP]
  iintro -
  iapply wp_true_sep_intro
  iunfold grpcInvokerOk at Hinv
  icases Hinv with ⟨#Htri, -⟩
  ihave Htri' := Htri $$ %method %Req %Rep %hreq %hrep %Spec %m %Φ %Ψe %ctx %cd %om %inp %out %opts'
    %vs %([] : List Loc) %(iprop(True) : IProp GF)
  iapply Htri' $$ [Hspec Hsend Hown]
  · iframe #
    iframe
    try (isplitr; · ipureintro; trivial)
    try (isplitr; · itrivial)
    try (isplitr; · ipureintro; exact Hw)
    try (isplitr; · ipureintro; exact Hvs)
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  inext
  iintro %err ⟨-, Hsend, -, Hout⟩
  iexists err
  iframe Hsend
  isplitr
  · ipureintro; rfl
  unfold invokeOut
  iexact Hout

end defs

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

end Perennial
