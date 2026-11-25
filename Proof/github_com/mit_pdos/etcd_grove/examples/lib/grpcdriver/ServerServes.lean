/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the server serves the table's unary entries

From the methods' specs (`server.Echo.spec`, `server.Fail.spec`) and the generated handlers'
(`svc._Driver_Echo_Handler.spec`, `svc._Driver_Fail_Handler.spec`), taken as hypotheses:

* each method meets its table spec as a service method (`grpcHandlerOkMd`, at any resource);
* each generated handler on the server `s` meets it as a run (`grpcRunOkMd`), with no interceptors
  (`grpc.NewServer()` with no options: the chain `[]`);
* so `s`'s registrations serve the table's entries `echoName`, `failName` and `metaName` (`grpcServesEnt`),
  for registrations that put, under each name, its generated handler on `s` and no stream.

-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Echo
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Fail
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Meta
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_Echo_Handler
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_Fail_Handler
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_Meta_Handler
public import Proof.google_golang_org.grpc.InvGrpcRun

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section serves
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- `*server` implements `svc.DriverServer` (a method-set fact). -/
theorem server_isDriverServer :
    go.typeSetContains (go.GoType.PointerType server.ty) svc.DriverServer.ty = true := by
  go_type_set

/-- The table's entry for `echoName`. -/
theorem drvSvc_echo (γid : GName) :
    drvSvc (GF := GF) γid echoName =
      some (.unary ⟨reqWire (GF := GF), repWire (GF := GF), echoSpec γid⟩) := by
  unfold drvSvc
  rw [if_pos rfl]

/-- The table's entry for `failName`. -/
theorem drvSvc_fail (γid : GName) :
    drvSvc (GF := GF) γid failName =
      some (.unary ⟨reqWire (GF := GF), repWire (GF := GF), failSpec⟩) := by
  unfold drvSvc
  rw [if_neg (by decide), if_pos rfl]

/-- The table's entry for `metaName`. -/
theorem drvSvc_meta (γid : GName) :
    drvSvc (GF := GF) γid metaName =
      some (.unary ⟨reqWire (GF := GF), repWire (GF := GF), metaSpec⟩) := by
  unfold drvSvc
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- **`Echo` meets `echoSpec`** as a service method (at any resource `S`, which it does not touch). -/
theorem echo_handlerOk (wp_Echo : server.Echo.spec (GF := GF) (hG := hG)) (γid : GName) (s : Loc)
    (S : IProp GF) :
    isDrvServer γid s ⊢
      grpcHandlerOkMd (Req := (pbStringValueT (GF := GF)).toProtoMsg)
        (Rep := (pbStringValueRT (GF := GF)).toProtoMsg)
        (s @!! go.GoType.PointerType server.ty @!! go!"Echo") S (echoSpec γid) := by
  iintro #Hs
  unfold grpcHandlerOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨HS, #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  iunfold grpcSpecAt at HSpec
  icases HSpec with ⟨%md, -, HSpec⟩
  iapply wp_Echo γid s ci r m md Φ Ψe $$ [HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨%Herr, Hsend, HΦ⟩
  subst Herr
  iapply HΨ
  iframe HS
  isplitl [Hsend HΦ]
  · iintro %_
    simp only [pbStringValueRT, pbStringValueR]
    iexists _
    isplitl [Hsend]
    · iexact Hsend
    · iexact HΦ
  isplitr
  · iapply handlerErrOut_nil
  · iapply go_etcd_io.etcd.cache.v3.srvErrOk_nil

/-- **`Fail` meets `failSpec`** as a service method (at any resource `S`, which it does not touch). -/
theorem fail_handlerOk (wp_Fail : server.Fail.spec (GF := GF) (hG := hG)) (s : Loc) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ⊢
      grpcHandlerOkMd (Req := (pbStringValueT (GF := GF)).toProtoMsg)
        (Rep := (pbStringValueRT (GF := GF)).toProtoMsg)
        (s @!! go.GoType.PointerType server.ty @!! go!"Fail") S failSpec := by
  iintro #Hpkg
  unfold grpcHandlerOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨HS, #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  iunfold grpcSpecAt at HSpec
  icases HSpec with ⟨%md, -, HSpec⟩
  iapply wp_Fail s ci r m md Φ Ψe $$ [HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨%Hne, Hout, #Hse⟩
  iapply HΨ
  iframe
  iframe Hse
  iintro %Hnil
  exact absurd Hnil Hne

/-- **`Meta` meets `metaSpec`** as a service method (at any resource `S`, which it does not touch). -/
theorem meta_handlerOk (wp_Meta : server.Meta.spec (GF := GF) (hG := hG)) (s : Loc) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ⊢
      grpcHandlerOkMd (Req := (pbStringValueT (GF := GF)).toProtoMsg)
        (Rep := (pbStringValueRT (GF := GF)).toProtoMsg)
        (s @!! go.GoType.PointerType server.ty @!! go!"Meta") S metaSpec := by
  iintro #Hpkg
  unfold grpcHandlerOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨HS, #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  iunfold grpcSpecAt at HSpec
  icases HSpec with ⟨%md, #Hmd, HSpec⟩
  iapply wp_Meta s ci r m md Φ Ψe $$ [HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨%Herr, Hsend, HΦ⟩
  subst Herr
  iapply HΨ
  iframe HS
  isplitl [Hsend HΦ]
  · iintro %_
    simp only [pbStringValueRT, pbStringValueR]
    iexists _
    isplitl [Hsend]
    · iexact Hsend
    · iexact HΦ
  isplitr
  · iapply handlerErrOut_nil
  · iapply go_etcd_io.etcd.cache.v3.srvErrOk_nil

/-- **The generated `Echo` handler on the server `s` meets `echoSpec` as a run** (no interceptors). -/
theorem echo_runOk (wp_Echo : server.Echo.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_Echo_Handler.spec (GF := GF) (hG := hG)) (γid : GName) (s : Loc) :
    isDrvServer γid s ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcRunOkMd (Req := (pbStringValueT (GF := GF)).toProtoMsg)
        (Rep := (pbStringValueRT (GF := GF)).toProtoMsg)
        #(functions svc._Driver_Echo_Handler []) (interface.mkOk (go.GoType.PointerType server.ty) #s)
        [] (echoSpec γid) := by
  iintro ⟨#Hs, #Hsvc⟩
  ihave #Hh := echo_handlerOk wp_Echo γid s iprop((True : IProp GF) ∗ [∗list] R ∈ ([] : List (IProp GF)), R) $$ Hs
  ihave #Hh' := grpcHandlerOkMd_own _ _ _ $$ Hh
  unfold grpcRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HT, Hlc, #Hctx, #Hrc, #Hd, #Hch, HSpec⟩ HΨ
  iapply (wp_H (pbStringValueT (GF := GF)).toProtoMsg (pbStringValueRT (GF := GF)).toProtoMsg
    (echoSpec γid) ⟨go.GoType.PointerType server.ty, #s⟩ iprop(True) [] [] (fun _ => iprop(True))
    m Φ Ψe ci cd dec ui rfl rfl server_isDriverServer) $$ [HSpec]
  · isplitr
    · iexact Hsvc
    isplitr
    · iintro !> %l Hl
      simp only [pbStringValueT, pbStringValue]
      iexact Hl
    isplitr
    · iexact Hh'
    isplitr
    · simp only [srvInterceptorsOk]
      itrivial
    isplitr
    · iintro !> %l -
      itrivial
    isplitr
    · itrivial
    isplitr
    · iapply (BigSepL.bigSepL_nil_intro (PROP := IProp GF) (P := iprop(True)))
      itrivial
    iframe; iframe #
  inext
  iintro %resp %err ⟨-, -, Hres, Herr, #Hse⟩
  iapply HΨ
  iframe Hse
  iframe

/-- **The generated `Fail` handler on the server `s` meets `failSpec` as a run** (no
interceptors). -/
theorem fail_runOk (wp_Fail : server.Fail.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_Fail_Handler.spec (GF := GF) (hG := hG)) (s : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcRunOkMd (Req := (pbStringValueT (GF := GF)).toProtoMsg)
        (Rep := (pbStringValueRT (GF := GF)).toProtoMsg)
        #(functions svc._Driver_Fail_Handler []) (interface.mkOk (go.GoType.PointerType server.ty) #s)
        [] failSpec := by
  iintro ⟨#Hpkg, #Hsvc⟩
  ihave #Hh := fail_handlerOk wp_Fail s iprop((True : IProp GF) ∗ [∗list] R ∈ ([] : List (IProp GF)), R) $$ Hpkg
  ihave #Hh' := grpcHandlerOkMd_own _ _ _ $$ Hh
  unfold grpcRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HT, Hlc, #Hctx, #Hrc, #Hd, #Hch, HSpec⟩ HΨ
  iapply (wp_H (pbStringValueT (GF := GF)).toProtoMsg (pbStringValueRT (GF := GF)).toProtoMsg
    failSpec ⟨go.GoType.PointerType server.ty, #s⟩ iprop(True) [] [] (fun _ => iprop(True))
    m Φ Ψe ci cd dec ui rfl rfl server_isDriverServer) $$ [HSpec]
  · isplitr
    · iexact Hsvc
    isplitr
    · iintro !> %l Hl
      simp only [pbStringValueT, pbStringValue]
      iexact Hl
    isplitr
    · iexact Hh'
    isplitr
    · simp only [srvInterceptorsOk]
      itrivial
    isplitr
    · iintro !> %l -
      itrivial
    isplitr
    · itrivial
    isplitr
    · iapply (BigSepL.bigSepL_nil_intro (PROP := IProp GF) (P := iprop(True)))
      itrivial
    iframe; iframe #
  inext
  iintro %resp %err ⟨-, -, Hres, Herr, #Hse⟩
  iapply HΨ
  iframe Hse
  iframe

/-- **The server's registrations serve the table's `Echo` entry** (`grpcServesEnt`): for
registrations that put under `echoName` the generated handler on `s` and no stream, at
`StringValue`'s registered models. -/
theorem echo_servesEnt (wp_Echo : server.Echo.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_Echo_Handler.spec (GF := GF) (hG := hG)) (γid : GName) (s : Loc)
    (sics : List GoFunc) (regs sregs : List (GoString × GoFunc × GoInterface))
    (hsr : echoName ∉ sregs.map Prod.fst)
    (hreg : ∀ mh srv, (echoName, mh, srv) ∈ regs →
      mh = functions svc._Driver_Echo_Handler [] ∧
        srv = interface.mkOk (go.GoType.PointerType server.ty) #s) :
    isDrvServer γid s ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcServesEnt [] sics regs sregs echoName
        (.unary ⟨reqWire (GF := GF), repWire (GF := GF), echoSpec γid⟩) := by
  iintro ⟨#Hs, #Hsvc⟩
  simp only [grpcServesEnt]
  isplitr
  · ipureintro; exact hsr
  iintro %mh %srv %hin
  obtain ⟨rfl, rfl⟩ := hreg mh srv hin
  iexists (pbStringValueT (GF := GF)), (pbStringValueRT (GF := GF)), echoSpec γid
  isplitr
  · ipureintro
    exact ⟨pbStringValueT_reqReg, pbStringValueRT_repReg, rfl⟩
  iapply echo_runOk wp_Echo wp_H γid s
  iframe #

/-- **The server's registrations serve the table's `Fail` entry** (`grpcServesEnt`), as
`echo_servesEnt`. -/
theorem fail_servesEnt (wp_Fail : server.Fail.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_Fail_Handler.spec (GF := GF) (hG := hG)) (s : Loc)
    (sics : List GoFunc) (regs sregs : List (GoString × GoFunc × GoInterface))
    (hsr : failName ∉ sregs.map Prod.fst)
    (hreg : ∀ mh srv, (failName, mh, srv) ∈ regs →
      mh = functions svc._Driver_Fail_Handler [] ∧
        srv = interface.mkOk (go.GoType.PointerType server.ty) #s) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcServesEnt [] sics regs sregs failName
        (.unary ⟨reqWire (GF := GF), repWire (GF := GF), failSpec⟩) := by
  iintro ⟨#Hpkg, #Hsvc⟩
  simp only [grpcServesEnt]
  isplitr
  · ipureintro; exact hsr
  iintro %mh %srv %hin
  obtain ⟨rfl, rfl⟩ := hreg mh srv hin
  iexists (pbStringValueT (GF := GF)), (pbStringValueRT (GF := GF)), (failSpec (GF := GF))
  isplitr
  · ipureintro
    exact ⟨pbStringValueT_reqReg, pbStringValueRT_repReg, rfl⟩
  iapply fail_runOk wp_Fail wp_H s
  iframe #

/-- **The generated `Meta` handler on the server `s` meets `metaSpec` as a run** (no
interceptors). -/
theorem meta_runOk (wp_Meta : server.Meta.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_Meta_Handler.spec (GF := GF) (hG := hG)) (s : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcRunOkMd (Req := (pbStringValueT (GF := GF)).toProtoMsg)
        (Rep := (pbStringValueRT (GF := GF)).toProtoMsg)
        #(functions svc._Driver_Meta_Handler []) (interface.mkOk (go.GoType.PointerType server.ty) #s)
        [] metaSpec := by
  iintro ⟨#Hpkg, #Hsvc⟩
  ihave #Hh := meta_handlerOk wp_Meta s iprop((True : IProp GF) ∗ [∗list] R ∈ ([] : List (IProp GF)), R) $$ Hpkg
  ihave #Hh' := grpcHandlerOkMd_own _ _ _ $$ Hh
  unfold grpcRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HT, Hlc, #Hctx, #Hrc, #Hd, #Hch, HSpec⟩ HΨ
  iapply (wp_H (pbStringValueT (GF := GF)).toProtoMsg (pbStringValueRT (GF := GF)).toProtoMsg
    metaSpec ⟨go.GoType.PointerType server.ty, #s⟩ iprop(True) [] [] (fun _ => iprop(True))
    m Φ Ψe ci cd dec ui rfl rfl server_isDriverServer) $$ [HSpec]
  · isplitr
    · iexact Hsvc
    isplitr
    · iintro !> %l Hl
      simp only [pbStringValueT, pbStringValue]
      iexact Hl
    isplitr
    · iexact Hh'
    isplitr
    · simp only [srvInterceptorsOk]
      itrivial
    isplitr
    · iintro !> %l -
      itrivial
    isplitr
    · itrivial
    isplitr
    · iapply (BigSepL.bigSepL_nil_intro (PROP := IProp GF) (P := iprop(True)))
      itrivial
    iframe; iframe #
  inext
  iintro %resp %err ⟨-, -, Hres, Herr, #Hse⟩
  iapply HΨ
  iframe Hse
  iframe

/-- **The server's registrations serve the table's `Meta` entry** (`grpcServesEnt`), as
`echo_servesEnt`. -/
theorem meta_servesEnt (wp_Meta : server.Meta.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_Meta_Handler.spec (GF := GF) (hG := hG)) (s : Loc)
    (sics : List GoFunc) (regs sregs : List (GoString × GoFunc × GoInterface))
    (hsr : metaName ∉ sregs.map Prod.fst)
    (hreg : ∀ mh srv, (metaName, mh, srv) ∈ regs →
      mh = functions svc._Driver_Meta_Handler [] ∧
        srv = interface.mkOk (go.GoType.PointerType server.ty) #s) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcServesEnt [] sics regs sregs metaName
        (.unary ⟨reqWire (GF := GF), repWire (GF := GF), metaSpec⟩) := by
  iintro ⟨#Hpkg, #Hsvc⟩
  simp only [grpcServesEnt]
  isplitr
  · ipureintro; exact hsr
  iintro %mh %srv %hin
  obtain ⟨rfl, rfl⟩ := hreg mh srv hin
  iexists (pbStringValueT (GF := GF)), (pbStringValueRT (GF := GF)), (metaSpec (GF := GF))
  isplitr
  · ipureintro
    exact ⟨pbStringValueT_reqReg, pbStringValueRT_repReg, rfl⟩
  iapply meta_runOk wp_Meta wp_H s
  iframe #

end serves

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
