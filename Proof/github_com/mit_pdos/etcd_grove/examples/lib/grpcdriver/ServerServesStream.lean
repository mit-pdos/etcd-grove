/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the server serves the table's stream entries

From the stream methods' specs (`server.{ServerStream,ClientStream,Bidi}.spec`) and the generated
stream handlers' (`svc._Driver_*_Handler.spec`), taken as hypotheses: each method meets its handler's
contract (`svc.ssMethodOk`, `svc.strmMethodOk`) at the specification `drvStrmSpec dn` (the content
`Dn` the transport picks holds of the entry's `dn`); each generated handler on the server `s` meets it
as a run (`grpcStreamRunOk`, no stream interceptors); so `s`'s registrations serve the table's stream
entries (`grpcServesEnt`), with the identity conversions.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__ServerStream
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__ClientStream
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Bidi
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_ServerStream_Handler
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_ClientStream_Handler
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_Bidi_Handler
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.ServerServes

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

/-- **A stream's handler specification**: the content `Dn` the transport picks holds of the entry's
`dn`. -/
def drvStrmSpec (dn : GrpcMd → StreamNames → Nat → (strmMsg (GF := GF)).M → IProp GF) :
    GrpcMd → StreamSpec (strmMsg (GF := GF)) :=
  fun md γ Dn => iprop(□ ∀ (j : Nat) (m : (strmMsg (GF := GF)).M), dn md γ j m -∗ Dn j m)

instance drvStrmSpec_persistent (dn : GrpcMd → StreamNames → Nat → (strmMsg (GF := GF)).M → IProp GF)
    (md : GrpcMd) (γ : StreamNames) (Dn : Nat → (strmMsg (GF := GF)).M → IProp GF) :
    Persistent (drvStrmSpec dn md γ Dn) := by
  unfold drvStrmSpec; infer_instance

/-- `drvStrmSpec dn` holds at `dn`. -/
theorem drvStrmSpec_self (dn : GrpcMd → StreamNames → Nat → (strmMsg (GF := GF)).M → IProp GF) :
    ⊢ □ ∀ md γ, drvStrmSpec dn md γ (dn md γ) := by
  iintro !> %md %γ
  unfold drvStrmSpec
  iintro !> %j %m H
  iexact H

/-- The table's stream entries. -/
theorem drvSvc_serverStream (γid : GName) :
    drvSvc (GF := GF) γid serverStreamName =
      some (.stream ⟨strmWire (GF := GF), strmWire (GF := GF), ssUp, ssDn, strmSpec⟩) := by
  unfold drvSvc
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem drvSvc_clientStream (γid : GName) :
    drvSvc (GF := GF) γid clientStreamName =
      some (.stream ⟨strmWire (GF := GF), strmWire (GF := GF), csUp, csDn, strmSpec⟩) := by
  unfold drvSvc
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem drvSvc_bidi (γid : GName) :
    drvSvc (GF := GF) γid bidiName =
      some (.stream ⟨strmWire (GF := GF), strmWire (GF := GF), biUp, biDn, strmSpec⟩) := by
  unfold drvSvc
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]

/-- **`ServerStream` meets its handler's contract** (`ssMethodOk`). -/
theorem serverStream_methodOk (wp_SS : server.ServerStream.spec (GF := GF) (hG := hG)) (s : Loc)
    (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ⊢
      svc.ssMethodOk (Req := strmMsg (GF := GF)) (Rep := strmMsg (GF := GF))
        (s @!! go.GoType.PointerType server.ty @!! go!"ServerStream") S ssUp (drvStrmSpec ssDn) := by
  iintro #Hpkg
  unfold svc.ssMethodOk
  iintro !> %γ %Dn %ci %cd %st %r %v %Φ HSpec HS #Hst Hr HRt HSt HΦ
  iunfold grpcStreamSpecAt at HSpec
  icases HSpec with ⟨%md, -, #Hdn⟩
  iapply (wp_SS s r v st γ Dn ci cd md) $$ [Hr HRt HSt]
  · iframe; iframe #
  inext
  iintro %err #Herr
  iapply HΦ $$ Herr HS

/-- **`ClientStream` meets its handler's contract** (`strmMethodOk`). -/
theorem clientStream_methodOk (wp_M : server.ClientStream.spec (GF := GF) (hG := hG)) (s : Loc) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ⊢
      svc.strmMethodOk (Req := strmMsg (GF := GF)) (Rep := strmMsg (GF := GF))
        (s @!! go.GoType.PointerType server.ty @!! go!"ClientStream") S csUp (drvStrmSpec csDn) := by
  iintro #Hpkg
  unfold svc.strmMethodOk
  iintro !> %γ %Dn %ci %cd %st %Φ HSpec HS #Hst #Hsac HRt HSt HΦ
  iunfold grpcStreamSpecAt at HSpec
  icases HSpec with ⟨%md, -, #Hdn⟩
  iapply (wp_M s st γ Dn ci cd md) $$ [HRt HSt]
  · iframe; iframe #
  inext
  iintro %err #Herr
  iapply HΦ $$ Herr HS

/-- **`Bidi` meets its handler's contract** (`strmMethodOk`). -/
theorem bidi_methodOk (wp_M : server.Bidi.spec (GF := GF) (hG := hG)) (s : Loc) (S : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ⊢
      svc.strmMethodOk (Req := strmMsg (GF := GF)) (Rep := strmMsg (GF := GF))
        (s @!! go.GoType.PointerType server.ty @!! go!"Bidi") S biUp (drvStrmSpec biDn) := by
  iintro #Hpkg
  unfold svc.strmMethodOk
  iintro !> %γ %Dn %ci %cd %st %Φ HSpec HS #Hst #Hsac HRt HSt HΦ
  iunfold grpcStreamSpecAt at HSpec
  icases HSpec with ⟨%md, -, #Hdn⟩
  iapply (wp_M s st γ Dn ci cd md) $$ [HRt HSt]
  · iframe; iframe #
  inext
  iintro %err #Herr
  iapply HΦ $$ Herr HS

/-- **The generated `ServerStream` handler on the server `s` meets its specification as a run** (no stream
interceptors). -/
theorem serverStream_runOk (wp_M : server.ServerStream.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_ServerStream_Handler.spec (GF := GF) (hG := hG)) (s : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcStreamRunOk (Req := strmMsg (GF := GF)) (Rep := strmMsg (GF := GF))
        #(functions svc._Driver_ServerStream_Handler []) (interface.mkOk (go.GoType.PointerType server.ty) #s)
        [] ssUp (drvStrmSpec ssDn) := by
  iintro ⟨#Hpkg, #Hsvc⟩
  ihave #Hm := serverStream_methodOk wp_M s (threadTok (GF := GF)) $$ Hpkg
  unfold grpcStreamRunOk
  iintro !> %γ %Dn %ci %cd %st %info HSpec HT Hlc #Hraw HRt HSt HAux #Hinfo
  simp only [srvStreamChainWP]
  iintro -
  ihave #HrawW := srvRawStreamIsW_of_raw _ _ _ _ _ _ _ _ $$ Hraw
  iapply (wp_H ssUp (drvStrmSpec ssDn) ⟨go.GoType.PointerType server.ty, #s⟩ threadTok γ Dn ci cd st
    server_isDriverServer) $$ [HSpec HT HRt HSt]
  · iframe; iframe #
  inext
  iintro %err ⟨#Herr, HT⟩
  isplitr
  · itrivial
  iexists err
  iframe
  iframe #
  ipureintro; rfl

/-- **The generated `ClientStream` handler on the server `s` meets its specification as a run** (no stream
interceptors). -/
theorem clientStream_runOk (wp_M : server.ClientStream.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_ClientStream_Handler.spec (GF := GF) (hG := hG)) (s : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcStreamRunOk (Req := strmMsg (GF := GF)) (Rep := strmMsg (GF := GF))
        #(functions svc._Driver_ClientStream_Handler []) (interface.mkOk (go.GoType.PointerType server.ty) #s)
        [] csUp (drvStrmSpec csDn) := by
  iintro ⟨#Hpkg, #Hsvc⟩
  ihave #Hm := clientStream_methodOk wp_M s (threadTok (GF := GF)) $$ Hpkg
  unfold grpcStreamRunOk
  iintro !> %γ %Dn %ci %cd %st %info HSpec HT Hlc #Hraw HRt HSt HAux #Hinfo
  simp only [srvStreamChainWP]
  iintro -
  ihave #HrawW := srvRawStreamIsW_of_raw _ _ _ _ _ _ _ _ $$ Hraw
  iapply (wp_H csUp (drvStrmSpec csDn) ⟨go.GoType.PointerType server.ty, #s⟩ threadTok γ Dn ci cd st
    server_isDriverServer) $$ [HSpec HT HRt HSt]
  · iframe; iframe #
  inext
  iintro %err ⟨#Herr, HT⟩
  isplitr
  · itrivial
  iexists err
  iframe
  iframe #
  ipureintro; rfl

/-- **The generated `Bidi` handler on the server `s` meets its specification as a run** (no stream
interceptors). -/
theorem bidi_runOk (wp_M : server.Bidi.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_Bidi_Handler.spec (GF := GF) (hG := hG)) (s : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcStreamRunOk (Req := strmMsg (GF := GF)) (Rep := strmMsg (GF := GF))
        #(functions svc._Driver_Bidi_Handler []) (interface.mkOk (go.GoType.PointerType server.ty) #s)
        [] biUp (drvStrmSpec biDn) := by
  iintro ⟨#Hpkg, #Hsvc⟩
  ihave #Hm := bidi_methodOk wp_M s (threadTok (GF := GF)) $$ Hpkg
  unfold grpcStreamRunOk
  iintro !> %γ %Dn %ci %cd %st %info HSpec HT Hlc #Hraw HRt HSt HAux #Hinfo
  simp only [srvStreamChainWP]
  iintro -
  ihave #HrawW := srvRawStreamIsW_of_raw _ _ _ _ _ _ _ _ $$ Hraw
  iapply (wp_H biUp (drvStrmSpec biDn) ⟨go.GoType.PointerType server.ty, #s⟩ threadTok γ Dn ci cd st
    server_isDriverServer) $$ [HSpec HT HRt HSt]
  · iframe; iframe #
  inext
  iintro %err ⟨#Herr, HT⟩
  isplitr
  · itrivial
  iexists err
  iframe
  iframe #
  ipureintro; rfl

/-- **The server's registrations serve the table's `ServerStream` entry** (`grpcServesEnt`): for
registrations that put under `serverStreamName` the generated handler on `s` and no unary method. -/
theorem serverStream_servesEnt (wp_M : server.ServerStream.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_ServerStream_Handler.spec (GF := GF) (hG := hG)) (s : Loc)
    (regs sregs : List (GoString × GoFunc × GoInterface))
    (hr : serverStreamName ∉ regs.map Prod.fst)
    (hreg : ∀ mh srv, (serverStreamName, mh, srv) ∈ sregs →
      (#mh : val) = (@! svc._Driver_ServerStream_Handler) ∧
        srv = interface.mkOk (go.GoType.PointerType server.ty) #s) (ics : List GoFunc) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcServesEnt ics [] regs sregs serverStreamName
        (.stream ⟨strmWire (GF := GF), strmWire (GF := GF), ssUp, ssDn, strmSpec⟩) := by
  iintro ⟨#Hpkg, #Hsvc⟩
  simp only [grpcServesEnt]
  isplitr
  · ipureintro; exact hr
  iintro %mh %srv %hin
  obtain ⟨hmh, rfl⟩ := hreg mh srv hin
  rw [hmh]
  iexists (pbStringValueST (GF := GF)), (pbStringValueST (GF := GF)), ssUp, ssDn, strmSpec, ssUp,
    drvStrmSpec ssDn, ssDn
  isplitr
  · ipureintro
    exact ⟨pbStringValueST_reqReg, pbStringValueST_repReg, rfl⟩
  isplitr
  · iintro !> %i %m H
    iexact H
  isplitr
  · iapply drvStrmSpec_self
  isplitr
  · iintro !> %md %γ %j %m H
    iexact H
  iapply serverStream_runOk wp_M wp_H s
  iframe #

/-- **The server's registrations serve the table's `ClientStream` entry** (`grpcServesEnt`): for
registrations that put under `clientStreamName` the generated handler on `s` and no unary method. -/
theorem clientStream_servesEnt (wp_M : server.ClientStream.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_ClientStream_Handler.spec (GF := GF) (hG := hG)) (s : Loc)
    (regs sregs : List (GoString × GoFunc × GoInterface))
    (hr : clientStreamName ∉ regs.map Prod.fst)
    (hreg : ∀ mh srv, (clientStreamName, mh, srv) ∈ sregs →
      (#mh : val) = (@! svc._Driver_ClientStream_Handler) ∧
        srv = interface.mkOk (go.GoType.PointerType server.ty) #s) (ics : List GoFunc) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcServesEnt ics [] regs sregs clientStreamName
        (.stream ⟨strmWire (GF := GF), strmWire (GF := GF), csUp, csDn, strmSpec⟩) := by
  iintro ⟨#Hpkg, #Hsvc⟩
  simp only [grpcServesEnt]
  isplitr
  · ipureintro; exact hr
  iintro %mh %srv %hin
  obtain ⟨hmh, rfl⟩ := hreg mh srv hin
  rw [hmh]
  iexists (pbStringValueST (GF := GF)), (pbStringValueST (GF := GF)), csUp, csDn, strmSpec, csUp,
    drvStrmSpec csDn, csDn
  isplitr
  · ipureintro
    exact ⟨pbStringValueST_reqReg, pbStringValueST_repReg, rfl⟩
  isplitr
  · iintro !> %i %m H
    iexact H
  isplitr
  · iapply drvStrmSpec_self
  isplitr
  · iintro !> %md %γ %j %m H
    iexact H
  iapply clientStream_runOk wp_M wp_H s
  iframe #

/-- **The server's registrations serve the table's `Bidi` entry** (`grpcServesEnt`): for
registrations that put under `bidiName` the generated handler on `s` and no unary method. -/
theorem bidi_servesEnt (wp_M : server.Bidi.spec (GF := GF) (hG := hG))
    (wp_H : svc._Driver_Bidi_Handler.spec (GF := GF) (hG := hG)) (s : Loc)
    (regs sregs : List (GoString × GoFunc × GoInterface))
    (hr : bidiName ∉ regs.map Prod.fst)
    (hreg : ∀ mh srv, (bidiName, mh, srv) ∈ sregs →
      (#mh : val) = (@! svc._Driver_Bidi_Handler) ∧
        srv = interface.mkOk (go.GoType.PointerType server.ty) #s) (ics : List GoFunc) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcServesEnt ics [] regs sregs bidiName
        (.stream ⟨strmWire (GF := GF), strmWire (GF := GF), biUp, biDn, strmSpec⟩) := by
  iintro ⟨#Hpkg, #Hsvc⟩
  simp only [grpcServesEnt]
  isplitr
  · ipureintro; exact hr
  iintro %mh %srv %hin
  obtain ⟨hmh, rfl⟩ := hreg mh srv hin
  rw [hmh]
  iexists (pbStringValueST (GF := GF)), (pbStringValueST (GF := GF)), biUp, biDn, strmSpec, biUp,
    drvStrmSpec biDn, biDn
  isplitr
  · ipureintro
    exact ⟨pbStringValueST_reqReg, pbStringValueST_repReg, rfl⟩
  isplitr
  · iintro !> %i %m H
    iexact H
  isplitr
  · iapply drvStrmSpec_self
  isplitr
  · iintro !> %md %γ %j %m H
    iexact H
  iapply bidi_runOk wp_M wp_H s
  iframe #

/-- A unary entry of the table's: its registered reply model bounds every reply. -/
theorem drv_unaryBound (Spec : GrpcSpecMd (GF := GF) (pbStringValueT (GF := GF)).toProtoMsg
      (pbStringValueRT (GF := GF)).toProtoMsg) :
    ⊢ ∀ Rep : ProtoMsgT GF,
      ⌜grpcRepModelOf GF (⟨reqWire (GF := GF), repWire (GF := GF), Spec⟩ : GrpcEntry GF).Wp.ty =
        some Rep⌝ -∗ □ ∀ (l : Loc) (m : Rep.M), Rep.send l m -∗ ⌜Rep.wireLen m < grpcMsgMax⌝ := by
  iintro %Rep %hR
  obtain rfl : Rep = pbStringValueRT (GF := GF) :=
    (Option.some.inj ((pbStringValueRT_repReg (GF := GF)).symm.trans hR)).symm
  iintro !> %l %m Hs
  isimp only [pbStringValueRT, pbStringValueR, stringValueSend, stringValueSendB] at Hs
  icases Hs with ⟨%v, -, %Hv⟩
  ipureintro
  have hb : stringValueMax + 11 < grpcMsgMax := by decide
  simp only [pbStringValueRT, pbStringValueR, stringValueWireLen]
  omega

/-- A stream entry of the table's: its registered reply model bounds every reply. -/
theorem drv_streamBound (up : Nat → (strmMsg (GF := GF)).M → IProp GF)
    (dn : GrpcMd → StreamNames → Nat → (strmMsg (GF := GF)).M → IProp GF) :
    ⊢ ∀ Rep : StreamMsgT GF,
      ⌜streamRepModelOf GF (⟨strmWire (GF := GF), strmWire (GF := GF), up, dn, strmSpec⟩ :
        GrpcStreamEntry GF).Wp.ty = some Rep⌝ -∗
      □ ∀ (l : Loc) (m : Rep.M), Rep.send l m -∗ ⌜Rep.wireLen m < grpcMsgMax⌝ := by
  iintro %Rep %hR
  obtain rfl : Rep = pbStringValueST (GF := GF) :=
    (Option.some.inj ((pbStringValueST_repReg (GF := GF)).symm.trans hR)).symm
  iintro !> %l %m Hs
  isimp only [pbStringValueST, pbStringValueS, stringValueSend, stringValueSendB] at Hs
  icases Hs with ⟨%v, -, %Hv⟩
  ipureintro
  have hb : stringValueMax + 11 < grpcMsgMax := by decide
  simp only [pbStringValueST, pbStringValueS, stringValueWireLen]
  omega

/-- **Every reply the driver's table lets a handler send marshals** (`grpcRepliesBounded`): every
entry's reply is a `StringValue`, below `stringValueMax`. -/
theorem drvSvc_repliesBounded (γid : GName) : ⊢ grpcRepliesBounded (drvSvc (GF := GF) γid) := by
  unfold grpcRepliesBounded
  iintro !> %name %ent %he
  by_cases h1 : name = echoName
  · subst h1; rw [drvSvc_echo] at he; cases he; iapply drv_unaryBound
  by_cases h2 : name = failName
  · subst h2; rw [drvSvc_fail] at he; cases he; iapply drv_unaryBound
  by_cases h3 : name = metaName
  · subst h3; rw [drvSvc_meta] at he; cases he; iapply drv_unaryBound
  by_cases h4 : name = serverStreamName
  · subst h4; rw [drvSvc_serverStream] at he; cases he; iapply drv_streamBound
  by_cases h5 : name = clientStreamName
  · subst h5; rw [drvSvc_clientStream] at he; cases he; iapply drv_streamBound
  by_cases h6 : name = bidiName
  · subst h6; rw [drvSvc_bidi] at he; cases he; iapply drv_streamBound
  exfalso
  unfold drvSvc at he
  simp [h1, h2, h3, h4, h5, h6] at he

end serves

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
