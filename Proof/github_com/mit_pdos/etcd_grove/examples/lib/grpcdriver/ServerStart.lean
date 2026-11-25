/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the server's registrations serve the driver's table

`RegisterService` with `Driver_ServiceDesc` (`svc.drvDescs`: its methods and streams exactly) registers,
for the service value `&server{...}`, each of the table's names (`drvSvc γid`) with its generated
handler (`drv_regs_mem`, `drv_sregs_mem`), the full names jointly distinct (`drv_nodup`). So the server
serves the table (`drv_serves`, from each entry's `*_servesEnt`, over the methods' and the generated
handlers' specs, taken as hypotheses).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.ServerServesStream

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

/-- The driver's service name. -/
abbrev drvSvcName : GoString := go!"grpcdriver.Driver"

section lists
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- The methods `Driver_ServiceDesc` lists (`svc.drvDescs`'s). -/
abbrev drvMethods : List (GoString × val) :=
  [(go!"Echo", @! svc._Driver_Echo_Handler), (go!"Fail", @! svc._Driver_Fail_Handler),
   (go!"Meta", @! svc._Driver_Meta_Handler)]

/-- The streams `Driver_ServiceDesc` lists (`svc.drvDescs`'s). -/
abbrev drvStreams : List (GoString × val × Bool × Bool) :=
  [(go!"ServerStream", @! svc._Driver_ServerStream_Handler, true, false),
   (go!"ClientStream", @! svc._Driver_ClientStream_Handler, false, true),
   (go!"Bidi", @! svc._Driver_Bidi_Handler, true, true)]

/-- **A registered unary method** is one of the table's three, with its generated handler. -/
theorem drv_regs_mem {mds : List google_golang_org.grpc.MethodDesc} {ss : GoInterface}
    (hm : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = drvMethods)
    {n : GoString} {mh : GoFunc} {srv : GoInterface} (h : (n, mh, srv) ∈ descRegs drvSvcName mds ss) :
    srv = ss ∧ ((n = echoName ∧ (#mh : val) = @! svc._Driver_Echo_Handler) ∨
      (n = failName ∧ (#mh : val) = @! svc._Driver_Fail_Handler) ∨
      (n = metaName ∧ (#mh : val) = @! svc._Driver_Meta_Handler)) := by
  unfold descRegs at h
  obtain ⟨md, hmd, heq⟩ := List.mem_map.1 h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hin := List.mem_map_of_mem (f := fun md : google_golang_org.grpc.MethodDesc =>
    (md.MethodName', (#md.Handler' : val))) hmd
  rw [hm] at hin
  simp only [drvMethods, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hin
  refine ⟨rfl, ?_⟩
  rcases hin with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨by rw [grpcFullName, h1]; decide, h2⟩
  · right; left; exact ⟨by rw [grpcFullName, h1]; decide, h2⟩
  · right; right; exact ⟨by rw [grpcFullName, h1]; decide, h2⟩

/-- **A registered stream** is one of the table's three, with its generated handler. -/
theorem drv_sregs_mem {sds : List google_golang_org.grpc.StreamDesc} {ss : GoInterface}
    (hs : sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams',
      sd.ClientStreams')) = drvStreams)
    {n : GoString} {mh : GoFunc} {srv : GoInterface} (h : (n, mh, srv) ∈ descSRegs drvSvcName sds ss) :
    srv = ss ∧ ((n = serverStreamName ∧ (#mh : val) = @! svc._Driver_ServerStream_Handler) ∨
      (n = clientStreamName ∧ (#mh : val) = @! svc._Driver_ClientStream_Handler) ∨
      (n = bidiName ∧ (#mh : val) = @! svc._Driver_Bidi_Handler)) := by
  unfold descSRegs at h
  obtain ⟨sd, hsd, heq⟩ := List.mem_map.1 h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hin := List.mem_map_of_mem (f := fun sd : google_golang_org.grpc.StreamDesc =>
    (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams', sd.ClientStreams')) hsd
  rw [hs] at hin
  simp only [drvStreams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hin
  refine ⟨rfl, ?_⟩
  rcases hin with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · left; exact ⟨by rw [grpcFullName, h1]; decide, h2⟩
  · right; left; exact ⟨by rw [grpcFullName, h1]; decide, h2⟩
  · right; right; exact ⟨by rw [grpcFullName, h1]; decide, h2⟩

/-- The registered unary methods' names. -/
theorem drv_regs_names {mds : List google_golang_org.grpc.MethodDesc} (ss : GoInterface)
    (hm : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = drvMethods) :
    (descRegs drvSvcName mds ss).map Prod.fst = [echoName, failName, metaName] := by
  have h1 : (descRegs drvSvcName mds ss).map Prod.fst =
      (mds.map (fun md => (md.MethodName', (#md.Handler' : val)))).map
        (fun p => grpcFullName drvSvcName p.1) := by
    simp [descRegs, List.map_map, Function.comp_def]
  rw [h1, hm]
  simp only [drvMethods, List.map_cons, List.map_nil]
  decide

/-- The registered streams' names. -/
theorem drv_sregs_names {sds : List google_golang_org.grpc.StreamDesc} (ss : GoInterface)
    (hs : sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams',
      sd.ClientStreams')) = drvStreams) :
    (descSRegs drvSvcName sds ss).map Prod.fst = [serverStreamName, clientStreamName, bidiName] := by
  have h1 : (descSRegs drvSvcName sds ss).map Prod.fst =
      (sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams',
        sd.ClientStreams'))).map (fun p => grpcFullName drvSvcName p.1) := by
    simp [descSRegs, List.map_map, Function.comp_def]
  rw [h1, hs]
  simp only [drvStreams, List.map_cons, List.map_nil]
  decide

/-- **The registrations' full names are jointly distinct.** -/
theorem drv_nodup {mds : List google_golang_org.grpc.MethodDesc}
    {sds : List google_golang_org.grpc.StreamDesc} (ss : GoInterface)
    (hm : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = drvMethods)
    (hs : sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams',
      sd.ClientStreams')) = drvStreams) :
    ((descRegs drvSvcName mds ss ++ descSRegs drvSvcName sds ss).map Prod.fst).Nodup := by
  rw [List.map_append, drv_regs_names ss hm, drv_sregs_names ss hs]
  decide

end lists

section serves
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- **The server's registrations serve the driver's table** (no interceptors). -/
theorem drv_serves
    (wp_Echo : server.Echo.spec (GF := GF) (hG := hG)) (wp_Fail : server.Fail.spec (GF := GF) (hG := hG))
    (wp_Meta : server.Meta.spec (GF := GF) (hG := hG))
    (wp_SS : server.ServerStream.spec (GF := GF) (hG := hG))
    (wp_CS : server.ClientStream.spec (GF := GF) (hG := hG))
    (wp_Bi : server.Bidi.spec (GF := GF) (hG := hG))
    (wp_HE : svc._Driver_Echo_Handler.spec (GF := GF) (hG := hG))
    (wp_HF : svc._Driver_Fail_Handler.spec (GF := GF) (hG := hG))
    (wp_HM : svc._Driver_Meta_Handler.spec (GF := GF) (hG := hG))
    (wp_HSS : svc._Driver_ServerStream_Handler.spec (GF := GF) (hG := hG))
    (wp_HCS : svc._Driver_ClientStream_Handler.spec (GF := GF) (hG := hG))
    (wp_HBi : svc._Driver_Bidi_Handler.spec (GF := GF) (hG := hG))
    (γid : GName) (s : Loc) {mds : List google_golang_org.grpc.MethodDesc}
    {sds : List google_golang_org.grpc.StreamDesc}
    (hm : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = drvMethods)
    (hs : sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams',
      sd.ClientStreams')) = drvStreams) :
    isDrvServer γid s ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      grpcServes (drvSvc γid) [] []
        (descRegs drvSvcName mds (interface.mkOk (go.GoType.PointerType server.ty) #s))
        (descSRegs drvSvcName sds (interface.mkOk (go.GoType.PointerType server.ty) #s)) := by
  iintro ⟨#Hs, #Hsvc⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver $$ []
  · iunfold isDrvServer at Hs
    icases Hs with ⟨#Hp, -⟩
    iexact Hp
  have hrn := drv_regs_names (interface.mkOk (go.GoType.PointerType server.ty) #s) hm
  have hsn := drv_sregs_names (interface.mkOk (go.GoType.PointerType server.ty) #s) hs
  unfold grpcServes
  iintro !> %name %ent %he
  by_cases h1 : name = echoName
  · subst h1; rw [drvSvc_echo] at he; cases he
    iapply (echo_servesEnt wp_Echo wp_HE γid s [] _ _ (by rw [hsn]; decide)
      (fun mh srv hin => by
        obtain ⟨hsrv, hc⟩ := drv_regs_mem hm hin
        rcases hc with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact ⟨h, hsrv⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)))
    iframe #
  by_cases h2 : name = failName
  · subst h2; rw [drvSvc_fail] at he; cases he
    iapply (fail_servesEnt wp_Fail wp_HF s [] _ _ (by rw [hsn]; decide)
      (fun mh srv hin => by
        obtain ⟨hsrv, hc⟩ := drv_regs_mem hm hin
        rcases hc with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd h (by decide)
        · exact ⟨h, hsrv⟩
        · exact absurd h (by decide)))
    iframe #
  by_cases h3 : name = metaName
  · subst h3; rw [drvSvc_meta] at he; cases he
    iapply (meta_servesEnt wp_Meta wp_HM s [] _ _ (by rw [hsn]; decide)
      (fun mh srv hin => by
        obtain ⟨hsrv, hc⟩ := drv_regs_mem hm hin
        rcases hc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact ⟨h, hsrv⟩))
    iframe #
  by_cases h4 : name = serverStreamName
  · subst h4; rw [drvSvc_serverStream] at he; cases he
    iapply (serverStream_servesEnt wp_SS wp_HSS s _ _ (by rw [hrn]; decide)
      (fun mh srv hin => by
        obtain ⟨hsrv, hc⟩ := drv_sregs_mem hs hin
        rcases hc with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact ⟨h, hsrv⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)) [])
    iframe #
  by_cases h5 : name = clientStreamName
  · subst h5; rw [drvSvc_clientStream] at he; cases he
    iapply (clientStream_servesEnt wp_CS wp_HCS s _ _ (by rw [hrn]; decide)
      (fun mh srv hin => by
        obtain ⟨hsrv, hc⟩ := drv_sregs_mem hs hin
        rcases hc with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd h (by decide)
        · exact ⟨h, hsrv⟩
        · exact absurd h (by decide)) [])
    iframe #
  by_cases h6 : name = bidiName
  · subst h6; rw [drvSvc_bidi] at he; cases he
    iapply (bidi_servesEnt wp_Bi wp_HBi s _ _ (by rw [hrn]; decide)
      (fun mh srv hin => by
        obtain ⟨hsrv, hc⟩ := drv_sregs_mem hs hin
        rcases hc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact ⟨h, hsrv⟩) [])
    iframe #
  exfalso
  unfold drvSvc at he
  simp [h1, h2, h3, h4, h5, h6] at he

end serves

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
