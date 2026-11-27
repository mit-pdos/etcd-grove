module

public import Spec.google_golang_org.grpc.health.grpc_health_v1.RegisterHealthServer
public import Spec.google_golang_org.grpc.Server__RegisterService

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.health.grpc_health_v1.Assumptions]
variable [package_sem' : google_golang_org.grpc.health.Assumptions]

/-- The method names of `Health_ServiceDesc` (`healthDescs`). -/
private theorem health_mnames (mds : List google_golang_org.grpc.MethodDesc)
    (h : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) =
      [(go!"Check", @! google_golang_org.grpc.health.grpc_health_v1._Health_Check_Handler),
       (go!"List", @! google_golang_org.grpc.health.grpc_health_v1._Health_List_Handler)]) :
    mds.map (·.MethodName') = [go!"Check", go!"List"] := by
  have := congrArg (List.map Prod.fst) h
  simpa [List.map_map, Function.comp_def] using this

/-- The stream names and flags of `Health_ServiceDesc` (`healthDescs`). -/
private theorem health_snames (sds : List google_golang_org.grpc.StreamDesc)
    (h : sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams', sd.ClientStreams')) =
      [(go!"Watch", @! google_golang_org.grpc.health.grpc_health_v1._Health_Watch_Handler, true, false)]) :
    sds.map (·.StreamName') = [go!"Watch"] ∧ ∀ sd ∈ sds, sd.ServerStreams' = true := by
  refine ⟨?_, ?_⟩
  · have := congrArg (List.map Prod.fst) h
    simpa [List.map_map, Function.comp_def] using this
  · intro sd hsd
    have hm := List.mem_map_of_mem (f := fun sd : google_golang_org.grpc.StreamDesc =>
      (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams', sd.ClientStreams')) hsd
    rw [h] at hm
    simp only [List.mem_singleton] at hm
    exact (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hm).2).2).1

/-- The generated `RegisterHealthServer` (`health_grpc.pb.go`; until 2026-11-26 a trust-boundary
axiom): `*health.Server` embeds `UnimplementedHealthServer` by value, so the type assertion to
`interface{ testEmbeddedByValue() }` succeeds and the (empty) method runs on the embedded field;
then `s.RegisterService(&Health_ServiceDesc, srv)`, with the descriptor of the package's fact
(`healthDescs`): `Check` and `List`, the server stream `Watch`. -/
theorem grpc_health_v1.RegisterHealthServer.wp_proof
    (wp_RegisterService : grpc.Server.RegisterService.spec (GF := GF) (hG := hG)) :
    grpc_health_v1.RegisterHealthServer.spec (GF := GF) (hG := hG) := by
  intro gs hs ics sics svcs regs sregs
  wp_start as ⟨Hs, #Hhs, %Hsn⟩
  ihave #Hd : (google_golang_org.grpc.health.grpc_health_v1.healthDescs : IProp GF) $$ []
  · iapply google_golang_org.grpc.health.grpc_health_v1.healthDescs_of_init $$ Hpkg
  icases Hd with ⟨%mds, %sds, #Hd, %Hmds, %Hsds⟩
  iunfold grpcHealthSrv at Hhs
  icases Hhs with ⟨%mS, %mU, %uh, #Huh, -⟩
  have hmn := health_mnames mds Hmds
  obtain ⟨hsn, hfl⟩ := health_snames sds Hsds
  -- `*health.Server` has `testEmbeddedByValue` (promoted from its embedded `UnimplementedHealthServer`)
  have hte : go.typeSetContains (go.GoType.PointerType google_golang_org.grpc.health.Server.ty)
      (go.GoType.InterfaceType [go.InterfaceElem.MethodElem
        go!"google.golang.org/grpc/health/grpc_health_v1.testEmbeddedByValue"
        (go.signature.Signature [] false [])]) = true := by go_type_set
  wp_auto
  simp only [hte]
  wp_auto
  -- `testEmbeddedByValue` on the embedded field: loads it, runs the empty method
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  wp_apply (wp_RegisterService gs _ (interface.mkOk (go.GoType.PointerType
      google_golang_org.grpc.health.Server.ty) #hs) ics sics svcs regs sregs
      go!"grpc.health.v1.Health" (interface.mkOk (go.GoType.PointerType
        google_golang_org.grpc.health.grpc_health_v1.HealthServer.ty) #(null : Loc)) mds sds) $$ [Hs] as Hs
  · iframe Hs
    isplitl []
    · iunfold grpcDescIs; iunfold go_etcd_io.etcd.cache.v3.pbDescIs at Hd; iexact Hd
    ipureintro
    refine ⟨Hsn, ⟨google_golang_org.grpc.health.grpc_health_v1.HealthServer.ty, ⟨_, _⟩, rfl, rfl, ?_⟩,
      ?_, fun sd hsd => Or.inr (hfl sd hsd)⟩
    · go_type_set
    · simp only [descNames, hmn, hsn]; decide
  iapply HΦ
  iexists _, _
  iframe Hs
  ipureintro
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨md, -, rfl⟩ := List.mem_map.1 hx
      exact ⟨md.MethodName', by simp [grpcFullName]⟩
    · obtain ⟨sd, -, rfl⟩ := List.mem_map.1 hx
      exact ⟨sd.StreamName', by simp [grpcFullName]⟩
  · rw [List.map_append, descRegs_names, descSRegs_names, hmn, hsn]
    decide

end proof

end EtcdGrove
end Perennial
