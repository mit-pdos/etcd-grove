/- Lean-first (no Rocq counterpart).

# `Server`'s proof

`grpc.NewServer()` (no options) gives a server being built; the fresh `server` (its mutex over an
empty map and no ids: `isDrvServer`) is registered with `Driver_ServiceDesc` (`svc.drvDescs`);
`net.Listen` at `drvAddr` gives an open listener (`drv_listen`); `Serve` takes the right to serve the
table (`grpcServeTok`'s first form): the registrations serve it (`drv_serves`), their names are
distinct (`drv_nodup`), and every reply is bounded (`drvSvc_repliesBounded`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Server
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.RegisterDriverServer
public import Spec.google_golang_org.grpc.NewServer
public import Spec.google_golang_org.grpc.Server__Serve
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.ServerStart
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : _root_.Perennial.net.FieldAssumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Server.wp_proof
    (wp_NewServer : grpc.NewServer.spec (GF := GF) (hG := hG))
    (wp_Reg : svc.RegisterDriverServer.spec (GF := GF) (hG := hG))
    (wp_Listen : ∀ [HasExt netExt], _root_.Perennial.net.Listen.spec (GF := GF) (hG := hG))
    (wp_Serve : grpc.Server.Serve.spec (GF := GF) (hG := hG))
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
    (wp_HBi : svc._Driver_Bidi_Handler.spec (GF := GF) (hG := hG)) :
    Server.spec (GF := GF) (hG := hG) := by
  intro hX π σ γid
  wp_start as ⟨#Hinv, #Haddr⟩
  have hok : addrOk drvAddr = true := by decide
  ihave #Hsvc : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc $$ []
  · iPkgInit
  ihave #Hd := svc.drvDescs_of_init $$ Hsvc
  icases Hd with ⟨%mds, %sds, #Hdesc, %Hms⟩
  obtain ⟨hm, hs⟩ := Hms
  try wp_auto
  wp_apply (wp_NewServer slice.nil [] []) $$ [] as %gs Hgs
  · isplitr
    · iapply (ownSlice_nil (V := GoInterface) DFrac.discard)
    · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).mpr; iempintro
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w64) go.string go.uint64) as %mref Hm
  try wp_auto
  wp_alloc sptr as Hsrv
  iStructNamed Hsrv
  imod sync.init_Mutex (drvSrvInv γid sptr) ⊤ _ $$ mu [runs Hm] with #Hmu
  · inext
    iunfold drvSrvInv
    iexists mref, ∅, []
    iframe
    isplitr
    · ipureintro
      intro v n h
      simp at h
    · iapply (BigSepL.bigSepL_nil_intro (PROP := IProp GF) (P := iprop(True)))
      itrivial
  ihave #Hs : isDrvServer γid sptr $$ []
  · iunfold isDrvServer
    iframe #
  wp_apply (wp_Reg gs (interface.mkOk (go.GoType.PointerType server.ty) #sptr) [] [] [] [] []
    drvSvcName _ mds sds) $$ [Hgs] as Hgs
  · iframe
    isplitr
    · iunfold grpcDescIs
      iunfold go_etcd_io.etcd.cache.v3.pbDescIs at Hdesc
      iexact Hdesc
    ipureintro
    refine ⟨by simp, ⟨svc.DriverServer.ty, ⟨go.GoType.PointerType server.ty, #sptr⟩, rfl, rfl,
      server_isDriverServer⟩, ?_, ?_⟩
    · have h1 : mds.map (·.MethodName') = (mds.map (fun md => (md.MethodName', (#md.Handler' : val)))).map
          Prod.fst := by simp [List.map_map, Function.comp_def]
      have h2 : sds.map (·.StreamName') = (sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val),
          sd.ServerStreams', sd.ClientStreams'))).map Prod.fst := by
        simp [List.map_map, Function.comp_def]
      unfold descNames
      rw [h1, h2, hm, hs]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      decide
    · intro sd hsd
      have hin := List.mem_map_of_mem (f := fun sd : google_golang_org.grpc.StreamDesc =>
        (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams', sd.ClientStreams')) hsd
      rw [hs] at hin
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, _root_.or_false] at hin
      rcases hin with ⟨-, -, h1, -⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, h1, -⟩
      · exact Or.inr h1
      · exact Or.inl h2
      · exact Or.inr h1
  try wp_auto
  wp_apply (drv_listen wp_Listen drvAddr hok) $$ [] as %l %err Hl
  · iframe #
  icases Hl with (⟨%Herr, Hlo⟩ | %Herr)
  · subst Herr
    try wp_auto
    wp_apply (wp_Serve gs l drvAddr (drvSvc γid)) $$ [Hgs Hlo] as %err2 -
    · unfold grpcServeTok
      iexists ⟨[], [], [] ++ descRegs drvSvcName mds (interface.mkOk (go.GoType.PointerType server.ty) #sptr),
        [] ++ descSRegs drvSvcName sds (interface.mkOk (go.GoType.PointerType server.ty) #sptr)⟩, [] ++ [drvSvcName]
      isplitl [Hgs Hlo]
      · ileft
        isplitl [Hgs]
        · iexact Hgs
        · iexact Hlo
      isplitr
      · ipureintro
        simp only [grpcSrvNodup, List.nil_append]
        exact drv_nodup _ hm hs
      isplitr
      · iright
        iapply drvSvc_repliesBounded
      isplitr
      · iexists hX, π, σ
        iexact Haddr
      simp only [List.nil_append]
      iapply (drv_serves wp_Echo wp_Fail wp_Meta wp_SS wp_CS wp_Bi wp_HE wp_HF wp_HM wp_HSS wp_HCS
        wp_HBi γid sptr hm hs)
      iframe #
    try wp_auto
    iapply HΦ
    itrivial
  · cases err with
    | nil => exact absurd rfl Herr
    | ok e =>
      try wp_auto
      iapply HΦ
      itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
