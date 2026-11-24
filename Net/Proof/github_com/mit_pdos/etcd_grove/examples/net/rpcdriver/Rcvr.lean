/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: the receivers

The generated `rpcReceiver` (`examples/net/rpcdriver/rpc_model_gen.go`) on a `*service.Svc` gives a
`*Receiver` meeting Net's `rcvrIs` for the service's spec `echoSvc γid` (`svcRcv_holds`), and on a
`*service.NoMethods` one meeting `rcvrNone` (`noMethodsRcv_holds`). The method `Echo`
(`methodOk`): `NewArg()` allocates the zero `service.Args`, whose decoding of a deposit's argument
bytes `encArgs id data fail` is `CodecLaws.decA_Args` (Net's `argDec`); the call obligation:
`NewReply()`, then `Call`, which calls `Svc.Echo` (its spec a hypothesis, `Svc.Echo.spec`) with the
deposit's token of `id` (the decoded values are the deposit's: `encArgs_inj`), whose reply
`CodecLaws.enc_Reply` encodes into the deposit's success answer `encReply id data 1`, or whose error
is the deposit's `fail`. As epaxos's `NetRpc/Bindings.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.CodecProof
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.Svc__Echo

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.wire

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

/-- The generated `Method` of the functions named `na`, `nr`, `cl`. -/
abbrev mOf [GooseExts] [GoSemanticsFunctions] [GoGlobalContext] (na nr cl : GoString) :
    net.rpc.Method :=
  net.rpc.Method.mk (functions na []) (functions nr []) (functions cl [])

section bindings
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [rpcdriver.Assumptions]
variable [bvi : go.BasicIntoValInj]

attribute [local instance] GooseGlobalGS.gooseInvGS

set_option goose.wp.extras true

/-- What a method's `NewArg` must meet (`methodOk`'s body). -/
def newArgOk (C : net.rpc.CodecSpec GF) (rcvr : GoInterface) (Sm : net.rpc.MSpec GF)
    (v : net.rpc.Method) : IProp GF :=
  iprop(□ ∀ Ψ : val → IProp GF,
      ▷ (∀ (argv : GoInterface) (D : IProp GF) (Θ : List w8 → Bool → IProp GF),
          ⌜argv ≠ interface.nil⌝ -∗ net.rpc.argDec C argv D Sm Θ -∗ D -∗
          (∀ (args : List w8) (Φ : List w8 → GoString → IProp GF), Sm args Φ -∗ Θ args true -∗
            net.rpc.callObl C rcvr v argv Φ) -∗ Ψ #argv) -∗
      WP (App (Val #v.NewArg') (Val #())) {{ Ψ }})

instance newArgOk_persistent (C : net.rpc.CodecSpec GF) (rcvr : GoInterface)
    (Sm : net.rpc.MSpec GF) (v : net.rpc.Method) :
    Persistent (newArgOk (hG := hG) C rcvr Sm v) := by
  unfold newArgOk; infer_instance

theorem methodOk_of (C : net.rpc.CodecSpec GF) (rcvr : GoInterface) (Sm : net.rpc.MSpec GF)
    (mm : Loc) (v : net.rpc.Method) :
    mm ↦□ v ∗ newArgOk C rcvr Sm v ⊢ net.rpc.methodOk C rcvr Sm mm := by
  unfold net.rpc.methodOk newArgOk
  iintro ⟨#Hm, #Hn⟩
  iexists v
  iframe Hm
  iexact Hn

theorem echoSvc_Echo (γid : GName) (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    echoSvc (GF := GF) γid go!"Echo" args Φ = echoSpec γid args Φ := by
  unfold echoSvc; rw [if_pos rfl]

theorem newArg_Echo (L : CodecLaws (GF := GF)) (HE : service.Svc.Echo.spec (GF := GF) (hG := hG))
    (γid : GName) (s : Loc) :
    net.rpc.codecSet (drvCodec (GF := GF)) ∗ service.isSvc γid s ⊢
    newArgOk drvCodec (ptrIface service.Svc.ty s) (echoSvc γid go!"Echo")
      (mOf rpcNewArg_r0_Echo rpcNewReply_r0_Echo rpcCall_r0_Echo) := by
  iintro ⟨#Hcs, #HS⟩
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  have hne : ptrIface service.Args.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec drvCodec (ptrIface service.Args.ty p)
      (p ↦ service.Args.mk (W64 0) slice.nil go!"") (echoSvc γid go!"Echo")
      (fun args ok => iprop(if ok then ∃ (id : w64) (data : List w8) (fail : GoString)
          (dsl : GoSlice), ⌜args = encArgs id data fail ∧ args.length < 2 ^ 63⌝ ∗
          p ↦ service.Args.mk id dsl fail ∗ dsl ↦* data
        else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HD
    rw [echoSvc_Echo]
    unfold echoSpec
    icases HD with ⟨%id, %data, %fail, %Hargs, Htok, HD⟩
    isplitl [Htok HD]
    · iexists id, data, fail
      iframe Htok HD
      ipureintro; exact Hargs
    subst Hargs
    iapply L.decA_Args
    iframe Hp
    iintro %dsl %hb Hp Hdsl
    (try simp only [ite_true])
    iexists id, data, fail, dsl
    iframe Hp Hdsl
    ipureintro; exact ⟨rfl, hb⟩
  ihave Hp : p ↦ service.Args.mk (W64 0) slice.nil go!"" $$ [Hp]
  · rw [show service.Args.mk (W64 0) slice.nil go!"" = zero_val service.Args from rfl]
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HD Hp
  (try simp only [ite_true])
  icases Hp with ⟨%id, %data, %fail, %dsl, ⟨%Hm, %Hl⟩, Hp, Hdsl⟩
  rw [echoSvc_Echo]
  unfold echoSpec
  icases HD with ⟨%id', %data', %fail', %Hargs, Htok, HD⟩
  obtain ⟨rfl, rfl, rfl⟩ := encArgs_inj id id' data data' fail fail' (Hm ▸ Hl) (Hm ▸ Hargs)
  unfold net.rpc.callObl
  wp_func_call
  wp_call
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  wp_func_call
  wp_call
  wp_auto
  ihave Hr : «$r0_ptr» ↦ service.Reply.mk (W64 0) slice.nil (W64 0) $$ [«$r0»]
  · rw [show service.Reply.mk (W64 0) slice.nil (W64 0) = zero_val service.Reply from rfl]
    iexact «$r0»
  wp_apply (HE γid s p «$r0_ptr» id dsl fail _) $$ [Hp Hr Htok] as %e ⟨Hp, Hr, Hres⟩
  · iframe; iexact HS
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  icases Hres with (%Hfe | ⟨%Hf, #Hmsg⟩)
  · ileft
    isplitr
    · ipureintro; exact Hfe.2
    icases HD with ⟨HD, -⟩
    iapply L.enc_Reply
    iframe Hr Hdsl
    iintro _ _
    iapply HD
    ipureintro; exact Hfe.1
  · iright; ileft
    iexists fail
    iframe Hmsg
    rw [if_neg Hf]
    icases HD with ⟨-, HD, -⟩
    iapply HD
    ipureintro; exact Hf

theorem svcRcv_holds (L : CodecLaws (GF := GF))
    (HE : service.Svc.Echo.spec (GF := GF) (hG := hG)) : svcRcv.spec (GF := GF) := by
  intro γid s
  iintro ⟨%Hnn, #Hcs, #HS⟩
  rw [drvCodec_rcv_eq]
  iintro %Φ HΦ
  iapply wp_fupd
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) _ _) as %mp Hm
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m0 as H0
  ipersist H0
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  ipersist «$r0»
  imod ownMap_persist $$ Hm with #Hm
  iapply HΦ
  unfold net.rpc.rcvrIs
  iexists _, _
  iframe «$r0» Hm
  isplitr
  · ipureintro
    refine ⟨rfl, ?_, ?_⟩
    · simp [Hnn]
    · exact GMap.map_size_ne_0_lookup_2 _ (GMap.lookup_insert _ _ _)
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun k mm => net.rpc.methodOk drvCodec
    (ptrIface service.Svc.ty s) (echoSvc γid k) mm) ?_).2
  · rfl
  isplitr
  · iapply methodOk_of
    iframe H0
    iapply newArg_Echo L HE γid s
    iframe Hcs HS
  iapply BI.BigSepM.bigSepM_empty.2
  itrivial

theorem noMethodsRcv_holds : noMethodsRcv.spec (GF := GF) := by
  intro p
  iintro %Hnn
  rw [drvCodec_rcv_eq]
  iintro %Φ HΦ
  iapply wp_fupd
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) _ _) as %mp Hm
  (try wp_auto)
  ipersist «$r0»
  imod ownMap_persist $$ Hm with #Hm
  iapply HΦ
  unfold net.rpc.rcvrNone
  iexists _
  iframe «$r0» Hm
  ipureintro
  refine ⟨rfl, ?_⟩
  simp [Hnn]

end bindings

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

end Perennial
