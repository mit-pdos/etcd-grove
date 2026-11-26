/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/RegisterProof.lean (run
gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

`serverlib.RegisterWithMaster(ipOf k, portNum k, masterRpcAddr)` on replica node `k`: dial the
master's net/rpc over HTTP (`Net/`'s `rpc.DialHTTP.spec`, `dialEnv`), call `Master.Register`
(`Client.Call.spec`, the codec's `enc_RegisterArgs` / `dec_RegisterReply`), until a `Ready` answer:
its replica id, the full node list, and what the registry gives (`regReady`, the node's id, the
replicas' predictions). Every error is logged (`errAny`) and retried after a second.

Port: the arguments are read-only (`args ↦□`, the encoding gives them back at once); the reply
is reused across attempts at its zero value (a not-ready answer decodes to the zero reply:
`dec_RegisterReply` with `nodes = []`); the answer's facts travel in the decoding's outcome
`regΘ` (no injectivity of the encoding needed); error answers are the service's `withErr` part.
-/
module

public import Dsverify.Proof.gryff.Server.MasterRun
public import Dsverify.GeneratedProof.gryff.src.serverlib

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [sA : gryff.src.serverlib.Assumptions]
variable [net.rpc.Assumptions]
variable (L : CodecLaws (GF := GF))
variable (wp_Call : net.rpc.Client.Call.spec (GF := GF) (hG := hG))
variable (wp_DialHTTP : net.rpc.DialHTTP.spec (GF := GF) (hG := hG))

/-- What `Master.Register`'s answer gives the replica node `k`: an error, not ready, or `Ready`
with the full list. -/
def regAnswer (δ : DeployNames) (k : Nat) (rep : List w8) (msg : GoString) : IProp GF :=
  iprop(⌜msg ≠ []⌝ ∨ ⌜rep = encRegReply (W64 0) [] false⌝ ∨
    ∃ (id : w64) (nodes : List GoString), ⌜rep = encRegReply id nodes true⌝ ∗
      regReady δ k id nodes)

/-- The reply `rp` after decoding the answer `rep` (`ok`): the zero reply (not ready, or no
decoding), or `Ready` with the full list and the registry's witness. -/
def regΘ (δ : DeployNames) (k : Nat) (rp : Loc) (_rep : List w8) (ok : Bool) : IProp GF :=
  if ok then
    iprop(rp ↦ gryff.src.masterproto.RegisterReply.mk (W64 0) slice.nil false ∨
      ∃ (id : w64) (nodes : List GoString) (nl : GoSlice),
        rp ↦ gryff.src.masterproto.RegisterReply.mk id nl true ∗ nl ↦* nodes ∗
        regReady δ k id nodes)
  else iprop(rp ↦ gryff.src.masterproto.RegisterReply.mk (W64 0) slice.nil false)

omit sA in
/-- An error with a known message is `errAny`. -/
theorem errMsg_errAny' (err : GoInterface) (msg : GoString) :
    net.rpc.errMsg (GF := GF) err msg ⊢ models_lab.errAny err := by
  unfold net.rpc.errMsg models_lab.errAny
  iintro ⟨%e, %He, %Ht, #H⟩
  iexists e
  iframe %He %Ht
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iapply HΦ

set_option goose.wp.extras true

include L wp_Call wp_DialHTTP in
theorem wp_RegisterWithMaster' (γ : GryffNames GF) (k : Nat) (hk : k < 3)
    (hW : γ.rpc.SS masterRpcAddr go!"Master" = some (masterSvc γ.deploy (regCarry γ.proto))) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.serverlib ∗
        net.rpc.codecSet gryffCodec ∗ dialEnv (GF := GF) ∗
        net.rpc.rpcAddrP (Gg := hG.goose_globalGS) γ.rpc masterRpcAddr
          (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns ∗
        inv deployN (deployInv γ.deploy γ.proto) ∗ regCarry γ.proto k }}
      (App (App (App (Val (@! gryff.src.serverlib.RegisterWithMaster)) (Val #(ipOf k)))
        (Val #(portNum k))) (Val #masterRpcAddr))
    {{ (id : w64) (sl : GoSlice) (nodes : List GoString), RET (PairV #id #sl);
        sl ↦* nodes ∗ regReady γ.deploy k id nodes ∗ nodeIdIs γ.proto k id ∗ predsSet γ.proto ∗
        regPred γ.proto (uint.nat id) k }} := by
  wp_start as ⟨#Hcs, #Hde, #Hra, #Hdep, #Hcar⟩
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hanl⟩
  icases typedPointsto_not_null_dup _ _ _ $$ reply with ⟨reply, %Hrnl⟩
  ipersist «$r0»
  iunfold dialEnv at Hde
  icases Hde with ⟨%Hrb, #Hce, #Hhe, #Hcon⟩
  have hz : (zero_val gryff.src.masterproto.RegisterReply) =
      gryff.src.masterproto.RegisterReply.mk (W64 0) slice.nil false := rfl
  rw [hz]
  ihave IH : iprop(reply_ptr ↦ gryff.src.masterproto.RegisterReply.mk (W64 0) slice.nil false)
    $$ [reply]
  · iexact reply
  wp_for
  try wp_auto
  try rw [ite_eq_left_of_eq_true _ _ (by simp)]
  wp_apply (wp_DialHTTP go!"tcp" net.tcpNet_tcp γ.rpc masterRpcAddr) $$ [] as %c %err Hd
  · iframe Hce Hhe Hcon Hra
    ipureintro; exact Hrb
  icases Hd with (⟨%Herr, #Hc⟩ | ⟨%Herr, #He⟩)
  · subst Herr
    wp_auto
    wp_apply (wp_Call c γ.rpc masterRpcAddr go!"Master.Register" go!"Master" go!"Register"
      (masterSvc γ.deploy (regCarry γ.proto))
      (ptrIface gryff.src.masterproto.RegisterArgs.ty «$r0_ptr»)
      (ptrIface gryff.src.masterproto.RegisterReply.ty reply_ptr)
      (regAnswer γ.deploy k) iprop(True)
      (reply_ptr ↦ gryff.src.masterproto.RegisterReply.mk (W64 0) slice.nil false)
      (regΘ γ.deploy k reply_ptr) gryffCodec) $$ [IH] as %err2 Hres
    · iframe Hc Hcs IH
      isplitr
      · ipureintro; exact ⟨by decide, hW, by simp [ptrIface]⟩
      isplitr
      · ipureintro; simp [net.rpc.maxFrameN]
      isplitr
      · iapply L.enc_RegisterArgs «$r0_ptr» DFrac.discard (ipOf k) (portNum k)
        iframe «$r0»
        iintro -
        isplitr
        · ipureintro; exact encRegArgs_ipOf_length k (portNum k)
        isplitl
        · unfold masterSvc withErr masterSvc0
          isplit
          · isplitr
            · ipureintro; rfl
            iexists k
            isplitr
            · ipureintro; exact ⟨hk, rfl⟩
            iframe Hcar
            isplit
            · unfold regAnswer; iright; ileft; ipureintro; rfl
            · iintro %id %nodes #Hr
              unfold regAnswer; iright; iright; iexists id, nodes; iframe Hr; ipureintro; rfl
          · iintro %msg %hmsg
            unfold regAnswer; ileft; ipureintro; exact hmsg
        · itrivial
      iintro !> Hrep %rep HΦ
      unfold regAnswer
      icases HΦ with (%Hm | %Hrep0 | ⟨%id, %nodes, %Hrep1, #Hr⟩)
      · exact absurd rfl Hm
      · subst Hrep0
        iapply L.dec_RegisterReply reply_ptr (W64 0) [] false
        iframe Hrep
        iintro %nl Hrp Hnl
        rw [if_pos rfl]
        icases Hnl with %Hnl
        subst Hnl
        unfold regΘ
        simp only [↓reduceIte]
        ileft; iexact Hrp
      · subst Hrep1
        ihave %hl3 := regReady_length _ _ _ _ $$ Hr
        have hne : nodes ≠ [] := by intro h; subst h; simp at hl3
        iapply L.dec_RegisterReply reply_ptr id nodes true
        iframe Hrep
        iintro %nl Hrp Hnl
        simp only [hne, ↓reduceIte]
        unfold regΘ
        simp only [↓reduceIte]
        iright
        iexists id, nodes, nl
        iframe Hrp Hnl Hr
    icases Hres with (⟨%He2, -, %rep, HΘ⟩ | ⟨%msg, %Hm, #Hem, -, -, Hrep⟩ |
      ⟨%He2, #Hea, Hrest⟩)
    · -- the call returned: not ready, or `Ready`
      subst He2
      unfold regΘ
      simp only [↓reduceIte]
      icases HΘ with (Hrp | ⟨%id, %nodes, %nl, Hrp, Hnl, #Hr⟩)
      · iStructNamed Hrp
        wp_auto
        wp_apply log.wp_Printf_logArg _ slice.nil [] DFrac.discard as -
        · isplitr
          · iapply ownSlice_nil
          iintro !>
          iapply BigSepL.bigSepL_nil.2
          iempintro
        wp_apply time.wp_Sleep
        wp_for_post
        iframe
        iapply typedPointsto_combine _ _ _ Hrnl
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      · iStructNamed Hrp
        iapply fupd_wp
        imod deploy_nodeId γ.deploy γ.proto k hk id nodes ⊤ (by simp) $$ [Hdep Hr] with #Hnid
        · iframe #
        imod deploy_ready γ.deploy γ.proto k hk id nodes ⊤ (by simp) $$ [Hdep Hr] with ⟨#Hps, #Hrp⟩
        · iframe #
        imodintro
        wp_auto
        wp_for_post
        iapply HΦ
        iframe
        iframe #
    · -- a `ServerError`: the reply is unchanged
      obtain ⟨-, rfl⟩ := Hm
      ihave #HeA := errMsg_errAny' _ _ $$ Hem
      wp_auto
      wp_apply wp_slice_literal (V := GoInterface) _
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hlsl, -⟩
      wp_apply log.wp_Printf_logArg _ _ [net.rpc.serverErr msg] _ $$ [Hlsl] as -
      · iframe
        iintro !>
        iapply BigSepL.bigSepL_singleton.2
        iapply logArg_err $$ HeA
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · -- another error: the reply is unchanged (no decoding, or a failed one)
      ihave Hrep : iprop(reply_ptr ↦ gryff.src.masterproto.RegisterReply.mk (W64 0) slice.nil false)
        $$ [Hrest]
      · icases Hrest with (⟨-, (Hrep | ⟨%rep, Hd⟩)⟩ | ⟨-, Hrep⟩)
        · iexact Hrep
        · unfold regΘ; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hd
        · iexact Hrep
      obtain ⟨Hne, -⟩ := He2
      cases err2 with
      | nil => exact absurd rfl Hne
      | ok ei =>
      wp_auto
      wp_apply wp_slice_literal (V := GoInterface) _
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hlsl, -⟩
      wp_apply log.wp_Printf_logArg _ _ [GoInterface.ok ei] _ $$ [Hlsl] as -
      · iframe
        iintro !>
        iapply BigSepL.bigSepL_singleton.2
        iapply logArg_err $$ Hea
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
  · -- the dial failed
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_apply log.wp_Printf_logArg _ _ [GoInterface.ok ei] _ $$ [Hlsl] as -
    · iframe
      iintro !>
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_err $$ He
    wp_apply time.wp_Sleep
    wp_for_post
    iframe

end proof

end Perennial.gryff
