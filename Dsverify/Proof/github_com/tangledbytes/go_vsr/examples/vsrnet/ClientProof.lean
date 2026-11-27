/-
Client machine `c`'s program (`kit.go`'s `Client`, notes/dsv-vr.md): `mkClient(Addrs(),
waitConf(CfgAddrs(), 1 + c), c)`, then `remote.ServeClient(c, ClientAddrs()[c], newClient, Op,
Codec(), attempt())` with `newClient` returning the system made before.

Against remote's `ServeClient.spec` (remote-serveclient): `newClient` is a one-shot WP, which here
consumes the client's exclusive system (`sysRes`: its go-vsr client, the ghost layer's request
counter `nextReq`) and starts the far side's count of served calls (`budUsed_zero`); each call of
`Op` comes with one of the address's call units (`budUnit`), counted by `budUsed_add`, which bounds
the request counter by the address's budget (24 units: `Check`'s 8 operations of `readTries`
attempts), well below the ghost layer's 2^28 (`Op.spec`'s `n < 2 ^ 28`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.MkClientProofDefs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ClientProofDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS
attribute [local instance] Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.jsonCodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

theorem Client.wp_proof
    (codec_ok : vsrnet.codecOk (GF := GF) (hG := hG))
    (wp_Op : Op.spec (GF := GF) (hG := hG))
    (wp_ServeClient : github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient.spec (GF := GF) (hG := hG) (I := KIn) (O := KOut))
    (wp_CfgAddrs : CfgAddrs.spec (GF := GF) (hG := hG))
    (wp_waitConf : waitConf.spec (GF := GF) (hG := hG))
    (wp_mkClient : mkClient.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro γ c hc
  wp_start as ⟨#Hcp, #Hnp, #HsysI, #HregI, Hnext, #Hra, %Hbud, Hfr⟩
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  ihave #Hkit : encoding.json.kitCodecOk (GF := GF) vsrnet.scanF $$ []
  · have hk := codec_ok
    unfold vsrnet.codecOk at hk
    iapply hk
  wp_auto
  wp_apply wp_Addrs as %asl Hasl
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hasl with #Hasl
  imodintro
  wp_apply wp_CfgAddrs as %cfgs Hcfgs
  wp_apply (wp_waitConf γ cfgs
    (DFrac.own 1) (W64 1 + W64 (c : Int)) (by word)) $$ [Hcfgs] as %cf ⟨-, #Hcf⟩
  · iframe; iframe #
  wp_apply (wp_mkClient γ c asl cf hc) $$ [Hnext Hfr] as %x Hres
  · iframe; iframe #
  wp_apply wp_ClientAddrs as %casl Hcasl
  ihave %Hal := ownSlice_len _ _ _ $$ Hcasl
  have hal : clientAddrs.length = 6 := rfl
  have hb : 0 ≤ sint.Z (W64 (c : Int)) ∧ sint.Z (W64 (c : Int)) < sint.Z casl.len := by
    rw [hal] at Hal; constructor <;> word
  rw [ite_eq_left hb]
  list_elem clientAddrs c as a
  wp_apply wp_load_slice_index casl (sint.Z (W64 (c : Int))) clientAddrs _ a hb.1 $$ [Hcasl]
    as Hcasl
  · iframe
    ipureintro
    rw [show (sint.Z (W64 (c : Int))).toNat = c by word]
    exact Ha_lookup
  have ha : a = clientAddrs.getD c [] := by simp [List.getD_eq_getElem?_getD, Ha_lookup]
  subst ha
  wp_auto
  wp_apply (wp_Codec γ.gn) as %cd #Hcd
  wp_apply wp_attempt as %d -
  wp_apply (wp_ServeClient (RBase.svc (Gg := hG.goose_globalGS) (kvR γ.gn)) (W64 (c : Int))
    (clientAddrs.getD c []) _ (functions github_com.tangledbytes.go_vsr.examples.vsrnet.Op []) cd d
    (sysTok γ c (clientAddrs.getD c []))) $$ [Hres sys] as ⟨⟩
  iframe #
  isplit
  · iapply codecOk_wireOk $$ Hcd
  isplitl []
  · iapply (Op_svcOp wp_Op γ c hc _ Hbud) $$ Hpkg
  -- `newClient(c)`: the system made before, with the far side's count at none
  iintro %Φn HΦn
  wp_auto
  iapply HΦn
  unfold sysTok
  iexists 1, 0
  isplitr
  · ipureintro; omega
  isplitl [Hres]
  · iexact Hres
  iapply budUsed_zero

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
