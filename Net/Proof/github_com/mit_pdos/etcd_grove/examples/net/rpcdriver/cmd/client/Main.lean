/- Lean-first (no Rocq counterpart).

# `net/rpcdriver/cmd/client`'s `main`: `Register()` (the codec, from net/rpc's first-run `codecUnset`),
then `Client()`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.BootDefs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Register
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Client
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.client
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.client.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main
    (wp_Register : github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Register.spec (GF := GF) (hG := hG))
    (wp_Client : github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Client.spec (GF := GF) (hG := hG))
    (γid reg : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.client ∗ github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.bootRes ∗
        ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ threadTok ∗
        net.rpc.rpcAddr (Gg := hG.goose_globalGS) (github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.drvWorld γid reg) github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.tcpAddr ∗
        net.rpc.rpcAddrP (Gg := hG.goose_globalGS) (github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.drvWorld γid reg) github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.httpAddr
          (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns ∗
        ghostMapAuth (K := w64) (V := Unit) γid 1 ∅ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); threadTok }} := by
  wp_start as ⟨Hres, %Hb, %Hrb, Htok, #Htcp, #Hha, Hauth⟩
  iunfold github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.bootRes at Hres
  icases Hres with ⟨-, Hrf, #Hf⟩
  iunfold net.rpc.rpcFirstRes at Hrf
  icases Hrf with ⟨Hunset, -⟩
  ihave #Hrpc : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hhttp : (isPkgInit (PROP := IProp GF) pkg_id.net.http) $$ []
  · iPkgInit
  ihave #Hsync : (isPkgInit (PROP := IProp GF) pkg_id.sync) $$ []
  · iPkgInit
  ihave #Hstr : (isPkgInit (PROP := IProp GF) pkg_id.strings) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrpc
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, #Henv, #Hcon, #Hmu⟩
  iunfold net.rpc.srvEnv at Henv
  icases Henv with ⟨#Hcli, -⟩
  ihave #Hhe := net.http.httpEnv_access $$ Hhttp
  try wp_auto
  wp_apply wp_Register $$ [$Hsync $Hmu $Hunset] as #Hset
  wp_apply wp_Client γid reg $$ [Htok Hauth] as Htok
  · iframe Htok Hstr Hsync Hf Hset Hcli Hhe Hcon Htcp Hha Hauth
    ipureintro; exact ⟨Hb, Hrb⟩
  iapply HΦ
  iexact Htok

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.client
end Perennial
