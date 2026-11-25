/- Lean-first (no Rocq counterpart).

# `net/rpcdriver/cmd/server`'s `main`: `Register()` (the codec, from net/rpc's first-run `codecUnset`),
then `Server()`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.BootDefs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Register
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Server
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.server
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.server.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.server

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main
    (wp_Register : github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Register.spec (GF := GF) (hG := hG))
    (wp_Server : github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Server.spec (GF := GF) (hG := hG))
    (γid reg : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.server ∗ github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.bootRes ∗
        ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
        net.rpc.rpcLisP (Gg := hG.goose_globalGS) (github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.drvWorld γid reg) github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.tcpAddr [] [] ∗
        net.rpc.rpcLisP (Gg := hG.goose_globalGS) (github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.drvWorld γid reg) github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.httpAddr
          (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hres, %Hb, #Htl, #Hhl⟩
  iunfold github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.bootRes at Hres
  icases Hres with ⟨Hmux, #Hse, Hrf, #Hf⟩
  iunfold net.rpc.rpcFirstRes at Hrf
  icases Hrf with ⟨Hunset, %γs, %γf, #Hds, Hown⟩
  ihave #Hrpc : (isPkgInit (PROP := IProp GF) pkg_id.net.rpc) $$ []
  · iPkgInit
  ihave #Hhttp : (isPkgInit (PROP := IProp GF) pkg_id.net.http) $$ []
  · iPkgInit
  ihave #Hsync : (isPkgInit (PROP := IProp GF) pkg_id.sync) $$ []
  · iPkgInit
  ihave #Hlog : (isPkgInit (PROP := IProp GF) pkg_id.log) $$ []
  · iPkgInit
  ihave #Hsvcp : (isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service) $$ []
  · iPkgInit
  ihave #Hri := net.rpc.rpcInit_access $$ Hrpc
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, #Henv, #Hcon, #Hmu⟩
  try wp_auto
  wp_apply wp_Register $$ [$Hsync $Hmu $Hunset] as #Hset
  wp_apply wp_Server γid reg γs γf $$ [Hown Hmux]
  · iframe Hf Hset Hhttp Hlog Hsvcp Henv Hcon Hse Hds Hown Hmux Htl Hhl
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.server
end Perennial
