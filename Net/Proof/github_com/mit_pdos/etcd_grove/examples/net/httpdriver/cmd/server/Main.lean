/- Lean-first (no Rocq counterpart).

# `net/httpdriver/cmd/server`'s `main`: `Server()`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.BootDefs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Server
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [hπ : net.http.HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main
    (wp_Server : github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Server.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server ∗
        github_com.mit_pdos.etcd_grove.examples.net.httpdriver.bootRes ∗ ⌜threadBound GF ≤ 2 ^ 30⌝ ∗
        net.http.protoLis (Gg := hG.goose_globalGS) github_com.mit_pdos.etcd_grove.examples.net.httpdriver.addrS
          github_com.mit_pdos.etcd_grove.examples.net.httpdriver.drvP }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hres, %Hb, #Hpl⟩
  iunfold github_com.mit_pdos.etcd_grove.examples.net.httpdriver.bootRes at Hres
  icases Hres with ⟨#Hu, ⟨%ms, #Hms⟩, #Hse, -⟩
  ihave #Hd : (isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver) $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_Server ms $$ []
  · iframe Hu Hms Hse Hpl
    ipureintro; exact Hb
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server
end Perennial
