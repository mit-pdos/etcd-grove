/- Lean-first (no Rocq counterpart).

# `net/httpdriver/cmd/client`'s `main`: `Client()`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.BootDefs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Client
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [hπ : net.http.HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem wp_main
    (wp_Client : github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Client.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client ∗
        github_com.mit_pdos.etcd_grove.examples.net.httpdriver.bootRes ∗ ⌜threadBound GF ≤ 2 ^ 30⌝ ∗
        github_com.mit_pdos.etcd_grove.examples.net.httpdriver.drvAddr ∗ threadTok }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); threadTok }} := by
  wp_start as ⟨#Hres, %Hb, #Ha, Htok⟩
  iunfold github_com.mit_pdos.etcd_grove.examples.net.httpdriver.bootRes at Hres
  icases Hres with ⟨-, -, -, #Hf⟩
  ihave #Hd : (isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver) $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_Client $$ [Htok] as Htok
  · iframe Hd Hf Ha Htok
    ipureintro; exact Hb
  iapply HΦ
  iexact Htok

end proof

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client
end Perennial
