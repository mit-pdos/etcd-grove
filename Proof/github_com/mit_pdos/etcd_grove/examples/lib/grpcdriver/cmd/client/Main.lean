/- Lean-first (no Rocq counterpart).

# Command `client`'s `main`

`grpcdriver.Client()`, from the command's package fact (its imports' facts), the server's address set
to serve the driver's table, the ids' ghost map (empty) and the main thread's token.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Client
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem wp_main
    (wp_Client : github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Client.spec (GF := GF) (hG := hG))
    [hX : HasExt netExt] (π : NetProtoGS) (σ : NetSlotGS) (γid : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client ∗
        ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ threadTok ∗
        grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ)
          github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.drvAddr
          (github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.drvSvc γid) ∗
        ghostMapAuth (K := w64) (V := Unit) γid 1 ∅ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); threadTok }} := by
  wp_start as ⟨#Hpkg, %Hb, Htok, #Haddr, Hauth⟩
  ihave #Hd : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_Client π σ γid $$ [Htok Hauth] as Htok
  · iframe #
    iframe
    ipureintro; exact Hb
  try wp_auto
  iapply HΦ
  iexact Htok

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client
end Perennial
