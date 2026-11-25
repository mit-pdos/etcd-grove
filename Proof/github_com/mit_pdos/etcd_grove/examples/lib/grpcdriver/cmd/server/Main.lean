/- Lean-first (no Rocq counterpart).

# Command `server`'s `main`

`grpcdriver.Server()`, from the command's package fact (its imports' facts) and the server's start
(its address's listening token in its invariant, the address set to serve the driver's table).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Server
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.server.Base
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.server

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem wp_main
    (wp_Server : github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Server.spec (GF := GF) (hG := hG))
    [hX : HasExt netExt] (π : NetProtoGS) (σ : NetSlotGS) (γid : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.server ∗
        inv (lisTokN github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.drvAddr)
          (netLisTok (NG (Gg := hG.goose_globalGS)) github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.drvAddr) ∗
        grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ)
          github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.drvAddr
          (github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.drvSvc γid) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpkg, #Htok, #Haddr⟩
  ihave #Hd : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_Server π σ γid $$ []
  · iframe #
  try wp_auto
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.server
end Perennial
