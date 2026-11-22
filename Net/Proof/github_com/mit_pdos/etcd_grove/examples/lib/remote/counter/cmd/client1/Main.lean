/-
The proof of the counter instance's `cmd/client1` `main`: `counter.Client(1, ClientAddr1, ServerAddr)`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client1.Base
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Client

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client1

open github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.client1.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Client : counter.Client.spec (GF := GF) (hG := hG)) (γs : GName) :
    {{ isPkgInit (PROP := IProp GF)
          pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client1 ∗
        remoteAddr (Gg := hG.goose_globalGS) (cR (GF := GF) γs) go!"127.0.0.1:7303" ∗
        remoteAddr (Gg := hG.goose_globalGS) (cR (GF := GF) γs) go!"127.0.0.1:7301" ∗
        mapCtx (Gg := hG.goose_globalGS) (I := Bool) ∗
        □ (∀ i : Bool, ⌜cB.isWrite i = false⌝ -∗
          lin (Gg := hG.goose_globalGS) (cR (GF := GF) γs) i (fun _ => iprop(True))) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hra, #Hsa, #Hmap, #Hrd⟩
  ihave #Hcp : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Client γs (W64 1) go!"127.0.0.1:7303" go!"127.0.0.1:7301" $$ [] as ⟨⟩
  iframe #

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client1
end Perennial
