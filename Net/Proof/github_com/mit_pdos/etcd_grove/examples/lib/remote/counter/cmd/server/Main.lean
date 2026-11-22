/-
The proof of the counter instance's `cmd/server` `main`: `counter.Server(ServerAddr)`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server.Base
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Server

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server

open github_com.mit_pdos.etcd_grove.examples.lib.remote github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : cmd.server.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem wp_main (wp_Server : counter.Server.spec (GF := GF) (hG := hG)) (γs : GName) :
    {{ isPkgInit (PROP := IProp GF)
          pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server ∗
        remoteAddr (Gg := hG.goose_globalGS) (cR (GF := GF) γs) go!"127.0.0.1:7301" ∗
        ghostVar γs (1 : Qp).half (W64 0) }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hra, Hs⟩
  ihave #Hcp : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter) $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Server γs go!"127.0.0.1:7301" $$ [Hs] as ⟨⟩
  iframe #
  iframe Hs

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server
end Perennial
