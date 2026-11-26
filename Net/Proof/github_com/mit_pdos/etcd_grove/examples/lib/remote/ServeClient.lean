/-
The proof of `ServeClient` (`Net/Spec/.../lib/remote/ServeClient.lean`): `newClient(c)` (its
WP, a one-shot premise: `tok sys`), then `Serve`, which never returns.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Serve
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {I O : Type} [Pos.Countable I] [Pos.Countable O]

theorem ServeClient.wp_proof
    (wp_Serve : Serve.spec (GF := GF) (hG := hG) (I := I) (O := O)) :
    ServeClient.spec (GF := GF) (hG := hG) (I := I) (O := O) := by
  intro S c a newClient op cd d tok
  wp_start as ⟨#Haddr, #Hcd, #Hop, HnewClient⟩
  wp_auto
  wp_apply HnewClient as %sys Hsys
  wp_apply wp_Serve S a sys op cd d tok $$ [Hsys] as Hf
  · iframe Haddr Hcd Hop Hsys
  iexfalso
  iexact Hf

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
