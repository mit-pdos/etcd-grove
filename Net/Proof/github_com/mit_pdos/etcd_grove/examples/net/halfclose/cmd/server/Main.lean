/-
The proof of halfclose's server command (`examples/net/halfclose/cmd/server`): its `main` calls
`halfclose.Serve` (`wp_Serve`, `Nodes.lean`), with `io.EOF`'s value from the package's
initialization (`eof_init`), which the command's initialization gives (`iPkgInit`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.Nodes
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.server.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)
open github_com.mit_pdos.etcd_grove.examples.net.halfclose (hcInvs srvAddr wp_Serve eof_init)

namespace github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.server

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [go.BasicIntoValInj]

/-- The server command's `main`: `Serve`, under halfclose's protocol (`hcInvs`) and the plan's
address `SrvAddr` at the node's host (the network's plan, `Listen`'s premise). -/
theorem wp_main
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.server ∗
        hcInvs γm ∗
        ⌜addrOk srvAddr = true⌝ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, %Hplan⟩
  ihave #Hhc : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.halfclose) $$ []
  · iPkgInit
  icases eof_init $$ Hhc with ⟨%x, #Heof⟩
  (try wp_auto)
  wp_apply wp_Serve wp_Listen wp_Accept wp_Read wp_Write wp_Close γm x $$ []
  · iframe Hinvs Heof
    ipureintro; exact Hplan
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.server
end Perennial
