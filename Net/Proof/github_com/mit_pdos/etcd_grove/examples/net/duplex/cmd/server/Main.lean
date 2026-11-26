/-
The proof of `examples/net/duplex/cmd/server`'s `main`, the server node's program: it calls
`duplex.Serve` (`wp_Serve`, `Nodes.lean`), with the example package's initialization from the
command's (`iPkgInit`) and the values of `io.EOF` and `poll.ErrDeadlineExceeded` from it (`eof_init`,
`wire.ed_init`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.Nodes
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)
open github_com.mit_pdos.etcd_grove.examples.net.duplex (dupInvs srvAddr eof_init wp_Serve)

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : server.Assumptions]
variable [go.BasicIntoValInj]

/-- The server node's program, over the protocol's invariants and the plan's entry for `SrvAddr`
at the node's own host (the network's plan, which `Listen` reads). -/
theorem wp_main
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server ∗
        dupInvs γm ∗ ⌜addrOk srvAddr = true⌝ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, %Hplan⟩
  ihave #Hdup : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.duplex) $$ []
  · iPkgInit
  icases eof_init $$ Hdup with ⟨%eof, #Heof⟩
  ihave #Hwire : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.wire) $$ []
  · iPkgInit
  icases wire.ed_init $$ Hwire with ⟨%ed, #Hed⟩
  (try wp_auto)
  wp_apply wp_Serve wp_Listen wp_Accept wp_Read wp_Write wp_Close γm eof ed $$ []
  · iframe Hinvs Heof Hed
    ipureintro; exact Hplan
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server
end Perennial
