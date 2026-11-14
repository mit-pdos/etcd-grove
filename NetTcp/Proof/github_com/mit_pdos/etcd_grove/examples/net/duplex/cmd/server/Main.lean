/-
The proof of `examples/net/duplex/cmd/server`'s `main`, the server node's program: it calls
`duplex.Serve` (`wp_Serve`, `Nodes.lean`), with the example package's initialization from the
command's (`iPkgInit`) and the values of `io.EOF` and `poll.ErrDeadlineExceeded` from it (`eof_init`,
`ed_init`).
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.Nodes
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)
open github_com.mit_pdos.etcd_grove.examples.net.duplex (dupInvs srvAddr eof_init ed_init wp_Serve)

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : server.Assumptions] [field_sem : net.FieldAssumptions]
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
        dupInvs γm ∗ ⌜(extGlobalGS tcpExt (G := hG.goose_globalGS)).plan !! srvAddr =
          some (extLocalGS tcpExt (L := hG.goose_localGS)).host⌝ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, %Hplan⟩
  ihave #Hdup : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.duplex) $$ []
  · iPkgInit
  icases eof_init $$ Hdup with ⟨%eof, #Heof⟩
  icases ed_init $$ Hdup with ⟨%ed, #Hed⟩
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
