/-
The proof of halfclose's client command (`examples/net/halfclose/cmd/client`): its `main` calls
`halfclose.Call` (`wp_Call`, `Nodes.lean`), with `io.EOF`'s value from the package's
initialization (`eof_init`), which the command's initialization gives (`iPkgInit`).
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.Nodes
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.client.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)
open github_com.mit_pdos.etcd_grove.examples.net.halfclose (hcInvs srvAddr wp_Call eof_init)

namespace github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- The client command's `main`: `Call`, under halfclose's protocol (`hcInvs`) and the plan's
entry of `SrvAddr` (at any host `h`). -/
theorem wp_main
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_CloseWrite : net.TCPConn.CloseWrite.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.client ∗
        hcInvs γm ∗ tcpPlan G srvAddr h }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  ihave #Hhc : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.halfclose) $$ []
  · iPkgInit
  icases eof_init $$ Hhc with ⟨%x, #Heof⟩
  (try wp_auto)
  wp_apply wp_Call wp_Dial wp_Read wp_Write wp_CloseWrite wp_Close γm h x $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.client
end Perennial
