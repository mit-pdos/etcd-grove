/-
The proof of acceptloop's `server` command (`examples/net/acceptloop/cmd/server/main.go`): its
`main` calls `acceptloop.Serve` (`wp_Serve`, `Nodes.lean`), with `io.EOF`'s and
`poll.ErrDeadlineExceeded`'s values from the package's initialization (`eof_init`;
`wire.ed_init`, from `wire`'s). The command is the server node's program, a process of its own, in `Results.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.Nodes
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.server.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)
open github_com.mit_pdos.etcd_grove.examples.net.acceptloop (srvAddr echoInvs eof_init
  wp_Serve)

namespace github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.server

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.server

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : Assumptions]
variable [go.BasicIntoValInj]

/-- The server node's program: the accept loop at `SrvAddr`, on the host the plan puts it at (a
`Listen` of `SrvAddr` listens at it, `ListenAt`). -/
theorem wp_main
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗
        ⌜addrOk srvAddr = true⌝ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, %Hla⟩
  ihave #Hal : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.acceptloop) $$ []
  · iPkgInit
  icases eof_init $$ Hal with ⟨%eof, #Heof⟩
  ihave #Hwire : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.wire) $$ []
  · iPkgInit
  icases wire.ed_init $$ Hwire with ⟨%ed, #Hed⟩
  (try wp_auto)
  wp_apply wp_Serve wp_Listen wp_Accept wp_ReadFull wp_Write wp_Close γm eof ed $$ []
  · iframe Hinvs Heof Hed
    ipureintro; exact Hla
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.server
end Perennial
