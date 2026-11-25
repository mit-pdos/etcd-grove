/-
The proof of acceptloop's `client` command (`examples/net/acceptloop/cmd/client/main.go`): its
`main` calls `acceptloop.Call` (`wp_Call`, `Nodes.lean`: 1 to 8 concurrent calls, joined by a
wait group), with `io.EOF`'s and `poll.ErrDeadlineExceeded`'s values from the package's initialization
(`eof_init`; `wire.ed_init`, from `wire`'s). The command is the client node's program, a process of
its own, in `Results.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.Nodes
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.client.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)
open github_com.mit_pdos.etcd_grove.examples.net.acceptloop (srvAddr echoInvs eof_init
  wp_Call)

namespace github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.client

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- The client node's program: two concurrent calls to the server at `SrvAddr` (the plan's `h`),
from any host. -/
theorem wp_main
    (wp_RandomInt : wire.RandomInt.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (wp_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ ⌜addrOk srvAddr = true⌝ }}
      (App (Val (@! main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  ihave #Hal : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.acceptloop) $$ []
  · iPkgInit
  icases eof_init $$ Hal with ⟨%eof, #Heof⟩
  ihave #Hwire : (isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.net.wire) $$ []
  · iPkgInit
  icases wire.ed_init $$ Hwire with ⟨%ed, #Hed⟩
  (try wp_auto)
  wp_apply wp_Call wp_RandomInt wp_Dial wp_ReadFull wp_Write wp_Close wp_Add wp_Done wp_Wait γm eof ed $$ []
  · iframe Hinvs Hplan Heof Hed
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.client
end Perennial
