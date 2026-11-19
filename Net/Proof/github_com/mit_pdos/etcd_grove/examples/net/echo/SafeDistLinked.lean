/-
`examples/net/echo` as an instance of the kits' statement `SafeDist`
(`Net/Statement/SafeDist.lean`): the check that the statement is not vacuous
(`notes/dsverify-net-port-plan.md`, phase 4). The three nodes (`cmd/server`, `cmd/client`, `cmd/junk`, each its package's boot program with no
arguments), the plan `[(SrvAddr, "h")]`, every node on the host `"h"` (the examples run on one
machine). From the start resources `SafeDist`'s bridge gives (`SrvAddr` unset: its pending set and
plan entry), the proof allocates echo's own protocol (`echoInvs`, `Defs.lean`) rather than the
kits' library (a program may keep the network's resources in its own protocol), and each node's
boot program is safe by the same `wp_main` lemmas as `echo_crash_safety` (`Results.lean`).

`echo_safeDist` is `SafeDist`, closed: its premises are only the program's assumptions on the Go
context (`go.BasicIntoValInj`, and each node's `Assumptions` inside the statement). The theorem
without restarts is weaker than `echo_crash_safety` (with crashes and restarts); it is here to show
that `SafeDist`'s premises (`PlanWellFormed`, the start) are met by a real system.
-/
module

public import Net.Statement.SafeDist
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.Results

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.echo

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section nodes
variable [GoGlobalContext]

/-- The server node: `cmd/server`'s `main`. -/
def serverNode : Net.Node where
  Assumptions := fun [GoLocalContext] [GoSemanticsFunctions] =>
    cmd.server.Assumptions ∧ net.FieldAssumptions
  init := cmd.server.initialize'
  main := cmd.server.main

/-- The client node: `cmd/client`'s `main`. -/
def clientNode : Net.Node where
  Assumptions := fun [GoLocalContext] [GoSemanticsFunctions] =>
    cmd.client.Assumptions ∧ net.FieldAssumptions
  init := cmd.client.initialize'
  main := cmd.client.main

/-- The junk sender: `cmd/junk`'s `main`. -/
def junkNode : Net.Node where
  Assumptions := fun [GoLocalContext] [GoSemanticsFunctions] =>
    cmd.junk.Assumptions ∧ net.FieldAssumptions
  init := cmd.junk.initialize'
  main := cmd.junk.main

/-- The plan: the server's address, at the host `"h"`. -/
def echoPlan : List (GoString × GoString) := [(srvAddr, go!"h")]

/-- Every node on the host `"h"`. -/
def echoHosts : List GoString := [go!"h", go!"h", go!"h"]

theorem echoPlan_wf : PlanWellFormed echoPlan := by decide

end nodes

set_option linter.unusedVariables false in
/-- **echo is safe, as a `SafeDist`**: the three nodes, in every execution without restarts
from a start with the plan `echoPlan` and every node on `"h"`, are safe. -/
theorem echo_safeDist [GoGlobalContext] [go.BasicIntoValInj] :
    SafeDist [serverNode, clientNode, junkNode] echoPlan echoHosts := by
  refine safeDist_of_bootAt _ _ _ echoPlan_wf rfl ?_
  intro G
  iintro %hplan Hs
  have HGp : (extGlobalGS netExt (G := G)).plan !! srvAddr = some go!"h" := by
    rw [hplan]; rfl
  unfold echoPlan
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hu, -⟩
  unfold addrUnset addrTok
  icases Hu with ⟨Hpend, %h, #Hplan, %HGh⟩
  dsimp only at HGh
  have hh : h = go!"h" := by rw [HGp] at HGh; cases HGh; rfl
  subst hh
  imod echoInvs_alloc (Gg := G) $$ Hpend with ⟨%γm, #Hinvs⟩
  imodintro
  iexists fun _ => iprop(echoInvs (Gg := G) γm ∗ netPlan (extGlobalGS netExt) srvAddr go!"h" ∗
    ⌜(extGlobalGS netExt (G := G)).plan !! srvAddr = some go!"h"⌝)
  isplitr
  · ipureintro
    intro i nd hh hnd hhost hG s hGG hA
    subst hGG
    letI := hG
    letI := s
    match i, hnd, hhost with
    | 0, hnd, hhost =>
      cases hnd; cases hhost
      obtain ⟨hA1, hA2⟩ := hA
      haveI := hA1; haveI := hA2
      iintro ⟨#Hinvs, #Hplan, %HGp⟩ %Hh Hgs
      rw [show serverNode.boot = boot cmd.server.initialize' cmd.server.main from rfl]
      iapply wp_boot cmd.server.initialize' cmd.server.main _ cmd.server.getIsPkgInit
          (cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf) _
          (cmd.server.wp_main net.Listen.wp_proof net.Listener.Accept.wp_proof
            (wire.ReadFull.wp_proof net.Conn.Read.wp_proof) net.Conn.Write.wp_proof
            net.Conn.Close.wp_proof γm) $$ [] Hgs
      iframe Hinvs
      ipureintro
      rw [Hh]
      exact HGp
    | 1, hnd, hhost =>
      cases hnd; cases hhost
      obtain ⟨hA1, hA2⟩ := hA
      haveI := hA1; haveI := hA2
      iintro ⟨#Hinvs, #Hplan, %HGp⟩ %Hh Hgs
      rw [show clientNode.boot = boot cmd.client.initialize' cmd.client.main from rfl]
      iapply wp_boot cmd.client.initialize' cmd.client.main _ cmd.client.getIsPkgInit
          (cmd.client.wp_initialize' _ cmd.client.getIsPkgInit_wf) _
          (cmd.client.wp_main net.Dial.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
            net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm go!"h") $$ [] Hgs
      iframe Hinvs Hplan
    | 2, hnd, hhost =>
      cases hnd; cases hhost
      obtain ⟨hA1, hA2⟩ := hA
      haveI := hA1; haveI := hA2
      iintro ⟨#Hinvs, #Hplan, %HGp⟩ %Hh Hgs
      rw [show junkNode.boot = boot cmd.junk.initialize' cmd.junk.main from rfl]
      iapply wp_boot cmd.junk.initialize' cmd.junk.main _ cmd.junk.getIsPkgInit
          (cmd.junk.wp_initialize' _ cmd.junk.getIsPkgInit_wf) _
          (cmd.junk.wp_main net.Dial.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
            net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm go!"h") $$ [] Hgs
      iframe Hinvs Hplan
  · dsimp only
    ihave #HP : iprop(echoInvs (Gg := G) γm ∗ netPlan (extGlobalGS netExt) srvAddr go!"h" ∗
        ⌜(extGlobalGS netExt (G := G)).plan !! srvAddr = some go!"h"⌝) $$ []
    · iframe Hinvs Hplan
      ipureintro; exact HGp
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iexact HP
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iexact HP
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iexact HP
    iapply BigSepL.bigSepL_nil.2
    iempintro

#print axioms echo_safeDist

end github_com.mit_pdos.etcd_grove.examples.net.echo

end Perennial
