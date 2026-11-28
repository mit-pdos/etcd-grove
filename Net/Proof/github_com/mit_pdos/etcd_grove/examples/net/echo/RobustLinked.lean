/-
`examples/net/echo` as an instance of the distributed deployments' statement: `Robust` with no crashing machine
(`Robustness/Statement.lean`) under the deployment premise (`DistDeploy`,
`Net/Statement/DistDeploy.lean`), proved through the distributed bridge (`robust_of_distBoot`,
`Net/Statement/DistBridge.lean`): the check that the premise is not vacuous and that the bridge is
usable (`notes/dsverify-net-port-plan.md`, phase 4).

The three machines are the example's commands (`system`, `Results.lean`: `cmd/server`, `cmd/client`,
`cmd/junk`, each its package's boot program), the addresses `[SrvAddr]` (`echoAddrs`; valid:
`decide`). From the start resources the bridge gives (`SrvAddr` unset: its pending set), the proof
allocates
echo's own protocol (`echoInvs`, `Defs.lean`) rather than the net protocol library (a program may keep the
network's resources in its own protocol), and each machine's boot program is safe by the same
`wp_main` lemmas as `echo_crash_safety` (`Results.lean`).

The theorem without restarts is weaker than `echo_crash_robust` (every machine may crash and
restart), from which it also follows by `Robust.of_all_crashing` (a run with no crashing machine is
a run in which every machine may crash: `distCrashNsteps_more_boots`); it is proved through the
bridge to show the bridge applies to a real system.
-/
module

public import Net.Statement.DistBridge
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.Results

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness

namespace github_com.mit_pdos.etcd_grove.examples.net.echo

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

/-- The deployment's addresses: the server's. -/
def echoAddrs : List GoString := [srvAddr]

set_option linter.unusedVariables false in
/-- **echo as a distributed deployment**: the three machines, none of which crashes, deployed with the address
`echoAddrs` (`DistDeploy`), are robust: in every execution, of any length, no thread of any machine
is stuck and none has an unrecovered panic. -/
theorem echo_dist_robust [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [srv_sem : cmd.server.Assumptions] [cli_sem : cmd.client.Assumptions]
    [junk_sem : cmd.junk.Assumptions] [go.BasicIntoValInj]
    (σs σc σj : state) (g : GlobalState) (threads bound : Nat) :
    DistDeploy echoAddrs (system σs σc σj) g → Robust [] (system σs σc σj) g threads bound := by
  refine robust_of_distBoot _ _ g threads bound ?_
  intro G
  iintro Hs
  unfold echoAddrs
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hu, -⟩
  unfold addrUnset addrTok
  icases Hu with ⟨Hpend, %Hok, Htk⟩
  imod echoInvs_alloc (Gg := G) $$ Hpend Htk with ⟨%γm, #Hinvs⟩
  imodintro
  iexists fun _ => iprop(echoInvs (Gg := G) γm ∗ ⌜addrOk srvAddr = true⌝)
  isplitr
  · ipureintro
    intro i m hm hG hGG hctx
    obtain ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    dsimp only at hGG hctx
    subst hGG hctx
    letI hG : HeapGS .hasLC netGF := ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    match i, hm with
    | 0, hm =>
      cases hm
      dsimp only
      iintro ⟨#Hinvs, #Hplan⟩ Hgs
      rw [show boot_server = boot cmd.server.initialize' cmd.server.main from rfl]
      iapply wp_boot cmd.server.initialize' cmd.server.main _ cmd.server.getIsPkgInit
          (cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf) _
          (cmd.server.wp_main net.Listen.wp_proof net.Listener.Accept.wp_proof
            (wire.ReadFull.wp_proof net.Conn.Read.wp_proof) net.Conn.Write.wp_proof
            net.Conn.Close.wp_proof γm) $$ [] Hgs
      iframe Hinvs Hplan
    | 1, hm =>
      cases hm
      dsimp only
      iintro ⟨#Hinvs, #Hplan⟩ Hgs
      rw [show boot_client = boot cmd.client.initialize' cmd.client.main from rfl]
      iapply wp_boot cmd.client.initialize' cmd.client.main _ cmd.client.getIsPkgInit
          (cmd.client.wp_initialize' _ cmd.client.getIsPkgInit_wf) _
          (cmd.client.wp_main wire.wp_RandomBytes net.Dial.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
            net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm) $$ [] Hgs
      iframe Hinvs Hplan
    | 2, hm =>
      cases hm
      dsimp only
      iintro ⟨#Hinvs, #Hplan⟩ Hgs
      rw [show boot_junk = boot cmd.junk.initialize' cmd.junk.main from rfl]
      iapply wp_boot cmd.junk.initialize' cmd.junk.main _ cmd.junk.getIsPkgInit
          (cmd.junk.wp_initialize' _ cmd.junk.getIsPkgInit_wf) _
          (cmd.junk.wp_main wire.wp_RandomInt wire.wp_RandomBytes net.Dial.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
            net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm) $$ [] Hgs
      iframe Hinvs Hplan
  · dsimp only
    ihave #HP : iprop(echoInvs (Gg := G) γm ∗ ⌜addrOk srvAddr = true⌝) $$ []
    · iframe Hinvs
      ipureintro; exact Hok
    simp only [system]
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

#print axioms echo_dist_robust

end github_com.mit_pdos.etcd_grove.examples.net.echo

end Perennial
