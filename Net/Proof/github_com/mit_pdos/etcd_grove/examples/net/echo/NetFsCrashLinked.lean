/-
`examples/net/echo` with its server on a machine that crashes and restarts and its client on one that
never crashes, over the network and Linux files together (`[netExt, fsExt]`, `kvnetExts`): the
minimal instance of the bridge `robust_of_netFsBoot` (`Net/Statement/NetFsBridge.lean`, etcd-dist
stage D3), the check that it applies to a real system. (It proves the implication only; that its
premise `NetFsDeploy` is satisfiable is argued in `notes/dist-crash-bridge.md`, not proved here.)

Two machines: the crashing `[(boot_serverNF, σs)]` and the stable `[(boot_clientNF, σc)]` (echo's
commands `cmd/server` and `cmd/client`, `TopLevelDefs.lean`), the address `[SrvAddr]` (valid:
`decide`). The proof is `echo_dist_robust`'s (`RobustLinked.lean`), over `kvnetExts`: from `SrvAddr`
unset, echo's protocol (`echoInvs`, `Defs.lean`), which is global ghost state and so survives the
server's crashes; the server's precondition in a generation is the protocol and its empty package
state, which every crash gives back (the file system's crash rest is not needed: the server keeps
nothing on disk); each program is safe by the same `wp_main` lemmas. The programs are proved over any
extensions with the net extension (`[HasExt netExt]`), so nothing of echo's proof changes.

The theorem is weaker than `echo_crash_robust` (every machine may crash, over `[netExt]` alone), and
says nothing of files; it is here to show the bridge closes over a deployment with both kinds of
machine and both extensions, with no axiom beyond Lean's and the extensions' (`#print axioms`).
-/
module

public import Net.Statement.NetFsBridge
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.TopLevelDefs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.server.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.server.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.client.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.client.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Dial
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net NetFs Robustness

namespace github_com.mit_pdos.etcd_grove.examples.net.echo

attribute [local instance] kvnetExts kvnetExtsSemantics kvnetExtsInterp kvnetExtsCrashInterp
  kvnetExts_hasNet kvnetExts_hasFs GooseGlobalGS.gooseInvGS

/-- A command's boot program over `[netExt, fsExt]` (`TopLevelDefs.lean`'s `boot`, which is over
`[netExt]`: a program's syntax is over its list of extensions): run its package's initializer `init`,
then call its `main`. -/
def bootNF [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The server machine's program: the command `cmd/server`. -/
abbrev boot_serverNF [GoGlobalContext] : Expr := bootNF cmd.server.initialize' cmd.server.main

/-- The client machine's program: the command `cmd/client`. -/
abbrev boot_clientNF [GoGlobalContext] : Expr := bootNF cmd.client.initialize' cmd.client.main

section
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A command's boot program is safe (`Results.lean`'s `wp_boot`, over `[netExt, fsExt]`). -/
theorem wp_bootNF [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    (init : val) (main pkg : GoString) [IsPkgInit (IProp GF) pkg] (getIs : GoString → IProp GF)
    (Hinit : {{ ownInitializing getIs }}
        (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getIs ∗ isPkgInit (PROP := IProp GF) pkg }})
    (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF) pkg ∗ P }}
        (App (Val (@! main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP (bootNF init main) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold bootNF
  wp_apply Hinit $$ [Hgs] as ⟨-, #Hpkg⟩
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  wp_pures
  wp_apply Hf $$ [HP]
  · iframe
  ipureintro; rfl

end

set_option linter.unusedVariables false in
/-- **echo with a crashing server, over the network and files**: the server's machine may crash at
any step and restart, the client's never crashes; deployed with the address `[SrvAddr]` and every
machine's files as on disk (`NetFsDeploy`), in every execution of fewer than `bound` steps along
which every machine keeps fewer than `threads` threads, no thread of either machine is stuck and
none has an unrecovered panic: the client's check (the reply it read in full is its request) holds
however often the server crashes. -/
theorem echo_netfs_mixed_robust [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [srv_sem : cmd.server.Assumptions] [cli_sem : cmd.client.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (σs σc : state) (g : GlobalState) (threads bound : Nat) :
    NetFsDeploy [srvAddr] [(boot_serverNF, σs)] [(boot_clientNF, σc)] g →
      Robust [(boot_serverNF, σs)] [(boot_clientNF, σc)] g threads bound := by
  refine robust_of_netFsBoot (GF := kvnetGF) _ _ _ g threads bound ?_
  intro G _
  iintro Hs
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hu, -⟩
  unfold addrUnset addrTok
  icases Hu with ⟨Hpend, %Hok, Htk⟩
  imod echoInvs_alloc (Gg := G) $$ Hpend Htk with ⟨%γm, #Hinvs⟩
  imodintro
  iexists fun _ L => iprop(echoInvs (Gg := G) γm ∗ ⌜addrOk srvAddr = true⌝ ∗
    ownGoState (hG := L.goose_go_stateGS) ∅)
  iexists fun _ => iprop(echoInvs (Gg := G) γm ∗ ⌜addrOk srvAddr = true⌝)
  isplitr
  · -- the server, in every generation
    ipureintro
    intro i m hm L hL
    match i, hm with
    | 0, hm =>
      cases hm
      subst hL
      dsimp only
      letI hG : HeapGS .hasLC kvnetGF := ⟨G, L⟩
      iintro ⟨#Hinvs, #Hplan, Hgs⟩ -
      imodintro
      isplitl [Hgs]
      · rw [show boot_serverNF = bootNF cmd.server.initialize' cmd.server.main from rfl]
        iapply wp_bootNF cmd.server.initialize' cmd.server.main _ cmd.server.getIsPkgInit
            (cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf) _
            (cmd.server.wp_main net.Listen.wp_proof net.Listener.Accept.wp_proof
              (wire.ReadFull.wp_proof net.Conn.Read.wp_proof) net.Conn.Write.wp_proof
              net.Conn.Close.wp_proof γm) $$ [] Hgs
        iframe Hinvs Hplan
      · -- after a crash: the protocol is global, the package state is the new generation's
        iintro %L' %V' - - - Hgs' -
        imodintro
        iframe Hinvs Hplan Hgs'
  isplitr
  · -- the client
    ipureintro
    intro j m hm L hL
    match j, hm with
    | 0, hm =>
      cases hm
      subst hL
      dsimp only
      letI hG : HeapGS .hasLC kvnetGF := ⟨G, L⟩
      iintro ⟨#Hinvs, #Hplan⟩ - Hgs -
      imodintro
      rw [show boot_clientNF = bootNF cmd.client.initialize' cmd.client.main from rfl]
      iapply wp_bootNF cmd.client.initialize' cmd.client.main _ cmd.client.getIsPkgInit
          (cmd.client.wp_initialize' _ cmd.client.getIsPkgInit_wf) _
          (cmd.client.wp_main net.Dial.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
            net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm) $$ [] Hgs
      iframe Hinvs Hplan
  isplitl []
  · -- the server's first generation
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · iintro %L %_ - Hgs
      imodintro
      dsimp only
      iframe Hinvs Hgs
      ipureintro; exact Hok
    iapply BigSepL.bigSepL_nil.2
    iempintro
  · -- the client's share
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · dsimp only
      iframe Hinvs
      ipureintro; exact Hok
    iapply BigSepL.bigSepL_nil.2
    iempintro

#print axioms echo_netfs_mixed_robust

end github_com.mit_pdos.etcd_grove.examples.net.echo

end Perennial
