/-
The probe proved end to end (M2c; `notes/harness-m2a.md`, "M2c result"): `SafeDist` for the
probe's two nodes (node 0 runs `ClientMain`, node 1 `ServerMain`, as under the rig:
`harness/netprobe/rig.toml`) and the rig's configuration (`probeCfg`: node `i` at
10.77.0.(10+i), the server's endpoint 10.77.0.11:7000).

* `wp_initialize'`: the package's initializer (`net`'s, then `time`'s).
* `wp_boot_client`, `wp_boot_server`: each node's boot program (initialize, then call its main
  function) from the extension's resources it needs: the client the protocols of the server's
  address, the server also the address's token.
* `netprobe_safeDist`: `safeDist_of_boot` (`Harness/SafeDist.lean`), whose obligation is
  discharged by setting the protocols of the configured address to `echoProto`
  (`addrs_set_proto`) and giving its token to the server node; each node's `BootWp` is its boot
  WP.
-/
module

public import Harness.SafeDist
public import Harness.Proof.dsverify_lab.harness.netprobe.Client
public import Harness.Proof.dsverify_lab.harness.netprobe.Server
public import Perennial.Proof.io.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn Dsv

namespace dsverify_lab.harness.netprobe

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : netprobe.Assumptions] [model_sem : net.model.Assumptions]

set_option goose.wp.extras true in
/-- The package's initialization: it initializes its imports (`net`, `time`). -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.dsverify_lab.harness.netprobe get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.dsverify_lab.harness.netprobe }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply time.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Htime⟩
  wp_apply net.initialize'.wp_proof time.wp_initialize' io.wp_initialize' _ Hinit.2.1 $$ Hown
    as ⟨Hown, #Hnet⟩
  iframe Hown
  is_pkg_init_finish

/-- The `get_is_pkg_init` of a boot program: every package `netprobe` imports, transitively. -/
def getIsPkgInit (p : GoString) : IProp GF :=
  if p = pkg_id.dsverify_lab.harness.netprobe then
    isPkgInit (PROP := IProp GF) pkg_id.dsverify_lab.harness.netprobe
  else if p = pkg_id.net then isPkgInit (PROP := IProp GF) pkg_id.net
  else if p = pkg_id.time then isPkgInit (PROP := IProp GF) pkg_id.time
  else if p = pkg_id.io then isPkgInit (PROP := IProp GF) pkg_id.io
  else if p = pkg_id.errors then isPkgInit (PROP := IProp GF) pkg_id.errors
  else if p = pkg_id.sync then isPkgInit (PROP := IProp GF) pkg_id.sync
  else if p = pkg_id.sync.atomic then isPkgInit (PROP := IProp GF) pkg_id.sync.atomic
  else if p = pkg_id.internal.race then isPkgInit (PROP := IProp GF) pkg_id.internal.race
  else if p = pkg_id.internal.synctest then isPkgInit (PROP := IProp GF) pkg_id.internal.synctest
  else iprop(True)

theorem getIsPkgInit_wf :
    GetIsPkgInitProp (PROP := IProp GF) pkg_id.dsverify_lab.harness.netprobe
      (getIsPkgInit (GF := GF)) := by
  repeat' (first | exact trivial | constructor)
  done

/-- From no package initialized, initialize the package. -/
theorem wp_boot_init (Φ : val → IProp GF) :
    ⊢ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      (isPkgInit (PROP := IProp GF) pkg_id.dsverify_lab.harness.netprobe -∗ Φ #()) -∗
      WP (App (Val initialize') (Val #())) {{ Φ }} := by
  iintro Hgs HΦ
  wp_apply wp_initialize' getIsPkgInit getIsPkgInit_wf $$ [Hgs] as ⟨-, #Hpkg⟩
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  iapply HΦ $$ Hpkg

end init

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : netprobe.Assumptions] [model_sem : net.model.Assumptions]

/-- The client node's boot program. -/
theorem wp_boot_client :
    ⊢ addrProto (GF := GF) serverAddr echoProto echoProto -∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      WP (boot initialize' ClientMain) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro #Hpr Hgs
  unfold boot
  wp_apply wp_boot_init $$ Hgs
  iintro #Hpkg
  wp_pures
  wp_apply wp_ClientMain $$ [$Hpkg $Hpr]
  ipureintro; rfl

/-- The server node's boot program. -/
theorem wp_boot_server :
    ⊢ addrTok (GF := GF) serverAddr -∗ addrProto serverAddr echoProto echoProto -∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      WP (boot initialize' ServerMain) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro Htok #Hpr Hgs
  unfold boot
  wp_apply wp_boot_init $$ Hgs
  iintro #Hpkg
  wp_pures
  wp_apply wp_ServerMain $$ [$Hpkg $Htok $Hpr]
  ipureintro; rfl

end boot

/-! ## The nodes, the configuration, the theorem -/

attribute [local instance] netConnExts netConnExtsSemantics netConnExtsInterp
  GooseGlobalGS.gooseInvGS netConnExts_has

section dist
variable [GoGlobalContext]

/-- A node's assumptions on its Go context: the package's generated ones and the `net`
model's trusted layouts. -/
def nodeAssumptions [GoLocalContext] [GoSemanticsFunctions] : Prop :=
  netprobe.Assumptions ∧ net.model.Assumptions

/-- Node 0: the client node. -/
def clientNode : Node where
  Assumptions := nodeAssumptions
  init := initialize'
  main := ClientMain

/-- Node 1: the server node. -/
def serverNode : Node where
  Assumptions := nodeAssumptions
  init := initialize'
  main := ServerMain

/-- The rig's configuration (`harness/rig/README.md`): node `i` at 10.77.0.(10+i); the server
listens on port 7000 of node 1. -/
def probeCfg : NetConfig :=
  ⟨[⟨10, 77, 0, 10⟩, ⟨10, 77, 0, 11⟩], [⟨⟨10, 77, 0, 11⟩, 7000⟩]⟩

theorem probeCfg_wf : probeCfg.WellFormed 2 := by decide

theorem probeCfg_addrs : probeCfg.addrs = [serverAddr] := by decide

/-- **The probe's safety**: in every execution of the client node and the server node, from a
start where each has its Go context, no package initialized and one thread, and the network
has the configured address and no listener or connection, no node panics, no thread is stuck,
and a finished main thread returned. In particular the client's `check` passes: the echo is a
prefix of the message, whatever the network does (breaks, timeouts, failures) within the
model. -/
theorem netprobe_safeDist : SafeDist [clientNode, serverNode] probeCfg := by
  apply safeDist_of_boot _ _ probeCfg_wf
  intro G
  rw [probeCfg_addrs]
  iintro Hs
  imod addrs_set_proto (fun _ => echoProto) (fun _ => echoProto) _ $$ Hs with
    ⟨⟨Htok, -⟩, ⟨#Hpr, -⟩⟩
  imodintro
  iexists (fun i => match i with
    | 0 => addrProto serverAddr echoProto echoProto
    | _ => iprop(addrTok serverAddr ∗ addrProto serverAddr echoProto echoProto))
  isplitr
  · ipureintro
    rintro (_ | _ | i) nd h <;> simp at h <;> subst h <;> intro hG s hGG ⟨_, _⟩ <;> subst hGG <;>
      simp only [clientNode, serverNode, Node.boot_mk]
    · iintro #Hpr Hgs; iapply wp_boot_client $$ Hpr Hgs
    · iintro ⟨Htok, #Hpr⟩ Hgs; iapply wp_boot_server $$ Htok Hpr Hgs
  iapply BigSepL.bigSepL_cons.2; isplitl []; · simp only; iexact Hpr
  iapply BigSepL.bigSepL_cons.2; simp only; iframe Htok Hpr
  iapply BigSepL.bigSepL_nil.2; iempintro

end dist

end dsverify_lab.harness.netprobe

end Perennial
