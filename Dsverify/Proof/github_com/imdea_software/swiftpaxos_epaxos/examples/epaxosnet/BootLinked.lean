/-
**The server machines' boot: the owned packages' first initializations, proved** (notes/dsv-epaxos.md,
the boot; as dsv-swiftpaxos's `BootLinked.lean`). A linking module: it composes the initializers'
proofs.

Every server command imports `epaxosnet` only, whose initializer runs, innermost first, `errors`,
porcupine, remote, `state`, `defs`, then `master` (whose initializer runs net/rpc's, the first run of
net/rpc and of net/http, inside it, on the machine), then `epaxos`, ... . The packages whose first
run hands the machine owned resources are initialized here for the first time, from a table
(`gOff S G`, `BootTable.lean`) in which they are not initialized yet:
* `master`'s returns, through net/rpc's first run (`RpcFirstInit`, `RpcBoot.lean`), net/rpc's boot
  resources (`rpcBootRes`);
* `epaxosnet`'s returns them, and every server command's (`BootCmdsLinked.lean`) too.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.BootTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.RpcBoot
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Init
public import Proof.runtime.PkgInitFirst
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.imdea_software.swiftpaxos_epaxos

attribute [local instance] GooseGlobalGS.gooseInvGS

local notation "epnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
local notation "masterPkg" => pkg_id.github_com.imdea_software.swiftpaxos_epaxos.master

/-- The tables of the boot (`gOff S G`): `S1` before `epaxosnet`'s first run, `S2` before
`master`'s, `SR` before net/rpc's. -/
abbrev bootS1 : List GoString := [epnetPkg, masterPkg, pkg_id.net.rpc, pkg_id.net.http]
abbrev bootS2 : List GoString := [masterPkg, pkg_id.net.rpc, pkg_id.net.http]
abbrev bootSR : List GoString := [pkg_id.net.rpc, pkg_id.net.http]

/-- A machine's empty package state is `ownInitializing` of any table. -/
theorem ownInitializing_of_empty [GooseExts] [GooseSemantics] [GooseInterp]
    [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
    (g : GoString → IProp GF) :
    ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ ⊢ ownInitializing g := by
  rw [ownInitializing_unseal]
  unfold ownInitializingDef
  iintro Hg
  iexists ∅
  iframe Hg
  iintro !>
  iapply BigSepM.bigSepM_empty.2
  iempintro

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [examples.epaxosnet.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions]
variable [RpcFirstInit (GF := GF)]

variable {G : GoString → IProp GF} (hk : KitG G)
include hk

set_option maxHeartbeats 4000000 in
/-- `master`'s first initialization: through net/rpc's first run, net/rpc's boot resources. -/
theorem boot_master :
    {{ ownInitializing (gOff bootS2 G) }}
      (App (Val github_com.imdea_software.swiftpaxos_epaxos.master.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) masterPkg ∗ rpcBootRes }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_first (gA := gOff bootS2 G) (gB := gOff bootSR G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_imdea_software_swiftpaxos_epaxos_master) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos_epaxos.replica.defs.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_epaxos_replica_defs hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hm0⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos_epaxos.dlog.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_epaxos_dlog hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hm1⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos_epaxos.config.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_epaxos_config hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hm2⟩
  try wp_auto
  wp_apply time.wp_initialize' _ (wfO_time hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hm3⟩
  try wp_auto
  wp_apply sync.wp_initialize' _ (wfO_sync hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hm4⟩
  try wp_auto
  wp_apply (RpcFirstInit.wp_init_first (gOff bootSR G) G (gOff_off _ _ _ (by decide))
        (gOff_off _ _ _ (by decide)) (wf_net_rpc hk)
        (fun p h1 h2 => (gOff_ne _ _ _ (by simp [bootSR, h1, h2])).symm)) $$ Hown
    as ⟨Hown, #Hm5, HR⟩
  try wp_auto
  wp_apply net.http.wp_initialize' _ (wf_net_http hk) $$ Hown as ⟨Hown, #Hm5h⟩
  try wp_auto
  wp_apply net.wp_initialize' _ (wf_net hk) $$ Hown as ⟨Hown, #Hm6⟩
  try wp_auto
  wp_apply fmt.wp_initialize' _ (wf_fmt hk) $$ Hown as ⟨Hown, #Hm7⟩
  try wp_auto
  wp_apply errors.wp_initialize' _ (wf_errors hk) $$ Hown as ⟨Hown, #Hm8⟩
  try wp_auto
  iframe Hown HR
  try (isplitr; · ipureintro; exact isPanic_intoVal ())
  is_pkg_init_finish

set_option maxHeartbeats 8000000 in
/-- **`epaxosnet`'s first initialization**: through `master`'s, the machine's net/rpc boot
resources. -/
theorem boot_epaxosnet :
    {{ ownInitializing (gOff bootS1 G) }}
      (App (Val examples.epaxosnet.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) epnetPkg ∗ rpcBootRes }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_first (gA := gOff bootS1 G) (gB := gOff bootS2 G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_imdea_software_swiftpaxos_epaxos_examples_epaxosnet) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  wp_apply errors.wp_initialize' _ (wfO_errors hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hn0⟩
  try wp_auto
  wp_apply github_com.anishathalye.porcupine.wp_initialize' _ (wfO_github_com_anishathalye_porcupine hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hn1⟩
  try wp_auto
  wp_apply github_com.mit_pdos.etcd_grove.examples.lib.remote.wp_initialize' _ (wfO_github_com_mit_pdos_etcd_grove_examples_lib_remote hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hn2⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos_epaxos.state.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_epaxos_state hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hn3⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos_epaxos.replica.defs.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_epaxos_replica_defs hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hn4⟩
  try wp_auto
  wp_apply boot_master hk $$ Hown as ⟨Hown, #Hn5, HR⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos_epaxos.epaxos.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_epaxos_epaxos hk) $$ Hown as ⟨Hown, #Hg0⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos_epaxos.dlog.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_epaxos_dlog hk) $$ Hown as ⟨Hown, #Hg1⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos_epaxos.config.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_epaxos_config hk) $$ Hown as ⟨Hown, #Hg2⟩
  try wp_auto
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ (wf_github_com_goose_lang_primitive hk) $$ Hown as ⟨Hown, #Hg3⟩
  try wp_auto
  wp_apply time.wp_initialize' _ (wf_time hk) $$ Hown as ⟨Hown, #Hg4⟩
  try wp_auto
  wp_apply net.rpc.wp_initialize' _ (wf_net_rpc hk) $$ Hown as ⟨Hown, #Hg5⟩
  try wp_auto
  wp_apply net.http.wp_initialize' _ (wf_net_http hk) $$ Hown as ⟨Hown, #Hg6⟩
  try wp_auto
  wp_apply net.wp_initialize' _ (wf_net hk) $$ Hown as ⟨Hown, #Hg7⟩
  try wp_auto
  wp_apply encoding.binary.wp_initialize' _ (wf_encoding_binary hk) $$ Hown as ⟨Hown, #Hg8⟩
  try wp_auto
  wp_apply bufio.wp_initialize' _ (wf_bufio hk) $$ Hown as ⟨Hown, #Hg9⟩
  try wp_auto
  iframe Hown HR
  try (isplitr; · ipureintro; exact isPanic_intoVal ())
  is_pkg_init_finish

end boot

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
