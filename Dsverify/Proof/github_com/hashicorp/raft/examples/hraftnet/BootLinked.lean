/-
**The machines' boot: `hraftnet`'s first initialization, proved** (notes/dsv-hraft.md, "The boot"; as
craq's `BootLinked.lean`). A linking module: it composes the initializers' proofs.

Every command imports `hraftnet` only, whose initializer runs, innermost first, snapstore's (and
raft's), then net/rpc's, its first run on the machine (Net's `net.rpc.wp_init_first`, given Net's
proved `NewServer.spec_owned`; net/rpc's initializer runs net/http's by net/http's `wp_initialize'`),
then raft's, `errors`, remote's, `service`'s, `rpctransport`'s, ... (initialized already, or not
owning anything). The two packages whose first run hands the machine owned resources, `hraftnet` and
net/rpc, are initialized here for the first time, from a table (`gOff S G`, `BootTable.lean`) in which
they are not initialized yet: `boot_hraftnet` returns net/rpc's codec unregistered (`codecUnset`,
`rpcFirstRes`'s; the rest of it, `DefaultServer`'s registry, the kit does not use), and so does every
command's boot (`BootCmdsLinked.lean`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.BootTable
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Init
public import Net.Proof.net.rpc.InitFirst
public import Net.Proof.net.rpc.Results
public import Proof.runtime.PkgInitFirst

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.hashicorp.raft.examples.hraftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

local notation "hraftPkg" => pkg_id.github_com.hashicorp.raft.examples.hraftnet

/-- The tables of the boot (`gOff S G`): `S1` before `hraftnet`'s first run, `SR` before net/rpc's. -/
abbrev bootS1 : List GoString := [hraftPkg, pkg_id.net.rpc]
abbrev bootSR : List GoString := [pkg_id.net.rpc]

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
variable [examples.hraftnet.Assumptions] [π : NetProtoGS]

variable {G : GoString → IProp GF} (hk : KitG G)
include hk

set_option maxHeartbeats 8000000 in
/-- **`hraftnet`'s first initialization**: through net/rpc's first run, net/rpc's codec unregistered. -/
theorem boot_hraftnet :
    {{ ownInitializing (gOff bootS1 G) }}
      (App (Val examples.hraftnet.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) hraftPkg ∗ net.rpc.codecUnset }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_first (gA := gOff bootS1 G) (gB := gOff bootSR G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_hashicorp_raft_examples_hraftnet) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  wp_apply github_com.hashicorp.raft.examples.snapstore.wp_initialize' _
    (wfO_github_com_hashicorp_raft_examples_snapstore hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hn0⟩
  try wp_auto
  wp_apply (net.rpc.wp_init_first net.rpc.NewServer.wp_owned (gOff bootSR G) G
      (gOff_off _ _ _ (by decide)) (wf_net_rpc hk)
      (fun p h => (gOff_ne _ _ _ (by simp [bootSR, h])).symm)) $$ Hown
    as ⟨Hown, #Hrp, Hres⟩
  try wp_auto
  wp_apply github_com.hashicorp.raft.wp_initialize' _ (wf_github_com_hashicorp_raft hk) $$ Hown as ⟨Hown, #Hg0⟩
  try wp_auto
  wp_apply errors.wp_initialize' _ (wf_errors hk) $$ Hown as ⟨Hown, #Hg1⟩
  try wp_auto
  wp_apply github_com.mit_pdos.etcd_grove.examples.lib.remote.wp_initialize' _
    (wf_github_com_mit_pdos_etcd_grove_examples_lib_remote hk) $$ Hown as ⟨Hown, #Hg2⟩
  try wp_auto
  wp_apply github_com.hashicorp.raft.examples.hraftnet.service.wp_initialize' _
    (wf_github_com_hashicorp_raft_examples_hraftnet_service hk) $$ Hown as ⟨Hown, #Hg3⟩
  try wp_auto
  wp_apply github_com.hashicorp.raft.examples.hraftnet.rpctransport.wp_initialize' _
    (wf_github_com_hashicorp_raft_examples_hraftnet_rpctransport hk) $$ Hown as ⟨Hown, #Hg4⟩
  try wp_auto
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ (wf_github_com_goose_lang_primitive hk)
    $$ Hown as ⟨Hown, #Hg5⟩
  try wp_auto
  wp_apply github_com.anishathalye.porcupine.wp_initialize' _ (wf_github_com_anishathalye_porcupine hk)
    $$ Hown as ⟨Hown, #Hg6⟩
  try wp_auto
  wp_apply time.wp_initialize' _ (wf_time hk) $$ Hown as ⟨Hown, #Hg7⟩
  try wp_auto
  wp_apply strconv.wp_initialize' _ (wf_strconv hk) $$ Hown as ⟨Hown, #Hg8⟩
  try wp_auto
  wp_apply net.wp_initialize' _ (wf_net hk) $$ Hown as ⟨Hown, #Hg9⟩
  try wp_auto
  wp_apply io.wp_initialize' _ (wf_io hk) $$ Hown as ⟨Hown, #Hg10⟩
  try wp_auto
  iunfold net.rpc.rpcFirstRes at Hres
  icases Hres with ⟨Hcu, -⟩
  iframe Hown Hcu
  try (isplitr; · ipureintro; exact isPanic_intoVal ())
  is_pkg_init_finish

end boot

end Perennial.github_com.hashicorp.raft.examples.hraftnet
