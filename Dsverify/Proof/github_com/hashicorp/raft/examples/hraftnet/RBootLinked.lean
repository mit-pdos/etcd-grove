/-
**The restartable server machines' boot: `rserver`'s first initialization, proved** (hraft_robust;
notes/dsv-hraft.md, "The boot"; as `BootLinked.lean`'s `boot_hraftnet`). A linking module: it
composes the initializers' proofs.

Every command `cmd/rserverj` imports `rserver` only, whose initializer runs, innermost first,
durable's (over `os`, `path/filepath`: initialized as any package, the file system's extension is
not touched), `service`'s, then `rpctransport`'s, whose initializer runs net/rpc's first run on the
machine (Net's `net.rpc.wp_init_first`, given Net's proved `NewServer.spec_owned`), then the disk's,
`hraftnet`'s (net/rpc initialized by then: an ordinary initialization), raft's, .... The packages
whose first run is proved here, `rserver`, `rpctransport` and net/rpc, are initialized from a table
(`gOff S G`, `rserver/BootTable.lean`) in which they are not initialized yet: `boot_rserver` returns
net/rpc's codec unregistered (`codecUnset`, `rpcFirstRes`'s), and so does every command's boot
(`RBootCmdsLinked.lean`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rserver.BootTable
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rserver.Init
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.BootLinked
public import Net.Proof.net.rpc.InitFirst
public import Net.Proof.net.rpc.Results
public import Proof.runtime.PkgInitFirst

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.hashicorp.raft.examples.hraftnet.rserver

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

local notation "rserverPkg" => pkg_id.github_com.hashicorp.raft.examples.hraftnet.rserver
local notation "rpctPkg" => pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-- The tables of the boot (`gOff S G`): `S1` before `rserver`'s first run, `ST` before
`rpctransport`'s, `SR` before net/rpc's. -/
abbrev bootS1 : List GoString := [rserverPkg, rpctPkg, pkg_id.net.rpc]
abbrev bootST : List GoString := [rpctPkg, pkg_id.net.rpc]
abbrev bootSR : List GoString := [pkg_id.net.rpc]

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [examples.hraftnet.rserver.Assumptions] [π : NetProtoGS]

variable {G : GoString → IProp GF} (hk : rserver.KitG G)
include hk

set_option maxHeartbeats 8000000 in
/-- **`rpctransport`'s first initialization**: through net/rpc's first run, net/rpc's codec
unregistered. -/
theorem boot_rpctransport :
    {{ ownInitializing (rserver.gOff bootST G) }}
      (App (Val examples.hraftnet.rpctransport.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) rpctPkg ∗ net.rpc.codecUnset }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_first (gA := rserver.gOff bootST G) (gB := rserver.gOff bootSR G) (gC := G)
    (hA := rserver.gOff_off _ _ _ (by decide)) (hAB := rserver.gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_hashicorp_raft_examples_hraftnet_rpctransport) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  wp_apply github_com.hashicorp.raft.examples.snapstore.wp_initialize' _
    (rserver.wfO_github_com_hashicorp_raft_examples_snapstore hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hg0⟩
  try wp_auto
  wp_apply github_com.hashicorp.raft.wp_initialize' _
    (rserver.wfO_github_com_hashicorp_raft hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hg1⟩
  try wp_auto
  wp_apply time.wp_initialize' _ (rserver.wfO_time hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hg2⟩
  try wp_auto
  wp_apply sync.wp_initialize' _ (rserver.wfO_sync hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hg3⟩
  try wp_auto
  wp_apply (net.rpc.wp_init_first net.rpc.NewServer.wp_owned (rserver.gOff bootSR G) G
      (rserver.gOff_off _ _ _ (by decide)) (rserver.wf_net_rpc hk)
      (fun p h => (rserver.gOff_ne _ _ _ (by simp [bootSR, h])).symm)) $$ Hown
    as ⟨Hown, #Hrp, Hres⟩
  try wp_auto
  wp_apply net.wp_initialize' _ (rserver.wf_net hk) $$ Hown as ⟨Hown, #Hg4⟩
  try wp_auto
  wp_apply io.wp_initialize' _ (rserver.wf_io hk) $$ Hown as ⟨Hown, #Hg5⟩
  try wp_auto
  wp_apply errors.wp_initialize' _ (rserver.wf_errors hk) $$ Hown as ⟨Hown, #Hg6⟩
  try wp_auto
  iunfold net.rpc.rpcFirstRes at Hres
  icases Hres with ⟨Hcu, -⟩
  iframe Hown Hcu
  try (isplitr; · ipureintro; exact isPanic_intoVal ())
  is_pkg_init_finish

set_option maxHeartbeats 8000000 in
/-- **`rserver`'s first initialization**: through `rpctransport`'s, net/rpc's codec unregistered. -/
theorem boot_rserver :
    {{ ownInitializing (rserver.gOff bootS1 G) }}
      (App (Val examples.hraftnet.rserver.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) rserverPkg ∗ net.rpc.codecUnset }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_first (gA := rserver.gOff bootS1 G) (gB := rserver.gOff bootST G) (gC := G)
    (hA := rserver.gOff_off _ _ _ (by decide)) (hAB := rserver.gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_hashicorp_raft_examples_hraftnet_rserver) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  wp_apply github_com.mit_pdos.etcd_grove.examples.lib.durable.wp_initialize' _
    (rserver.wfO_github_com_mit_pdos_etcd_grove_examples_lib_durable hk bootST (by decide)) $$ Hown
    as ⟨Hown, #Hg0⟩
  try wp_auto
  wp_apply github_com.hashicorp.raft.examples.hraftnet.service.wp_initialize' _
    (rserver.wfO_github_com_hashicorp_raft_examples_hraftnet_service hk bootST (by decide)) $$ Hown
    as ⟨Hown, #Hg1⟩
  try wp_auto
  wp_apply boot_rpctransport hk $$ Hown as ⟨Hown, #Hg2, Hcu⟩
  try wp_auto
  wp_apply github_com.hashicorp.raft.examples.hraftnet.disk.wp_initialize' _
    (rserver.wf_github_com_hashicorp_raft_examples_hraftnet_disk hk) $$ Hown as ⟨Hown, #Hg3⟩
  try wp_auto
  wp_apply net.rpc.wp_initialize' _ (rserver.wf_net_rpc hk) $$ Hown as ⟨Hown, #Hg4⟩
  try wp_auto
  wp_apply io.wp_initialize' _ (rserver.wf_io hk) $$ Hown as ⟨Hown, #Hg5⟩
  try wp_auto
  wp_apply github_com.hashicorp.raft.examples.hraftnet.wp_initialize' _
    (rserver.wf_github_com_hashicorp_raft_examples_hraftnet hk) $$ Hown as ⟨Hown, #Hg6⟩
  try wp_auto
  wp_apply github_com.hashicorp.raft.wp_initialize' _ (rserver.wf_github_com_hashicorp_raft hk) $$ Hown
    as ⟨Hown, #Hg7⟩
  try wp_auto
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ (rserver.wf_github_com_goose_lang_primitive hk)
    $$ Hown as ⟨Hown, #Hg8⟩
  try wp_auto
  wp_apply time.wp_initialize' _ (rserver.wf_time hk) $$ Hown as ⟨Hown, #Hg9⟩
  try wp_auto
  wp_apply strconv.wp_initialize' _ (rserver.wf_strconv hk) $$ Hown as ⟨Hown, #Hg10⟩
  try wp_auto
  wp_apply net.wp_initialize' _ (rserver.wf_net hk) $$ Hown as ⟨Hown, #Hg11⟩
  try wp_auto
  iframe Hown Hcu
  try (isplitr; · ipureintro; exact isPanic_intoVal ())
  is_pkg_init_finish

end boot

end Perennial.github_com.hashicorp.raft.examples.hraftnet.rserver
