/-
**The client and server machines' boot: `craqnet`'s first initialization, proved** (notes/dsv-craq.md,
the boot; as dsv-epaxos's `BootLinked.lean`). A linking module: it composes the initializers'
proofs.

Every client and server command imports `craqnet` only, whose initializer runs, innermost first,
`transport`, `errors`, remote, primitive, then `transport/netrpc`'s (whose initializer runs
net/rpc's, the first run of net/rpc and of net/http on the machine: Net's
`net.rpc.wp_init_first_http`, given Net's proved `NewServer.spec_owned`, on a machine of at most
`2 ^ 30` threads, `Threads30`), then go-craq's other packages, ... . The packages whose first run
hands the machine owned resources are initialized here for the first time, from a table (`gOff S
G`, `BootTable.lean`) in which they are not initialized yet: `boot_netrpc` and `boot_craqnet`
return the machine's net/rpc boot resources (`rpcBootRes`), and so does every command's boot
(`BootCmdsLinked.lean`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.BootTable
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.KitSpecs
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Init
public import Net.Proof.net.rpc.InitFirst
public import Net.Proof.net.http.InitFirst
public import Net.Proof.net.rpc.Results
public import Proof.runtime.PkgInitFirst

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.despreston.go_craq.examples.craqnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

local notation "craqPkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

local notation "netrpcPkg" => pkg_id.github_com.despreston.go_craq.transport.netrpc

/-- The tables of the boot (`gOff S G`): `S1` before `craqnet`'s first run, `S2` before
`transport/netrpc`'s, `SR` before net/rpc's. -/
abbrev bootS1 : List GoString := [craqPkg, netrpcPkg, pkg_id.net.rpc, pkg_id.net.http]
abbrev bootS2 : List GoString := [netrpcPkg, pkg_id.net.rpc, pkg_id.net.http]
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

/-- The machine's thread bound, as net/http's first initialization needs it (a class, so that the
commands' generated boots take it; the top-level proof gives it from `Robust`'s `2 ^ 30`). -/
class Threads30 [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors}
    [hG : HeapGS HasLC.hasLC GF] : Prop where
  le : threadBound GF ≤ 2 ^ 30

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [examples.craqnet.Assumptions] [π : NetProtoGS]
variable [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions]
variable [Threads30 (GF := GF)]

variable {G : GoString → IProp GF} (hk : KitG G)
include hk

set_option maxHeartbeats 4000000 in
/-- `transport/netrpc`'s first initialization: through net/rpc's (and net/http's) first run, the
machine's net/rpc boot resources. -/
theorem boot_netrpc :
    {{ ownInitializing (gOff bootS2 G) }}
      (App (Val github_com.despreston.go_craq.transport.netrpc.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) netrpcPkg ∗ rpcBootRes }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_first (gA := gOff bootS2 G) (gB := gOff bootSR G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_despreston_go_craq_transport_netrpc) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  wp_apply (net.rpc.wp_init_first_http net.rpc.NewServer.wp_owned (gOff bootSR G) G
      (gOff_off _ _ _ (by decide)) (gOff_off _ _ _ (by decide)) (wf_net_rpc hk)
      (fun p h1 h2 => (gOff_ne _ _ _ (by simp [bootSR, h1, h2])).symm)) $$ [Hown]
    as ⟨Hown, #Hrp, Hres, #Hht, Hmux, -⟩
  · iframe Hown; ipureintro; exact Threads30.le
  try wp_auto
  wp_apply github_com.despreston.go_craq.transport.wp_initialize' _ (wf_github_com_despreston_go_craq_transport hk) $$ Hown as ⟨Hown, #Hc0⟩
  try wp_auto
  ihave #Hri := net.rpc.rpcInit_access $$ Hrp
  ihave #He := net.http.httpEnv_access $$ Hht
  iunfold net.rpc.rpcInit at Hri
  icases Hri with ⟨-, #Hsrv, #Hcon, #Hmu⟩
  iunfold net.rpc.rpcFirstRes at Hres
  icases Hres with ⟨Hcu, Hds⟩
  ihave HR : rpcBootRes $$ [Hmux Hcu Hds]
  · unfold rpcBootRes codecFresh defaultSrvFresh
    iframe Hmu Hcu Hsrv He Hcon Hmux Hds
  iframe Hown HR
  try (isplitr; · ipureintro; exact isPanic_intoVal ())
  is_pkg_init_finish

set_option maxHeartbeats 8000000 in
/-- **`craqnet`'s first initialization**: through `transport/netrpc`'s, the machine's net/rpc boot
resources. -/
theorem boot_craqnet :
    {{ ownInitializing (gOff bootS1 G) }}
      (App (Val examples.craqnet.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) craqPkg ∗ rpcBootRes }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_first (gA := gOff bootS1 G) (gB := gOff bootS2 G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_despreston_go_craq_examples_craqnet) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  wp_apply github_com.despreston.go_craq.transport.wp_initialize' _ (wfO_github_com_despreston_go_craq_transport hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hn0⟩
  try wp_auto
  wp_apply errors.wp_initialize' _ (wfO_errors hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hn1⟩
  try wp_auto
  wp_apply github_com.mit_pdos.etcd_grove.examples.lib.remote.wp_initialize' _ (wfO_github_com_mit_pdos_etcd_grove_examples_lib_remote hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hn2⟩
  try wp_auto
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ (wfO_github_com_goose_lang_primitive hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hn3⟩
  try wp_auto
  wp_apply boot_netrpc hk $$ Hown as ⟨Hown, #Hn4, HR⟩
  try wp_auto
  wp_apply github_com.despreston.go_craq.store.kv.wp_initialize' _ (wf_github_com_despreston_go_craq_store_kv hk) $$ Hown as ⟨Hown, #Hg0⟩
  try wp_auto
  wp_apply github_com.despreston.go_craq.node.wp_initialize' _ (wf_github_com_despreston_go_craq_node hk) $$ Hown as ⟨Hown, #Hg1⟩
  try wp_auto
  wp_apply github_com.despreston.go_craq.coordinator.wp_initialize' _ (wf_github_com_despreston_go_craq_coordinator hk) $$ Hown as ⟨Hown, #Hg2⟩
  try wp_auto
  wp_apply github_com.anishathalye.porcupine.wp_initialize' _ (wf_github_com_anishathalye_porcupine hk) $$ Hown as ⟨Hown, #Hg3⟩
  try wp_auto
  wp_apply time.wp_initialize' _ (wf_time hk) $$ Hown as ⟨Hown, #Hg4⟩
  try wp_auto
  wp_apply sync.wp_initialize' _ (wf_sync hk) $$ Hown as ⟨Hown, #Hg5⟩
  try wp_auto
  wp_apply net.rpc.wp_initialize' _ (wf_net_rpc hk) $$ Hown as ⟨Hown, #Hg6⟩
  try wp_auto
  wp_apply net.http.wp_initialize' _ (wf_net_http hk) $$ Hown as ⟨Hown, #Hg7⟩
  try wp_auto
  wp_apply net.wp_initialize' _ (wf_net hk) $$ Hown as ⟨Hown, #Hg8⟩
  try wp_auto
  wp_apply math.rand.wp_initialize' _ (wf_math_rand hk) $$ Hown as ⟨Hown, #Hg11⟩
  try wp_auto
  wp_apply log.wp_initialize' _ (wf_log hk) $$ Hown as ⟨Hown, #Hg9⟩
  try wp_auto
  wp_apply io.wp_initialize' _ (wf_io hk) $$ Hown as ⟨Hown, #Hg10⟩
  try wp_auto
  iframe Hown HR
  try (isplitr; · ipureintro; exact isPanic_intoVal ())
  is_pkg_init_finish

end boot

end Perennial.github_com.despreston.go_craq.examples.craqnet
