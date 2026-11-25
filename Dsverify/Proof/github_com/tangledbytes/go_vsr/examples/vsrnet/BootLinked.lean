/-
**The vr kit's boot: encoding/json's first initialization on a machine, proved** (notes/dsv-vr.md,
"Round 7", the boot; as swiftpaxos's `BootLinked.lean`). A linking module: it composes the
initializers' proofs.

Every command imports `vsrnet` only, whose initializer runs, innermost first, go-vsr's `time`,
then `replica`, whose initializer runs `time`, `queue`, then `network`, whose initializer runs
`queue`, `assert`, `sync`, `net`, `log/slog`, `errors`, then **encoding/json**: the first package
on that path whose import closure contains encoding/json, so encoding/json's first run on the
machine is there. It allocates the registry (`codec`, nil; `codecMu`, an unlocked mutex) and
initializes `io` and `sync`; its first run hands the machine encoding/json's fresh registry
(`codecFresh`: `codecMu`'s mutex over `codecInv`, `codec`'s other half at nil), which `network`'s,
`replica`'s, `vsrnet`'s and every command's first runs pass on (`BootCmdsLinked.lean`), and which
the kit's `RegisterJSON()` takes (`KitLib.lean`). The packages of that path (`ownedPkgs`,
`BootTable.lean`) are initialized here for the first time, from a table (`gOff S G`) in which they
are not initialized yet; the others by their generated `wp_initialize'`, before the path's call
at `gOff S G` (their closures avoid the path) and after it at `G`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.BootTable
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Init
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.jsonlib
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.InitFirst

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.imdea_software.swiftpaxos (wp_package_init_first)

local notation "vsrnetPkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet
local notation "replicaPkg" => pkg_id.github_com.tangledbytes.go_vsr.pkg.replica
local notation "networkPkg" => pkg_id.github_com.tangledbytes.go_vsr.pkg.network
local notation "jsonPkg" => pkg_id.encoding.json

/-- The tables of the boot (`gOff S G`): `S1` before `vsrnet`'s first run, `S2` before
`replica`'s, `S3` before `network`'s, `S4` before encoding/json's. -/
abbrev bootS1 : List GoString := [vsrnetPkg, replicaPkg, networkPkg, jsonPkg]
abbrev bootS2 : List GoString := [replicaPkg, networkPkg, jsonPkg]
abbrev bootS3 : List GoString := [networkPkg, jsonPkg]
abbrev bootS4 : List GoString := [jsonPkg]

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
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]

variable {G : GoString → IProp GF} (hk : KitG G)
include hk

set_option goose.wp.extras true

/-- **encoding/json's first initialization**: the registry allocated, `codecMu`'s mutex made over
`codecInv` (half of `codec`'s nil), the other half returned: `codecFresh`. -/
theorem boot_json :
    {{ ownInitializing (gOff bootS4 G) }}
      (App (Val encoding.json.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) jsonPkg ∗
        encoding.json.codecFresh (GF := GF) }} := by
  wp_start as Hown
  iapply wp_package_init_first (gA := gOff bootS4 G) (gB := G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_le _ _)
    (heq := hk.e_encoding_json) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := _) encoding.json.codec _ as Hcodec
  wp_apply wp_GlobalAlloc (V := _) encoding.json.codecMu _ as HcodecMu
  wp_apply io.wp_initialize' _ (wf_io hk) $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply sync.wp_initialize' _ (wf_sync hk) $$ Hown as ⟨Hown, #Hd1⟩
  try wp_auto
  icases (typedPointsto_half_split (globalAddr encoding.json.codec) (null : Loc) 1).1 $$ Hcodec
    with ⟨Hh1, Hh2⟩
  imod (sync.init_Mutex (GF := GF) encoding.json.codecInv ⊤ (globalAddr encoding.json.codecMu))
    $$ HcodecMu [Hh1] with #Hmu
  · inext
    unfold encoding.json.codecInv
    iexists null
    iexact Hh1
  imodintro
  iframe Hown
  isplitl [Hh2]
  · unfold encoding.json.codecFresh encoding.json.codecUnset
    iframe Hmu
    iexact Hh2
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  is_pkg_init_finish

/-- `network`'s first initialization: its body as the generated one, encoding/json's run the
first (`boot_json`); returns `codecFresh`. -/
theorem boot_network :
    {{ ownInitializing (gOff bootS3 G) }}
      (App (Val pkg.network.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) networkPkg ∗
        encoding.json.codecFresh (GF := GF) }} := by
  wp_start as Hown
  iapply wp_package_init_first (gA := gOff bootS3 G) (gB := gOff bootS4 G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_tangledbytes_go_vsr_pkg_network) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) pkg.network.ErrNoConn _ as HErrNoConn
  wp_apply pkg.queue.wp_initialize' _
    (wfO_github_com_tangledbytes_go_vsr_pkg_queue hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply pkg.assert.wp_initialize' _
    (wfO_github_com_tangledbytes_go_vsr_pkg_assert hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply sync.wp_initialize' _ (wfO_sync hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply net.wp_initialize' _ (wfO_net hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply log.slog.wp_initialize' _ (wfO_log_slog hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply errors.wp_initialize' _ (wfO_errors hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply boot_json hk $$ Hown as ⟨Hown, #Hd4, HR⟩
  wp_apply pkg.ipv4port.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_pkg_ipv4port hk)
    $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply pkg.events.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_pkg_events hk)
    $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply io.wp_initialize' _ (wf_io hk) $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrNoConn
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrNoConn ⟨#SErrNoConn, #MErrNoConn⟩
  try wp_auto
  ipersist HErrNoConn
  iframe Hown HR
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  iunfold _root_.Perennial.errors.newVar
  iexists xErrNoConn
  iframe HErrNoConn SErrNoConn MErrNoConn

/-- `replica`'s first initialization: its body as the generated one, `network`'s run the first
(`boot_network`); returns `codecFresh`. -/
theorem boot_replica :
    {{ ownInitializing (gOff bootS2 G) }}
      (App (Val pkg.replica.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) replicaPkg ∗
        encoding.json.codecFresh (GF := GF) }} := by
  wp_start as Hown
  iapply wp_package_init_first (gA := gOff bootS2 G) (gB := gOff bootS3 G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_tangledbytes_go_vsr_pkg_replica) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply pkg.time.wp_initialize' _
    (wfO_github_com_tangledbytes_go_vsr_pkg_time hk bootS3 (by decide)) $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply pkg.queue.wp_initialize' _
    (wfO_github_com_tangledbytes_go_vsr_pkg_queue hk bootS3 (by decide)) $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply boot_network hk $$ Hown as ⟨Hown, #Hd9, HR⟩
  wp_apply pkg.log.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_pkg_log hk)
    $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply pkg.ipv4port.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_pkg_ipv4port hk)
    $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply pkg.events.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_pkg_events hk)
    $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply pkg.assert.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_pkg_assert hk)
    $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply sort.wp_initialize' _ (wf_sort hk) $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply math.wp_initialize' _ (wf_math hk) $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply log.slog.wp_initialize' _ (wf_log_slog hk) $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply io.wp_initialize' _ (wf_io hk) $$ Hown as ⟨Hown, #Hd1⟩
  try wp_auto
  iframe Hown HR
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  is_pkg_init_finish

/-- **`vsrnet`'s first initialization**: its body as the generated one, `replica`'s run the first
(`boot_replica`); returns `codecFresh`. -/
theorem boot_vsrnet :
    {{ ownInitializing (gOff bootS1 G) }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp GF) vsrnetPkg ∗
        encoding.json.codecFresh (GF := GF) }} := by
  wp_start as Hown
  iapply wp_package_init_first (gA := gOff bootS1 G) (gB := gOff bootS2 G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_tangledbytes_go_vsr_examples_vsrnet) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply pkg.time.wp_initialize' _
    (wfO_github_com_tangledbytes_go_vsr_pkg_time hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply boot_replica hk $$ Hown as ⟨Hown, #Hd16, HR⟩
  wp_apply pkg.network.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_pkg_network hk)
    $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply pkg.client.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_pkg_client hk)
    $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply examples.vsrwire.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_examples_vsrwire hk)
    $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply examples.vsrkv.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_examples_vsrkv hk)
    $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply github_com.mit_pdos.etcd_grove.examples.lib.remote.wp_initialize' _
    (wf_github_com_mit_pdos_etcd_grove_examples_lib_remote hk) $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply github_com.goose_lang.primitive.wp_initialize' _
    (wf_github_com_goose_lang_primitive hk) $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply github_com.anishathalye.porcupine.wp_initialize' _
    (wf_github_com_anishathalye_porcupine hk) $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply time.wp_initialize' _ (wf_time hk) $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply net.wp_initialize' _ (wf_net hk) $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply log.slog.wp_initialize' _ (wf_log_slog hk) $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply io.wp_initialize' _ (wf_io hk) $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply pkg.log.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_pkg_log hk)
    $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply pkg.events.wp_initialize' _ (wf_github_com_tangledbytes_go_vsr_pkg_events hk)
    $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply encoding.json.wp_initialize' _ (wf_encoding_json hk) $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply models_lab.jsoncodec.wp_initialize' _ (wf_models_lab_jsoncodec hk)
    $$ Hown as ⟨Hown, #Hd1⟩
  try wp_auto
  iframe Hown HR
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  is_pkg_init_finish

end boot

end Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet
