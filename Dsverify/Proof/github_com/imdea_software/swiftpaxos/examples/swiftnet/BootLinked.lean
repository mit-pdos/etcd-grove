/-
**The kit's boot: the owned packages' first initializations, proved** (notes/dsv-swiftpaxos.md,
"State (thirteenth session)", the boot; the lab's `SrvInit.lean` (`init_cmap_first`,
`init_client_first`, `init_swift_first`, `swiftnetInitSrv_first`), retargeted at the kit over
remote, as dsv-gryff's `wp_gryff_own`). A linking module: it composes the initializers' proofs.

Every command imports `swiftnet` only, whose initializer runs, innermost first, `errors`, remote,
`swift` (whose closure runs `concurrent-map`'s and `client`'s, and `client`'s runs net/rpc's,
the first run of net/rpc and net/http on the machine), then `defs`, `master`, ... . The kit's
packages whose first run hands the machine owned resources are initialized here for the first
time, from a table (`gOff S G`, `BootTable.lean`) in which they are not initialized yet:
* `concurrent-map`'s returns `SHARD_COUNT ↦ 32`;
* `client`'s returns the node's fresh ghost (`client.ghostFresh`), and, through net/rpc's first
  run (`RpcFirstInit`, a premise), net/rpc's boot resources (`rpcBootRes`);
* `swift`'s returns those and `MaxDescRoutines ↦ 100`, `useFastAckPool ↦ false`
  (`swift.mutGlobalsInit`, with `SHARD_COUNT`);
* `swiftnet`'s returns them (`bootRes`), and every command's (`cmd/*`: `bootCmd`) too.
`client`'s second run (from `swiftnet`'s own import list) finds it initialized: `init_client`
(its generic initialization, which keeps nothing).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.BootTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.InitFirst
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcBoot
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Pkg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.hook.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.Init
public import Dsverify.Proof.bufio.Init
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.slices.Link
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.crypto.sha256.Link
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.NewVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet
local notation "swiftPkg" => pkg_id.github_com.imdea_software.swiftpaxos.swift
local notation "cmapPkg" => pkg_id.github_com.orcaman.concurrent_map
local notation "clientPkg" => pkg_id.github_com.imdea_software.swiftpaxos.client

/-- The tables of the boot (`gOff S G`): `S1` before `swiftnet`'s first run, `S2` before
`swift`'s, `S3` before `concurrent-map`'s, `S4` before `client`'s, `SR` before net/rpc's. -/
abbrev bootS1 : List GoString :=
  [swiftnetPkg, swiftPkg, cmapPkg, clientPkg, pkg_id.net.rpc, pkg_id.net.http]
abbrev bootS2 : List GoString := [swiftPkg, cmapPkg, clientPkg, pkg_id.net.rpc, pkg_id.net.http]
abbrev bootS3 : List GoString := [cmapPkg, clientPkg, pkg_id.net.rpc, pkg_id.net.http]
abbrev bootS4 : List GoString := [clientPkg, pkg_id.net.rpc, pkg_id.net.http]
abbrev bootSR : List GoString := [pkg_id.net.rpc, pkg_id.net.http]

/-- A machine's empty package state is `ownInitializing` of any table. -/
theorem ownInitializing_of_empty [go_gctx : GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF]
    (g : GoString → IProp netDistGF) :
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
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [log.Assumptions] [net.http.Assumptions]
variable [math.rand.InitHyp netDistGF] [net.rpc.InitHyp netDistGF] [net.http.InitHyp netDistGF]
variable [encoding.gob.InitHyp netDistGF]
variable [os.signal.InitHyp netDistGF] [github_com.google.uuid.InitHyp netDistGF]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF] [RpcFirstInit (GF := netDistGF)]

/-- A machine's boot resources: the node's fresh ghost, the mutable globals at their initial
values, net/rpc's boot resources. -/
def bootRes : IProp netDistGF :=
  iprop(client.ghostFresh ∗ swift.mutGlobalsInit ∗ rpcBootRes)

variable {G : GoString → IProp netDistGF} (hk : KitG G)
include hk

set_option goose.wp.extras true

/-- `concurrent-map`'s first initialization: `SHARD_COUNT ↦ 32`, owned. -/
theorem boot_cmap :
    {{ ownInitializing (gOff bootS3 G) }}
      (App (Val github_com.orcaman.concurrent_map.initialize') (Val #()))
    {{ RET #(); ownInitializing (gOff bootS4 G) ∗ isPkgInit (PROP := IProp netDistGF) cmapPkg ∗
        typedPointsto (globalAddr github_com.orcaman.concurrent_map.SHARD_COUNT) (W64 32)
          (DFrac.own 1) }} := by
  wp_start as Hown
  iapply wp_package_init_first (gA := gOff bootS3 G) (gB := gOff bootS4 G) (gC := gOff bootS4 G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := (gOff_ne _ _ _ (by decide)).trans hk.e_github_com_orcaman_concurrent_map) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := w64) github_com.orcaman.concurrent_map.SHARD_COUNT go.int as H_SHARD_COUNT
    | wp_apply sync.wp_initialize' _ (wfO_sync hk bootS4 (by decide)) $$ Hown as ⟨Hown, #H1⟩
    | wp_apply encoding.json.wp_initialize' _ (wfO_encoding_json hk bootS4 (by decide)) $$ Hown as ⟨Hown, #H2⟩
    | wp_auto)
  iframe Hown
  isplitl [H_SHARD_COUNT]
  · iexact H_SHARD_COUNT
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  is_pkg_init_finish

omit hk in
/-- `NewGhost()` (GHOST): a new ghost, its mutex at its zero value, its prophecy fresh. -/
theorem client_wp_NewGhost :
    {{ True }} (App (Val (@! github_com.imdea_software.swiftpaxos.client.NewGhost)) (Val #()))
    {{ (g : Loc), RET #g; ∃ (p : proph_id) (pvs : List val), ⌜g ≠ null⌝ ∗
        structFieldRef github_com.imdea_software.swiftpaxos.client.Ghost go!"p" g ↦ p ∗
        structFieldRef github_com.imdea_software.swiftpaxos.client.Ghost go!"mu" g ↦
          (zero_val sync.Mutex) ∗ proph p pvs }} := by
  wp_start as -
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_NewProph as %pvs %p Hp
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamed «$r0»
  iapply HΦ
  iexists p, pvs
  iframe
  ipureintro; exact Hnn

set_option hygiene false in
local macro "client_pre_G" : tactic => `(tactic| (
  wp_apply wp_GlobalAlloc (V := Loc) github_com.imdea_software.swiftpaxos.client.nodeGhost (go.GoType.PointerType github_com.imdea_software.swiftpaxos.client.Ghost.ty) as H_nodeGhost
  try wp_auto
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ (wf_github_com_goose_lang_primitive hk) $$ Hown as ⟨Hown, #Hc0⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.rpc.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_rpc hk) $$ Hown as ⟨Hown, #Hc1⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.dlog.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_dlog hk) $$ Hown as ⟨Hown, #Hc2⟩
  try wp_auto
  wp_apply strings.wp_initialize' _ (wf_strings hk) $$ Hown as ⟨Hown, #Hc3⟩
  try wp_auto))

set_option hygiene false in
local macro "client_pre_R" : tactic => `(tactic| (
  wp_apply wp_GlobalAlloc (V := Loc) github_com.imdea_software.swiftpaxos.client.nodeGhost (go.GoType.PointerType github_com.imdea_software.swiftpaxos.client.Ghost.ty) as H_nodeGhost
  try wp_auto
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ (wfO_github_com_goose_lang_primitive hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hc0⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.rpc.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_rpc hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hc1⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.dlog.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_dlog hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hc2⟩
  try wp_auto
  wp_apply strings.wp_initialize' _ (wfO_strings hk bootSR (by decide)) $$ Hown as ⟨Hown, #Hc3⟩
  try wp_auto))

set_option hygiene false in
local macro "client_post" : tactic => `(tactic| (
  wp_apply fmt.wp_initialize' _ (wf_fmt hk) $$ Hown as ⟨Hown, #Hc10⟩
  try wp_auto
  wp_apply encoding.binary.wp_initialize' _ (wf_encoding_binary hk) $$ Hown as ⟨Hown, #Hc11⟩
  try wp_auto
  wp_apply bufio.wp_initialize' _ (wf_bufio hk) $$ Hown as ⟨Hown, #Hc12⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.state.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_state hk) $$ Hown as ⟨Hown, #Hc13⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.replica.defs.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_replica_defs hk) $$ Hown as ⟨Hown, #Hc14⟩
  try wp_auto
  wp_apply github_com.google.uuid.wp_initialize' _ (wf_github_com_google_uuid hk) $$ Hown as ⟨Hown, #Hc15⟩
  try wp_auto
  wp_apply time.wp_initialize' _ (wf_time hk) $$ Hown as ⟨Hown, #Hc16⟩
  try wp_auto
  wp_apply sync.wp_initialize' _ (wf_sync hk) $$ Hown as ⟨Hown, #Hc17⟩
  try wp_auto
  wp_apply net.wp_initialize' _ (wf_net hk) $$ Hown as ⟨Hown, #Hc18⟩
  try wp_auto
  wp_apply math.rand.wp_initialize' _ (wf_math_rand hk) $$ Hown as ⟨Hown, #Hc19⟩
  try wp_auto
  wp_apply errors.wp_initialize' _ (wf_errors hk) $$ Hown as ⟨Hown, #Hc20⟩
  try wp_auto
  wp_apply client_wp_NewGhost as %g ⟨%p, %pvs, %Hgn, Hgp, Hgmu, Hpr⟩
  try wp_auto))

set_option maxHeartbeats 4000000 in
/-- `client`'s initialization when it is not its first (`swiftnet` imports it after `swift`):
its package fact is `True`, and the ghost a run would make is dropped. -/
theorem init_client :
    {{ ownInitializing G }}
      (App (Val github_com.imdea_software.swiftpaxos.client.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp netDistGF) clientPkg }} := by
  wp_start as Hown
  iapply wp_package_init (heq := hk.e_github_com_imdea_software_swiftpaxos_client) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  client_pre_G
  wp_apply net.rpc.wp_initialize' _ (wf_net_rpc hk) $$ Hown as ⟨Hown, #H13⟩
  try wp_auto
  client_post
  iclear Hgp Hgmu Hpr H_nodeGhost
  iframe Hown
  is_pkg_init_finish

set_option maxHeartbeats 4000000 in
/-- `client`'s first initialization (net/rpc's first run inside it, `RpcFirstInit`): the node's
fresh ghost and net/rpc's boot resources. -/
theorem boot_client :
    {{ ownInitializing (gOff bootS4 G) }}
      (App (Val github_com.imdea_software.swiftpaxos.client.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp netDistGF) clientPkg ∗
        client.ghostFresh ∗ rpcBootRes }} := by
  wp_start as Hown
  iapply wp_package_init_first (gA := gOff bootS4 G) (gB := gOff bootSR G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_imdea_software_swiftpaxos_client) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  iapply wp_fupd
  try wp_auto
  client_pre_R
  wp_apply (RpcFirstInit.wp_init_first (gOff bootSR G) G (gOff_off _ _ _ (by decide))
        (gOff_off _ _ _ (by decide)) (wf_net_rpc hk) (wf_net_http hk)
            (fun p h1 h2 => (gOff_ne _ _ _ (by simp [bootSR, h1, h2])).symm)) $$ Hown
        as ⟨Hown, #H13, Hrb⟩
  try wp_auto
  client_post
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ H_nodeGhost with #HnG
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ Hgp with #Hgp
  imodintro
  iframe Hown Hrb
  isplitl [Hpr Hgmu]
  · iunfold client.ghostFresh
    iexists g, p, pvs
    iframe HnG Hgp Hpr Hgmu
    ipureintro; exact Hgn
  is_pkg_init_finish

set_option maxHeartbeats 8000000 in
/-- `swift`'s first initialization: the mutable globals at their initial values and, through
`concurrent-map`'s and `client`'s first initializations, `SHARD_COUNT`, the node's fresh ghost and
net/rpc's boot resources. -/
theorem boot_swift :
    {{ ownInitializing (gOff bootS2 G) }}
      (App (Val github_com.imdea_software.swiftpaxos.swift.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp netDistGF) swiftPkg ∗ bootRes }} := by
  wp_start as Hown
  iapply wp_package_init_first (gA := gOff bootS2 G) (gB := gOff bootS3 G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_imdea_software_swiftpaxos_swift) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  iapply wp_fupd
  try wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := GoFunc) github_com.imdea_software.swiftpaxos.swift.ReplyHook _ as H_ReplyHook
    | wp_apply wp_GlobalAlloc (V := GoFunc) github_com.imdea_software.swiftpaxos.swift.SyncHook _ as H_SyncHook
    | wp_apply wp_GlobalAlloc (V := GoFunc) github_com.imdea_software.swiftpaxos.swift.ExecHook _ as H_ExecHook
    | wp_apply wp_GlobalAlloc (V := sync.Pool) github_com.imdea_software.swiftpaxos.swift.fastAckPool sync.Pool.ty as H_fastAckPool
    | wp_apply wp_GlobalAlloc (V := Bool) github_com.imdea_software.swiftpaxos.swift.useFastAckPool go.bool as H_useFastAckPool
    | wp_apply wp_GlobalAlloc (V := w64) github_com.imdea_software.swiftpaxos.swift.MaxDescRoutines go.int as H_MaxDescRoutines
    | wp_apply wp_GlobalAlloc (V := GoInterface) github_com.imdea_software.swiftpaxos.swift.errVarintOverflow go.error as H_errVarintOverflow
    | wp_auto)
  wp_apply errors.wp_initialize' _ (wfO_errors hk bootS3 (by decide)) $$ Hown as ⟨Hown, #Hs0⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.hook.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_hook hk bootS3 (by decide)) $$ Hown as ⟨Hown, #Hs1⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.dlog.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_dlog hk bootS3 (by decide)) $$ Hown as ⟨Hown, #Hs2⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.config.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_config hk bootS3 (by decide)) $$ Hown as ⟨Hown, #Hs3⟩
  try wp_auto
  wp_apply sync.atomic.wp_initialize' _ (wfO_sync_atomic hk bootS3 (by decide)) $$ Hown as ⟨Hown, #Hs4⟩
  try wp_auto
  wp_apply boot_cmap hk $$ Hown as ⟨Hown, #Hcm, Hsc⟩
  try wp_auto
  wp_apply log.wp_initialize' _ (wfO_log hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs5⟩
  try wp_auto
  wp_apply encoding.binary.wp_initialize' _ (wfO_encoding_binary hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs6⟩
  try wp_auto
  wp_apply slices.wp_initialize' _ (wfO_slices hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs7⟩
  try wp_auto
  wp_apply crypto.sha256.wp_initialize' _ (wfO_crypto_sha256 hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hsha⟩
  try wp_auto
  wp_apply bytes.wp_initialize' _ (wfO_bytes hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs8⟩
  try wp_auto
  wp_apply time.wp_initialize' _ (wfO_time hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs9⟩
  try wp_auto
  wp_apply sync.wp_initialize' _ (wfO_sync hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs10⟩
  try wp_auto
  wp_apply io.wp_initialize' _ (wfO_io hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs11⟩
  try wp_auto
  wp_apply fmt.wp_initialize' _ (wfO_fmt hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs12⟩
  try wp_auto
  wp_apply encoding.gob.wp_initialize' _ (wfO_encoding_gob hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs13⟩
  try wp_auto
  wp_apply bufio.wp_initialize' _ (wfO_bufio hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs14⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.state.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_state hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs15⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.replica.defs.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_replica_defs hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs16⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.replica.wp_initialize' _ (wfO_github_com_imdea_software_swiftpaxos_replica hk bootS4 (by decide)) $$ Hown as ⟨Hown, #Hs17⟩
  try wp_auto
  wp_apply boot_client hk $$ Hown as ⟨Hown, #Hcl, Hfr, Hrb⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.rpc.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_rpc hk) $$ Hown as ⟨Hown, #Hrp⟩
  repeat (first
    | wp_apply errors.wp_New_errorString as %xE #EE
    | wp_auto
    | (wp_func_lits; wp_auto))
  imod sync.init_Pool (globalAddr swift.fastAckPool)
      { noCopy' := zeroValDef, local' := null, localSize' := 0, victim' := null, victimSize' := 0,
        New' := _ } iprop(True) swift.fastAckP ⊤ rfl $$ [H_fastAckPool] with #Hpool
  · isplitl [H_fastAckPool]
    · iexact H_fastAckPool
    unfold sync.newSpec
    iright
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    isplitr []
    · unfold swift.fastAckP
      iexists _, _
      iframe
      ipureintro; rfl
    itrivial
  ipersist H_ReplyHook
  ipersist H_SyncHook
  ipersist H_ExecHook
  ipersist H_errVarintOverflow
  imodintro
  iframe Hown
  isplitl [H_MaxDescRoutines H_useFastAckPool Hsc Hfr Hrb]
  · unfold bootRes swift.mutGlobalsInit
    iframe
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  is_pkg_init_finish
  unfold swift.pkgSt errors.newVar
  iframe H_ReplyHook H_SyncHook H_ExecHook
  isplitl
  · iexists _
    iframe H_errVarintOverflow EE
  · iexists _
    iframe Hpool
    ipureintro; intro hf; cases hf

set_option maxHeartbeats 8000000 in
/-- **`swiftnet`'s first initialization**: through `swift`'s, the machine's boot resources. -/
theorem boot_swiftnet :
    {{ ownInitializing (gOff bootS1 G) }}
      (App (Val examples.swiftnet.initialize') (Val #()))
    {{ RET #(); ownInitializing G ∗ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ bootRes }} := by
  wp_start as Hown
  iapply wp_package_init_first (gA := gOff bootS1 G) (gB := gOff bootS2 G) (gC := G)
    (hA := gOff_off _ _ _ (by decide)) (hAB := gOff_sub _ _ _ (by decide))
    (heq := hk.e_github_com_imdea_software_swiftpaxos_examples_swiftnet) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  wp_apply errors.wp_initialize' _ (wfO_errors hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hn0⟩
  try wp_auto
  wp_apply github_com.mit_pdos.etcd_grove.examples.lib.remote.wp_initialize' _ (wfO_github_com_mit_pdos_etcd_grove_examples_lib_remote hk bootS2 (by decide)) $$ Hown as ⟨Hown, #Hn1⟩
  try wp_auto
  wp_apply boot_swift hk $$ Hown as ⟨Hown, #Hn2, HR⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.replica.defs.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_replica_defs hk) $$ Hown as ⟨Hown, #Hg0⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.master.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_master hk) $$ Hown as ⟨Hown, #Hg1⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.dlog.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_dlog hk) $$ Hown as ⟨Hown, #Hg2⟩
  try wp_auto
  wp_apply github_com.imdea_software.swiftpaxos.config.wp_initialize' _ (wf_github_com_imdea_software_swiftpaxos_config hk) $$ Hown as ⟨Hown, #Hg3⟩
  try wp_auto
  wp_apply init_client hk $$ Hown as ⟨Hown, #Hg4⟩
  try wp_auto
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ (wf_github_com_goose_lang_primitive hk) $$ Hown as ⟨Hown, #Hg5⟩
  try wp_auto
  wp_apply github_com.anishathalye.porcupine.wp_initialize' _ (wf_github_com_anishathalye_porcupine hk) $$ Hown as ⟨Hown, #Hg6⟩
  try wp_auto
  wp_apply time.wp_initialize' _ (wf_time hk) $$ Hown as ⟨Hown, #Hg7⟩
  try wp_auto
  wp_apply sync.wp_initialize' _ (wf_sync hk) $$ Hown as ⟨Hown, #Hg8⟩
  try wp_auto
  wp_apply strings.wp_initialize' _ (wf_strings hk) $$ Hown as ⟨Hown, #Hg9⟩
  try wp_auto
  wp_apply net.rpc.wp_initialize' _ (wf_net_rpc hk) $$ Hown as ⟨Hown, #Hg10⟩
  try wp_auto
  wp_apply net.http.wp_initialize' _ (wf_net_http hk) $$ Hown as ⟨Hown, #Hg11⟩
  try wp_auto
  wp_apply net.wp_initialize' _ (wf_net hk) $$ Hown as ⟨Hown, #Hg12⟩
  try wp_auto
  wp_apply math.rand.wp_initialize' _ (wf_math_rand hk) $$ Hown as ⟨Hown, #Hg13⟩
  try wp_auto
  wp_apply log.wp_initialize' _ (wf_log hk) $$ Hown as ⟨Hown, #Hg14⟩
  try wp_auto
  wp_apply io.wp_initialize' _ (wf_io hk) $$ Hown as ⟨Hown, #Hg15⟩
  try wp_auto
  wp_apply fmt.wp_initialize' _ (wf_fmt hk) $$ Hown as ⟨Hown, #Hg16⟩
  try wp_auto
  iframe Hown HR
  is_pkg_init_finish

end boot

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
