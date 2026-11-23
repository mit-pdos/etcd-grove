/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientPkgInits.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The initializers of the packages the test package imports that no proof covers yet: the
SwiftPaxos packages (`client`, `config`, `dlog`, `master`, `replica/defs`, `replica`, `swift`,
`state`, `rpc`, `hook`), the `gods` and `concurrent-map` models and the lab's `encoding/gob`
model, at the run's package states (`pkgStates`' fields are `True`: each initializer
allocates and sets its globals and keeps nothing; except the gob model's, `encoding.gob.isInit`). Each chains its imports' initializers
(Perennial's and the harness's proved ones) as `driver.wp_initialize'` does.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.PkgState
public import Perennial.Proof.crypto.sha256
public import Perennial.Proof.strconv
public import Perennial.Proof.encoding.binary
public import Perennial.Proof.sort
public import Perennial.Proof.slices.Link
public import Perennial.Proof.math
public import Perennial.Proof.bytes
public import Perennial.Proof.errors
public import Perennial.Proof.github_com.goose_lang.primitive.Link

-- PORT: lab imports dropped: Harness.Proof.os, Harness.Proof.os.signal, Harness.Proof.syscall, Harness.Proof.encoding.json, Harness.Proof.encoding.hex, Harness.Proof.uuid.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace adapter

section inits
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions]

/-- The run's package states (`pkgStates`) at this heap. -/
local instance pkgStI : SwiftNetPkgState netDistGF := @pkgStates _ netDistGF hG sem

set_option goose.wp.extras true

local notation "wp_io" => (io.wp_initialize' (GF := netDistGF) (hG := hG))
local notation "wp_errors" => (errors.wp_initialize' (GF := netDistGF) (hG := hG))
local notation "wp_time" => (time.wp_initialize' (GF := netDistGF) (hG := hG))
local notation "wp_sync" => (sync.wp_initialize' (GF := netDistGF) (hG := hG))
local notation "wp_net" => (net.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_time wp_io)
local notation "wp_bufio" => (bufio.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_io wp_errors)
local notation "wp_http" => (net.http.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_sync wp_net wp_errors wp_bufio)
local notation "wp_rpc" => (net.rpc.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_http wp_sync wp_net wp_errors)
local notation "wp_json" => (encoding.json.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_sync wp_io)

theorem init_utils : InitSpec pkg_id.github_com.emirpasic.gods.utils github_com.emirpasic.gods.utils.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  repeat (first
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  iframe Hown
  is_pkg_init_finish
  all_goals (unfold pkgStI pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial))

theorem init_treemap : InitSpec pkg_id.github_com.emirpasic.gods.maps.treemap github_com.emirpasic.gods.maps.treemap.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  repeat (first
    | wp_apply init_utils _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  iframe Hown
  is_pkg_init_finish
  all_goals (unfold pkgStI pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial))

theorem init_cmap : InitSpec pkg_id.github_com.orcaman.concurrent_map github_com.orcaman.concurrent_map.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  iapply wp_fupd
  try wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := w64) github_com.orcaman.concurrent_map.SHARD_COUNT go.int as H_SHARD_COUNT
    | wp_apply sync.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  by_cases hrn : swift.replicaNode (netIp (L := hG.goose_localGS) (GF := netDistGF))
  · -- a replica node: the boot thread's (C14), not the package state's
    iclear H_SHARD_COUNT
    imodintro
    iframe Hown
    is_pkg_init_finish
    unfold pkgStI pkgStates; dsimp only
    isplitr
    · ipureintro; exact isPanic_intoVal ()
    imodintro; imodintro
    unfold cmap.pkgSt
    rw [if_pos hrn]
    itrivial
  ipersist H_SHARD_COUNT
  imodintro
  iframe Hown
  is_pkg_init_finish
  unfold pkgStI pkgStates; dsimp only
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  imodintro; imodintro
  unfold cmap.pkgSt
  rw [if_neg hrn]
  iexists _
  iframe H_SHARD_COUNT
  ipureintro; decide

/-- The gob model's initializer: `errTooBig` holds its `errors.New` error and `codecMu` is a
mutex over `codecInv` (with `codec` nil), the model's state `encoding.gob.isInit`
(Proof/gob/Base.lean, the gob field of `pkgStates`). -/
theorem init_gob : InitSpec pkg_id.encoding.gob encoding.gob.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  iapply wp_fupd
  try wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := GoInterface) encoding.gob.errTooBig go.error as H_errTooBig
    | wp_apply wp_GlobalAlloc (V := Loc) encoding.gob.codec (go.GoType.PointerType encoding.gob.Codec.ty) as H_codec
    | wp_apply wp_GlobalAlloc (V := sync.Mutex) encoding.gob.codecMu sync.Mutex.ty as H_codecMu
    | wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply io.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
    | wp_apply sync.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
    | wp_apply errors.wp_New_errorString as %xT #ET
    | wp_auto)
  imod sync.init_Mutex encoding.gob.codecInv ⊤ (globalAddr encoding.gob.codecMu)
      $$ [H_codecMu] [H_codec] with #HcMu
  · iexact H_codecMu
  · inext; unfold encoding.gob.codecInv; ileft; iexact H_codec
  ipersist H_errTooBig
  imodintro
  iframe Hown
  is_pkg_init_finish
  unfold pkgStI pkgStates; dsimp only
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  imodintro; imodintro
  unfold encoding.gob.isInit errors.newVar
  isplitl
  · iexists xT
    iframe H_errTooBig ET
  iexact HcMu

theorem init_rpc : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.rpc github_com.imdea_software.swiftpaxos.rpc.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  repeat (first
    | wp_apply io.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  iframe Hown
  is_pkg_init_finish
  all_goals (unfold pkgStI pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial))

theorem init_dlog : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.dlog github_com.imdea_software.swiftpaxos.dlog.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := Bool) github_com.imdea_software.swiftpaxos.dlog.DLOG go.bool as H_DLOG
    | wp_apply log.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply os.initialize'.wp_proof _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  iframe Hown
  is_pkg_init_finish
  all_goals (unfold pkgStI pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial))

theorem init_config : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.config github_com.imdea_software.swiftpaxos.config.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  repeat (first
    | wp_apply wp_bufio _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply fmt.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
    | wp_apply os.initialize'.wp_proof _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
    | wp_apply strconv.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
    | wp_apply strings.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
    | wp_apply time.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  iframe Hown
  is_pkg_init_finish
  all_goals (unfold pkgStI pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial))

theorem init_state : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.state github_com.imdea_software.swiftpaxos.state.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  repeat (first
    | wp_apply encoding.binary.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply encoding.hex.initialize'.wp_proof _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
    | wp_apply fmt.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
    | wp_apply io.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
    | wp_apply strconv.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
    | wp_apply sync.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
    | wp_apply init_treemap _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H7⟩
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  iframe Hown
  is_pkg_init_finish
  all_goals (unfold pkgStI pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial))

theorem init_hook : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.hook github_com.imdea_software.swiftpaxos.hook.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  repeat (first
    | wp_apply os.initialize'.wp_proof _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply os.signal.initialize'.wp_proof _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
    | wp_apply syscall.initialize'.wp_proof _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  iframe Hown
  is_pkg_init_finish
  all_goals (unfold pkgStI pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial))

theorem init_defs : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.replica.defs github_com.imdea_software.swiftpaxos.replica.defs.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  iapply wp_fupd
  try wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := GoString) github_com.imdea_software.swiftpaxos.replica.defs.LatencyConf go.string as H_LatencyConf
    | wp_apply wp_GlobalAlloc (V := GoString) github_com.imdea_software.swiftpaxos.replica.defs.Storage go.string as H_Storage
    | wp_apply wp_GlobalAlloc (V := GoString) github_com.imdea_software.swiftpaxos.replica.defs.StoreFilname go.string as H_StoreFilname
    | wp_apply wp_bufio _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply io.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
    | wp_apply sync.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
    | wp_apply init_state _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
    | wp_apply wp_net _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
    | wp_apply os.initialize'.wp_proof _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
    | wp_apply strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H7⟩
    | wp_apply time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H8⟩
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  ipersist H_LatencyConf
  imodintro
  iframe Hown
  is_pkg_init_finish
  unfold pkgStI pkgStates; dsimp only
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  imodintro; imodintro
  unfold defs.pkgSt
  iexact H_LatencyConf

theorem init_replica : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.replica github_com.imdea_software.swiftpaxos.replica.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  iapply wp_fupd
  try wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := GoInterface) github_com.imdea_software.swiftpaxos.replica.NO_QUORUM_FILE go.error as H_NO_QUORUM_FILE
    | wp_apply wp_GlobalAlloc (V := GoInterface) github_com.imdea_software.swiftpaxos.replica.THREE_QUARTERS go.error as H_THREE_QUARTERS
    | wp_apply wp_bufio _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply errors.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
    | wp_apply os.initialize'.wp_proof _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
    | wp_apply sort.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
    | wp_apply strings.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
    | wp_apply encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
    | wp_apply wp_json _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H7⟩
    | wp_apply io.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H8⟩
    | wp_apply math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H9⟩
    | wp_apply wp_net _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H10⟩
    | wp_apply sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H11⟩
    | wp_apply time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H12⟩
    | wp_apply init_config _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H13⟩
    | wp_apply init_dlog _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H14⟩
    | wp_apply init_defs _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H15⟩
    | wp_apply init_rpc _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H16⟩
    | wp_apply init_state _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H17⟩
    | (fail_if_success iclear E1); wp_apply errors.wp_New_errorString as %xE1 #E1
    | wp_apply errors.wp_New_errorString as %xE2 #E2
    | wp_auto)
  ipersist H_NO_QUORUM_FILE
  ipersist H_THREE_QUARTERS
  imodintro
  iframe Hown
  is_pkg_init_finish
  unfold pkgStI pkgStates; dsimp only
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  imodintro; imodintro
  unfold replica.pkgSt errors.newVar
  isplitl
  · iexists _
    iframe H_NO_QUORUM_FILE
    first | iexact E1 | iexact E2
  · iexists _
    iframe H_THREE_QUARTERS
    first | iexact E1 | iexact E2

/-- `NewGhost()` (GHOST, fork e968d22): a new ghost, its mutex at its zero value, its prophecy
fresh. -/
theorem client.wp_NewGhost :
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

theorem init_client : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.client github_com.imdea_software.swiftpaxos.client.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  iapply wp_fupd
  try wp_auto
  repeat (first
    | wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply math.rand.initialize'.wp_proof _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
    | wp_apply wp_net _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
    | wp_apply sync.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
    | wp_apply time.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
    | wp_apply github_com.google.uuid.initialize'.wp_proof _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
    | wp_apply init_defs _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H7⟩
    | wp_apply init_state _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H8⟩
    | wp_apply wp_bufio _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H9⟩
    | wp_apply encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H10⟩
    | wp_apply fmt.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H11⟩
    | wp_apply wp_rpc _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H13⟩
    | wp_apply strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H14⟩
    | wp_apply init_dlog _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H15⟩
    | wp_apply init_rpc _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H16⟩
    -- the GHOST code's import (L1, fork a650254)
    | wp_apply github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H17⟩
    | wp_apply client.wp_NewGhost as %g ⟨%p, %pvs, %Hgn, Hgp, Hgmu, Hpr⟩
    | wp_apply wp_GlobalAlloc (V := Loc) github_com.imdea_software.swiftpaxos.client.nodeGhost (go.GoType.PointerType github_com.imdea_software.swiftpaxos.client.Ghost.ty) as H_nodeGhost
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  -- L2 (D90, R-E1): on a replica node the ghost's claim right is the boot thread's (its first
  -- initialization, SrvInit.lean), not the package state's; on any other node it is kept under
  -- the claim invariant, to be taken with the node's own address token
  by_cases hrn : swift.replicaNode (netIp (L := hG.goose_localGS) (GF := netDistGF))
  · iclear Hpr Hgmu Hgp H_nodeGhost
    imodintro
    iframe Hown
    is_pkg_init_finish
    all_goals (unfold pkgStI pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial))
    all_goals (unfold client.pkgSt; rw [if_pos hrn]; itrivial)
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ H_nodeGhost with #HnG
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ Hgp with #Hgp
  imod inv_alloc client.ghostInitN ⊤ iprop(client.ghostUnclaimed g p ∨
      addrTokG (extGlobalGS netExt (hlc := .hasLC))
        (client.keyAddr (netIp (L := hG.goose_localGS) (GF := netDistGF)))) $$ [Hpr Hgmu]
    with #Hgi
  · inext
    ileft
    iunfold client.ghostUnclaimed
    iexists pvs
    iframe
  ihave #Hst : client.pkgSt $$ []
  · iunfold client.pkgSt
    rw [if_neg hrn]
    iexists g, p
    iframe HnG Hgp Hgi
    ipureintro; exact Hgn
  imodintro
  iframe Hown
  is_pkg_init_finish
  all_goals (unfold pkgStI pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial | iexact Hst))

theorem init_master : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.master github_com.imdea_software.swiftpaxos.master.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  repeat (first
    | wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply fmt.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
    | wp_apply wp_net _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
    | wp_apply wp_http _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
    | wp_apply wp_rpc _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
    | wp_apply sync.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
    | wp_apply time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H7⟩
    | wp_apply init_config _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H8⟩
    | wp_apply init_dlog _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H9⟩
    | wp_apply init_defs _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H10⟩
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  iframe Hown
  is_pkg_init_finish
  all_goals (unfold pkgStI pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial))

set_option maxHeartbeats 2000000 in
theorem init_swift : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.swift github_com.imdea_software.swiftpaxos.swift.initialize' := by
  intro g Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
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
    | wp_apply init_rpc _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply init_client _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
    | wp_apply init_replica _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
    | wp_apply init_defs _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
    | wp_apply init_state _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
    | wp_apply wp_bufio _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
    | wp_apply init_gob _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H7⟩
    | wp_apply fmt.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H8⟩
    | wp_apply io.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H9⟩
    | wp_apply sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H10⟩
    | wp_apply time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H11⟩
    | wp_apply bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H12⟩
    | wp_apply crypto.sha256.initialize'.wp_proof _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H13⟩
    | wp_apply slices.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H14⟩
    | wp_apply encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H15⟩
    | wp_apply log.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H16⟩
    | wp_apply init_cmap _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H17⟩
    | wp_apply sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H18⟩
    | wp_apply init_config _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H19⟩
    | wp_apply init_dlog _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H20⟩
    | wp_apply init_hook _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H21⟩
    | wp_apply errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H22⟩
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
  by_cases hrn : swift.replicaNode (netIp (L := hG.goose_localGS) (GF := netDistGF))
  · -- a replica node: the boot thread's (C14), not the package state's
    iclear H_MaxDescRoutines H_useFastAckPool
    imodintro
    iframe Hown
    is_pkg_init_finish
    unfold pkgStI pkgStates; dsimp only
    isplitr
    · ipureintro; exact isPanic_intoVal ()
    imodintro; imodintro
    unfold swift.pkgSt errors.newVar
    rw [if_pos hrn]
    iframe H_ReplyHook H_SyncHook H_ExecHook
    isplitl
    · iexists _
      iframe H_errVarintOverflow EE
    · isplitl
      · iexists _
        iframe Hpool
        ipureintro; intro hf; cases hf
      · itrivial
  · ipersist H_MaxDescRoutines
    ipersist H_useFastAckPool
    imodintro
    iframe Hown
    is_pkg_init_finish
    unfold pkgStI pkgStates; dsimp only
    isplitr
    · ipureintro; exact isPanic_intoVal ()
    imodintro; imodintro
    unfold swift.pkgSt errors.newVar
    rw [if_neg hrn]
    iframe H_ReplyHook H_SyncHook H_ExecHook H_MaxDescRoutines H_useFastAckPool
    isplitl
    · iexists _
      iframe H_errVarintOverflow EE
    · iexists _
      iframe Hpool
      ipureintro; intro hf; cases hf

/-- The SwiftPaxos packages' and the `encoding/gob` model's initializers (`SwiftInits`), at
`pkgStates`. -/
theorem swiftInits : SwiftInits :=
  ⟨init_client, init_config, init_dlog, init_master, init_defs, init_swift, init_state, init_gob⟩

/-- **The test package's initialization** at the run's package states (with `remote`'s, group A's
`initialize.wp_proof`): the `wp_initialize'` field of node 0's and the client nodes' specs. -/
theorem swiftnet_wp_initialize' :
    InitSpec pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet
      examples.swiftnet.initialize' :=
  initialize.wp_proof swiftInits

end inits

end adapter

end Perennial.github_com.imdea_software.swiftpaxos
