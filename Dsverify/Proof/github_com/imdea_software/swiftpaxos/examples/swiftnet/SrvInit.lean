/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/SrvInit.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The server-side initialization (change log C14, decision D9 (a')): `swiftnetInitSrv.spec`
(Proof/swiftnet/Servers.lean). On a fresh node (the test package, `swift`, `client` and `concurrent-map`
not initialized yet: `ownInitializing (gSrv [swiftnet, swift, client, cmap])`), the test package's
initialization runs every initializer for the first time; `concurrent-map`'s returns the
points-to of `SHARD_COUNT` and `swift`'s those of `MaxDescRoutines` and `useFastAckPool`
(on a replica node, where the package states leave them out), `client`'s (run inside
`swift`'s, after `concurrent-map`'s) returns the node's fresh ghost (`client.freshAt netIp`,
decision D90 R-E1), and the test package's returns them (`swift.mutGlobalsAt netIp`,
`client.freshAt netIp`), by `wp_package_init_first` (InitFirst.lean). The other
initializers are the ones of ClientPkgInits.lean and Perennial's / the harness's, at
`gSrv L` for the packages run before `swift` / `concurrent-map` (their import closures avoid
`L`), at `gBoot` after.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientPkgInits
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.InitFirst
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Servers

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet
local notation "swiftPkg" => pkg_id.github_com.imdea_software.swiftpaxos.swift
local notation "cmapPkg" => pkg_id.github_com.orcaman.concurrent_map
local notation "clientPkg" => pkg_id.github_com.imdea_software.swiftpaxos.client

namespace adapter

section srv
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions]

/-- The run's package states (`pkgStates`) at this heap. -/
local instance pkgStS : SwiftNetPkgState netDistGF := @pkgStates _ netDistGF hG sem

/-! ## `gSrv` -/

theorem gSrv_mono (L L' : List GoString) (h : ∀ p, offIn L' p = true → offIn L p = true)
    (p : GoString) : gSrv L p ⊢ gSrv L' p := by
  unfold gSrv
  by_cases h' : offIn L' p = true
  · rw [if_pos (h p h'), if_pos h']
  · rw [if_neg h']
    split
    · exact false_elim
    · exact .rfl

theorem gSrv_boot (L : List GoString) (p : GoString) : gSrv L p ⊢ gBoot p := by
  unfold gSrv
  split
  · exact false_elim
  · exact .rfl

theorem gSrv_off (L : List GoString) (p : GoString) (h : offIn L p = true) :
    gSrv L p ⊢ iprop(False) := by
  unfold gSrv
  rw [if_pos h]

theorem gSrv_cons (q : GoString) (L : List GoString) (p : GoString) :
    gSrv (q :: L) p ⊢ gSrv L p := by
  apply gSrv_mono
  intro p' h
  simp only [offIn]
  split
  · rfl
  · exact h

open Classical in
/-- `cmap`'s mutable global, on a replica node. -/
def cmapGlobAt : IProp netDistGF :=
  iprop(if swift.replicaNode (netIp (L := hG.goose_localGS) (GF := netDistGF)) then
    iprop(∃ n : w64, typedPointsto
      (globalAddr _root_.Perennial.github_com.orcaman.concurrent_map.SHARD_COUNT) n (DFrac.own 1))
    else iprop(True))

set_option goose.wp.extras true

theorem init_cmap_first
    (Hinit : GetIsPkgInitProp cmapPkg (gSrv (hG := hG) (sem := sem) [clientPkg])) :
    {{ ownInitializing (gSrv (hG := hG) (sem := sem) [clientPkg, cmapPkg]) }}
      (App (Val github_com.orcaman.concurrent_map.initialize') (Val #()))
    {{ RET #(); ownInitializing (gSrv (hG := hG) (sem := sem) [clientPkg]) ∗
        isPkgInit (PROP := IProp netDistGF) cmapPkg ∗ cmapGlobAt }} := by
  wp_start as Hown
  iapply wp_package_init_first (gA := gSrv [clientPkg, cmapPkg]) (gB := gSrv [clientPkg])
    (gC := gSrv [clientPkg])
    (hA := gSrv_off _ _ (by decide))
    (hAB := gSrv_mono _ _ (fun p h => by
      simp only [offIn] at h ⊢
      split at h <;> simp_all))
    (heq := Hinit.1) $$ [Hown] HΦ
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
  · imodintro
    isplitl [H_SHARD_COUNT]
    · unfold cmapGlobAt
      rw [if_pos hrn]
      iexists _
      iexact H_SHARD_COUNT
    iframe Hown
    is_pkg_init_finish
    unfold pkgStS pkgStates; dsimp only
    isplitr
    · ipureintro; exact isPanic_intoVal ()
    imodintro; imodintro
    unfold cmap.pkgSt
    rw [if_pos hrn]
    itrivial
  ipersist H_SHARD_COUNT
  imodintro
  isplitr
  · unfold cmapGlobAt
    rw [if_neg hrn]
    itrivial
  iframe Hown
  is_pkg_init_finish
  unfold pkgStS pkgStates; dsimp only
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  imodintro; imodintro
  unfold cmap.pkgSt
  rw [if_neg hrn]
  iexists _
  iframe H_SHARD_COUNT
  ipureintro; decide

theorem cmapGlobAt_pos (hrn : swift.replicaNode (netIp (L := hG.goose_localGS) (GF := netDistGF))) :
    cmapGlobAt (hG := hG) ⊢ ∃ n : w64, typedPointsto
      (globalAddr _root_.Perennial.github_com.orcaman.concurrent_map.SHARD_COUNT) n (DFrac.own 1) := by
  unfold cmapGlobAt
  rw [if_pos hrn]

local notation "wp_io" => (io.wp_initialize' (GF := netDistGF) (hG := hG))
local notation "wp_errors" => (errors.wp_initialize' (GF := netDistGF) (hG := hG))
local notation "wp_time" => (time.wp_initialize' (GF := netDistGF) (hG := hG))
local notation "wp_sync" => (sync.wp_initialize' (GF := netDistGF) (hG := hG))
local notation "wp_net" => (net.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_time wp_io)
local notation "wp_bufio" => (bufio.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_io wp_errors)

local notation "wp_http'" => (net.http.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_sync wp_net wp_errors wp_bufio)
local notation "wp_rpc'" => (net.rpc.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_http' wp_sync wp_net wp_errors)

set_option maxHeartbeats 2000000 in
/-- `client`'s first initialization (decision D90, R-E1): on a replica node it returns the node's
fresh ghost (`client.freshAt`), which the package state leaves out there; elsewhere it keeps
it under the package state's claim invariant (as `init_client`). -/
theorem init_client_first (Hinit : GetIsPkgInitProp clientPkg (gBoot (hG := hG) (sem := sem))) :
    {{ ownInitializing (gSrv (hG := hG) (sem := sem) [clientPkg]) }}
      (App (Val github_com.imdea_software.swiftpaxos.client.initialize') (Val #()))
    {{ RET #(); ownInitializing (gBoot (hG := hG) (sem := sem)) ∗
        isPkgInit (PROP := IProp netDistGF) clientPkg ∗
        client.freshAt (netIp (L := hG.goose_localGS) (GF := netDistGF)) }} := by
  wp_start as Hown
  iapply wp_package_init_first (gA := gSrv [clientPkg]) (gB := gBoot) (gC := gBoot)
    (hA := gSrv_off _ _ (by decide)) (hAB := gSrv_boot _) (heq := Hinit.1) $$ [Hown] HΦ
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
    | wp_apply wp_rpc' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H13⟩
    | wp_apply strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H14⟩
    | wp_apply init_dlog _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H15⟩
    | wp_apply init_rpc _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H16⟩
    | wp_apply github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H17⟩
    | wp_apply client.wp_NewGhost as %g ⟨%p, %pvs, %Hgn, Hgp, Hgmu, Hpr⟩
    | wp_apply wp_GlobalAlloc (V := Loc) github_com.imdea_software.swiftpaxos.client.nodeGhost (go.GoType.PointerType github_com.imdea_software.swiftpaxos.client.Ghost.ty) as H_nodeGhost
    | wp_apply errors.wp_New as %_e _
    | wp_auto)
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ H_nodeGhost with #HnG
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ Hgp with #Hgp
  by_cases hrn : swift.replicaNode (netIp (L := hG.goose_localGS) (GF := netDistGF))
  · -- a replica node: the boot thread's
    imodintro
    isplitl [Hpr Hgmu]
    · unfold client.freshAt
      rw [if_pos hrn]
      iunfold client.ghostFresh
      iexists g, p, pvs
      iframe HnG Hgp Hpr Hgmu
      ipureintro; exact Hgn
    iframe Hown
    is_pkg_init_finish
    all_goals (unfold pkgStS pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial))
    all_goals (unfold client.pkgSt; rw [if_pos hrn]; itrivial)
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
  isplitr
  · unfold client.freshAt
    rw [if_neg hrn]
    itrivial
  iframe Hown
  is_pkg_init_finish
  all_goals (unfold pkgStS pkgStates; dsimp only; repeat (first | isplit | (iintro !>; itrivial) | itrivial | iexact Hst))

set_option maxHeartbeats 4000000 in
/-- `swift`'s first initialization: on a replica node it returns the three mutable globals and
(through `client`'s first initialization) the node's fresh ghost. -/
theorem init_swift_first (Hinit : GetIsPkgInitProp swiftPkg (gBoot (hG := hG) (sem := sem))) :
    {{ ownInitializing (gSrv (hG := hG) (sem := sem) [swiftPkg, clientPkg, cmapPkg]) }}
      (App (Val github_com.imdea_software.swiftpaxos.swift.initialize') (Val #()))
    {{ RET #(); ownInitializing (gBoot (hG := hG) (sem := sem)) ∗
        isPkgInit (PROP := IProp netDistGF) swiftPkg ∗
        (swift.mutGlobalsAt (netIp (L := hG.goose_localGS) (GF := netDistGF)) ∗
          client.freshAt (netIp (L := hG.goose_localGS) (GF := netDistGF))) }} := by
  -- before `concurrent-map`: `client` and `concurrent-map` not initialized yet
  have W_errors : GetIsPkgInitProp pkg_id.errors (gSrv (hG := hG) (sem := sem) [clientPkg, cmapPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have W_hook : GetIsPkgInitProp pkg_id.github_com.imdea_software.swiftpaxos.hook
      (gSrv (hG := hG) (sem := sem) [clientPkg, cmapPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have W_dlog : GetIsPkgInitProp pkg_id.github_com.imdea_software.swiftpaxos.dlog
      (gSrv (hG := hG) (sem := sem) [clientPkg, cmapPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have W_config : GetIsPkgInitProp pkg_id.github_com.imdea_software.swiftpaxos.config
      (gSrv (hG := hG) (sem := sem) [clientPkg, cmapPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have W_atomic : GetIsPkgInitProp pkg_id.sync.atomic
      (gSrv (hG := hG) (sem := sem) [clientPkg, cmapPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have W_cmap : GetIsPkgInitProp cmapPkg (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  -- after `concurrent-map`, before `client`
  have V_log : GetIsPkgInitProp pkg_id.log (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_binary : GetIsPkgInitProp pkg_id.encoding.binary (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_slices : GetIsPkgInitProp pkg_id.slices (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_sha256 : GetIsPkgInitProp pkg_id.crypto.sha256 (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_bytes : GetIsPkgInitProp pkg_id.bytes (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_time : GetIsPkgInitProp pkg_id.time (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_sync : GetIsPkgInitProp pkg_id.sync (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_io : GetIsPkgInitProp pkg_id.io (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_fmt : GetIsPkgInitProp pkg_id.fmt (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_gob : GetIsPkgInitProp pkg_id.encoding.gob (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_bufio : GetIsPkgInitProp pkg_id.bufio (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_state : GetIsPkgInitProp pkg_id.github_com.imdea_software.swiftpaxos.state
      (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_defs : GetIsPkgInitProp pkg_id.github_com.imdea_software.swiftpaxos.replica.defs
      (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have V_replica : GetIsPkgInitProp pkg_id.github_com.imdea_software.swiftpaxos.replica
      (gSrv (hG := hG) (sem := sem) [clientPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  wp_start as Hown
  iapply wp_package_init_first (gA := gSrv [swiftPkg, clientPkg, cmapPkg])
    (gB := gSrv [clientPkg, cmapPkg])
    (gC := gBoot) (hA := gSrv_off _ _ (by decide))
    (hAB := gSrv_cons _ _)
    (heq := Hinit.1) $$ [Hown] HΦ
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
    | wp_apply errors.wp_initialize' _ W_errors $$ Hown as ⟨Hown, #H22⟩
    | wp_apply init_hook _ W_hook $$ Hown as ⟨Hown, #H21⟩
    | wp_apply init_dlog _ W_dlog $$ Hown as ⟨Hown, #H20⟩
    | wp_apply init_config _ W_config $$ Hown as ⟨Hown, #H19⟩
    | wp_apply sync.atomic.wp_initialize' _ W_atomic $$ Hown as ⟨Hown, #H18⟩
    | wp_apply init_cmap_first W_cmap $$ Hown as ⟨Hown, #H17, Hsc⟩
    | wp_apply init_rpc _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
    | wp_apply init_client_first Hinit.2.2.1 $$ Hown as ⟨Hown, #H2, Hfr⟩
    | wp_apply init_replica _ V_replica $$ Hown as ⟨Hown, #H3⟩
    | wp_apply init_defs _ V_defs $$ Hown as ⟨Hown, #H4⟩
    | wp_apply init_state _ V_state $$ Hown as ⟨Hown, #H5⟩
    | wp_apply wp_bufio _ V_bufio $$ Hown as ⟨Hown, #H6⟩
    | wp_apply init_gob _ V_gob $$ Hown as ⟨Hown, #H7⟩
    | wp_apply fmt.wp_initialize' _ V_fmt $$ Hown as ⟨Hown, #H8⟩
    | wp_apply io.wp_initialize' _ V_io $$ Hown as ⟨Hown, #H9⟩
    | wp_apply sync.wp_initialize' _ V_sync $$ Hown as ⟨Hown, #H10⟩
    | wp_apply time.wp_initialize' _ V_time $$ Hown as ⟨Hown, #H11⟩
    | wp_apply bytes.wp_initialize' _ V_bytes $$ Hown as ⟨Hown, #H12⟩
    | wp_apply crypto.sha256.initialize'.wp_proof _ V_sha256 $$ Hown as ⟨Hown, #H13⟩
    | wp_apply slices.wp_initialize' _ V_slices $$ Hown as ⟨Hown, #H14⟩
    | wp_apply encoding.binary.wp_initialize' _ V_binary $$ Hown as ⟨Hown, #H15⟩
    | wp_apply log.wp_initialize' _ V_log $$ Hown as ⟨Hown, #H16⟩
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
    ihave ⟨%n, Hn⟩ := cmapGlobAt_pos hrn $$ Hsc
    imodintro
    isplitl [H_MaxDescRoutines H_useFastAckPool Hn Hfr]
    · isplitl [H_MaxDescRoutines H_useFastAckPool Hn]
      · unfold swift.mutGlobalsAt swift.mutGlobals
        rw [if_pos hrn]
        iexists _, _, _
        iframe H_MaxDescRoutines H_useFastAckPool Hn
      · iexact Hfr
    iframe Hown
    is_pkg_init_finish
    unfold pkgStS pkgStates; dsimp only
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
    isplitl [Hfr]
    · isplitr
      · unfold swift.mutGlobalsAt
        rw [if_neg hrn]
        itrivial
      · iexact Hfr
    iframe Hown
    is_pkg_init_finish
    unfold pkgStS pkgStates; dsimp only
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

set_option maxHeartbeats 4000000 in
/-- **The server-side initialization** (`swiftnetInitSrv.spec`, decision D9): the test package's
first initialization, through `swift`'s and `concurrent-map`'s first ones. -/
theorem swiftnetInitSrv_first :
    letI := @pkgStates _ netDistGF hG sem
    swiftnetInitSrv.spec := by
  have Hinit : GetIsPkgInitProp swiftnetPkg (gBoot (hG := hG) (sem := sem)) := by
    unfold gBoot; get_is_pkg_init_wf
  have W_gob : GetIsPkgInitProp pkg_id.encoding.gob
      (gSrv (hG := hG) (sem := sem) [swiftPkg, clientPkg, cmapPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have W_state : GetIsPkgInitProp pkg_id.github_com.imdea_software.swiftpaxos.state
      (gSrv (hG := hG) (sem := sem) [swiftPkg, clientPkg, cmapPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have W_errors : GetIsPkgInitProp pkg_id.errors
      (gSrv (hG := hG) (sem := sem) [swiftPkg, clientPkg, cmapPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have W_remote : GetIsPkgInitProp pkg_id.dsverify_lab.harness.remote
      (gSrv (hG := hG) (sem := sem) [swiftPkg, clientPkg, cmapPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  have W_check : GetIsPkgInitProp pkg_id.dsverify_lab.harness.check
      (gSrv (hG := hG) (sem := sem) [swiftPkg, clientPkg, cmapPkg]) := by
    unfold gSrv; get_is_pkg_init_wf
  wp_start as Hown
  iapply wp_package_init_first (gA := gSrv [swiftnetPkg, swiftPkg, clientPkg, cmapPkg])
    (gB := gSrv [swiftPkg, clientPkg, cmapPkg]) (gC := gBoot) (hA := gSrv_off _ _ (by decide))
    (hAB := gSrv_cons _ _)
    (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  have wp_http := net.http.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_sync wp_net
    wp_errors wp_bufio
  have wp_rpc := net.rpc.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_http wp_sync wp_net
    wp_errors
  wp_apply init_gob _ W_gob $$ Hown as ⟨Hown, #H_gob⟩
  wp_apply init_state _ W_state $$ Hown as ⟨Hown, #H_state⟩
  wp_apply wp_errors _ W_errors $$ Hown as ⟨Hown, #H_errors⟩
  wp_apply remote.wp_initialize' _ W_remote $$ Hown as ⟨Hown, #H_remote⟩
  wp_apply check.wp_initialize' _ W_check $$ Hown as ⟨Hown, #H_check⟩
  wp_apply init_swift_first Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown
    as ⟨Hown, #H_swift, Hglob, Hfr⟩
  wp_apply init_defs _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_defs⟩
  wp_apply init_master _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_master⟩
  wp_apply init_dlog _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_dlog⟩
  wp_apply init_config _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_config⟩
  wp_apply init_client _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_client⟩
  wp_apply models.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_models⟩
  wp_apply wp_time _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_time⟩
  wp_apply wp_sync _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_sync⟩
  wp_apply strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_strings⟩
  wp_apply wp_rpc _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_rpc⟩
  wp_apply wp_http _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_http⟩
  wp_apply wp_net _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_net⟩
  wp_apply math.rand.initialize'.wp_proof _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H_rand⟩
  wp_apply log.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H_log⟩
  wp_apply wp_io _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H_io⟩
  wp_apply fmt.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H_fmt⟩
  isplitl [Hglob Hfr]
  · iframe Hglob Hfr
  iframe Hown
  is_pkg_init_finish

end srv

end adapter

end Perennial.github_com.imdea_software.swiftpaxos
