/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/NewReplica.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B2: `gryff.NewReplica` with the kit's arguments (`NewReplica.wp`'s proof, modulo the hub
requests named at their steps).
-/
module

public import Dsverify.Proof.gryff.Replica2.Specs
public import Dsverify.Proof.gryff.Replica2.SpecsN
public import Dsverify.Proof.gryff.X.Final
public import Dsverify.Proof.gryff.N.StrIndex
public import Dsverify.Proof.gryff.Lib.ReadFullLt
public import Dsverify.Proof.gryff.Lib.MathHyps
public import Dsverify.Proof.gryff.B.Handler
public import Dsverify.Proof.gryff.B.Ctor
public import Dsverify.Proof.gryff.Server.SpecsDefs
public import Dsverify.Proof.gryff.N.Boot
public import Dsverify.Proof.gryff.B.Tables
public import Dsverify.Proof.gryff.B.Names
public import Dsverify.Proof.gryff.B.BootLem
public import Dsverify.Proof.gryff.B.Rcvr
public import Dsverify.Proof.gryff.B.Registry
public import Dsverify.Proof.gryff.Lib.RandHyps
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open model replica2
open Perennial.gryff.replica (XS rowOwn stackOwn euOwn nSlots)
open gryff.boot (gryffGlobals)

attribute [local instance] GooseGlobalGS.gooseInvGS

set_option goose.wp.extras true

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [sortA : SortSliceHyp GF] [strconvA : strconv.Assumptions]
variable [io.Assumptions] [net.Assumptions] [net.FieldAssumptions] [netN.NetSpecs GF]
variable [strA : netN.StringsIndexHyp GF] [mathA : lib.MathPowHyp GF]
variable [net.rpc.Assumptions] [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF] [randA : lib.RandSeedHyp GF]


/-- The registry's facts: three replicas, `nodes[id]` is node `k`'s address. -/
theorem registeredAs_len (γ : GryffNames GF) (k : Nat) (id : w64) (nodes : List GoString) :
    registeredAs γ k id nodes ⊢ ⌜nodes.length = 3 ∧ nodes[uint.nat id]? = some (addrOf k)⌝ := by
  iintro #Hreg
  icases registeredAs_preds γ k id nodes $$ Hreg with ⟨%hk, #Hr, -, -⟩
  unfold regReady
  icases Hr with ⟨-, %Hf⟩
  ipureintro; exact ⟨Hf.1.length_eq, Hf.2⟩

/-- `genericBuilt`'s `N` field (unit N's body). -/
theorem genericBuilt_N (gR : Loc) (id : w64) (nodes : List GoString)
    (regs : List (w8 × GoInterface × Loc)) (cregs : List (w8 × Loc)) :
    genericBuilt (GF := GF) gR id nodes regs cregs ⊢ genericBuilt gR id nodes regs cregs ∗
      ∃ n : w64, gR.[src.genericsmr.Replica, go!"N"] ↦□ n ∗
        ⌜nodes.length = sint.nat n ∧ 0 ≤ sint.Z n⌝ := by
  iintro Hgb
  unfold genericBuilt netN.genericBuiltB netN.builtRest
  icases Hgb with ⟨%rt, %ct, %M, %CM, #H1, H2, H3, %H4, H5, #H6, H7, #H8,
    %sl, %pS, %rS, %wS, %aS, %ppoS, %ewS, %dS, %dlS, %stl, %smR, %propC, %beaC, %occ, %pc, %crm,
    %cwm, %mu, %st, %dac, %γprop, %γbea, %γocc, %γp, %γda, %ps, %ms, %mls, %Hl, #HN, Hrest⟩
  isplitl
  · iexists rt, ct, M, CM
    iframe
    iframe #
    isplitr
    · ipureintro; exact H4
    ipureintro; exact Hl
  iexists sl.len
  iframe #
  ipureintro; exact ⟨Hl.1, Hl.2.1⟩

/-- The three `crt` names as a function. -/
def gcf (gc0 gc1 gc2 : GName) : Fin 3 → GName := fun q =>
  if q.val = 0 then gc0 else if q.val = 1 then gc1 else gc2

theorem crt_list (gc0 gc1 gc2 : GName) :
    monoNatAuthOwn gc0 1 0 ∗ monoNatAuthOwn gc1 1 0 ∗ monoNatAuthOwn gc2 1 0 ⊢
      (([∗list] q ∈ List.finRange 3, monoNatAuthOwn (gcf gc0 gc1 gc2 q) 1 0) : IProp GF) := by
  rw [show List.finRange 3 = [0, 1, 2] from rfl]
  iintro ⟨H0, H1, H2⟩
  iapply BigSepL.bigSepL_cons.2
  isplitl [H0]
  · rw [show gcf gc0 gc1 gc2 0 = gc0 from rfl]; iexact H0
  iapply BigSepL.bigSepL_cons.2
  isplitl [H1]
  · rw [show gcf gc0 gc1 gc2 1 = gc1 from rfl]; iexact H1
  iapply BigSepL.bigSepL_cons.2
  isplitl [H2]
  · rw [show gcf gc0 gc1 gc2 2 = gc2 from rfl]; iexact H2
  iapply BigSepL.bigSepL_nil.2
  iempintro

/-- The replica's `run()` (the goroutine `NewReplica` starts), as a spec: the triple of
`Replica2/Results.lean`'s `run.wp` (its `wp_rfl` applied), which `NewReplica_core` takes as an
argument (CLAUDE.md, "Import tiers": a proof sees its callees through their specs only);
`examples/gryffnet/Link.lean` passes `run.wp`. -/
def Replica.run.spec : Prop :=
  ∀ (γ : GryffNames GF) (ρ : replica2.Repl2Names) (k : Fin 3) (r gR : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ replica2.isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ replica2.connectRes γ ρ k r gR }}
      (App (replica2.repM r go!"run") (Val #()))
    {{ RET #(); True }}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem NewReplica_core (wp_rfl : lib.io.ReadFull.specLt (GF := GF) (hG := hG))
    (wp_run : Replica.run.spec (GF := GF) (hG := hG))
    (L : CodecLaws (GF := GF)) (RL : RcvLaws (GF := GF)) (γ : GryffNames GF) (k : Nat)
    (id : w64) (sl : GoSlice) (nodes : List GoString) (hk : k < 3) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗
        net.rpc.codecSet gryffCodec ∗ □ sharedInvs γ ∗
        □ ([∗list] j ∈ [0, 1, 2], replicaLis γ j) ∗ registeredAs γ k id nodes ∗
        sl ↦* nodes ∗ replicaReady γ id ∗ gryffGlobals ∗
        inv deployN (deployInv γ.deploy γ.proto) }} -- B3-R1: the registry's port ids
      (App (App (App (App (App (App (App (App (App (App (App (App (App (App (App (App (App
        (Val (@! gryff.src.gryff.NewReplica)) (Val #id)) (Val #sl)) (Val #false)) (Val #true))
        (Val #true)) (Val #false)) (Val #false)) (Val #(go!""))) (Val #false)) (Val #true))
        (Val #false)) (Val #false)) (Val #(W8 1))) (Val #(W64 100))) (Val #(W64 100)))
        (Val #(W64 100))) (Val #false))
    {{ (rep : Loc), RET #rep; replicaOk γ rep ∗
        ∃ (ρ : replica2.Repl2Names) (kr : Fin 3), ⌜kr.val = uint.nat id⌝ ∗
          replica2.isReplica γ ρ kr rep }} := by
  wp_start as ⟨#Hcodec, #Hsh, #Hprotos, #Hreg, Hsl, Hready, Hglob, #Hdep⟩
  iapply wp_fupd
  ihave #Hgsmr : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
  · iPkgInit
  unfold replicaReady
  icases Hready with ⟨%p, %hid, #Htp, Hproph, Hslot, #Hpreds⟩
  wp_auto
  wp_apply (NewReplicaDurable_wp id sl nodes) $$ [Hsl] as %gR Hgb
  · iframe
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %cc1 %γc1 ⟨#Hcc1, -, Hoc1⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %cc2 %γc2 ⟨#Hcc2, -, Hoc2⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %cc3 %γc3 ⟨#Hcc3, -, Hoc3⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %cc4 %γc4 ⟨#Hcc4, -, Hoc4⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %cc5 %γc5 ⟨#Hcc5, -, Hoc5⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %cc6 %γc6 ⟨#Hcc6, -, Hoc6⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %cc7 %γc7 ⟨#Hcc7, -, Hoc7⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs1 %γs1 ⟨#Hcs1, -, Hos1⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs2 %γs2 ⟨#Hcs2, -, Hos2⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs3 %γs3 ⟨#Hcs3, -, Hos3⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs4 %γs4 ⟨#Hcs4, -, Hos4⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs5 %γs5 ⟨#Hcs5, -, Hos5⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs6 %γs6 ⟨#Hcs6, -, Hos6⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs7 %γs7 ⟨#Hcs7, -, Hos7⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs8 %γs8 ⟨#Hcs8, -, Hos8⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs9 %γs9 ⟨#Hcs9, -, Hos9⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs10 %γs10 ⟨#Hcs10, -, Hos10⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs11 %γs11 ⟨#Hcs11, -, Hos11⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %cs12 %γs12 ⟨#Hcs12, -, Hos12⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := Bool) (W64 1)) $$ [] as %cfw %γfw ⟨#Hcfw, -, Hofw⟩
  · ipureintro; decide
  try wp_auto
  simp only [src.gryff.Replica.fieldsUnsealed, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  try wp_auto
  ihave ⟨«$r0», %hr0nn⟩ := persistent_entails_left (typedPointsto_not_null _ _ _) $$ «$r0»
  iStructNamedPrefix «$r0» "f"
  ipersist fReplica
  ipersist fShutdown
  ipersist fproxy
  ipersist fshortcircuitTime
  ipersist fmtx
  ipersist fproph
  ipersist fmaxSeenTag
  ipersist fflush
  ipersist fread1Chan
  ipersist fread2Chan
  ipersist fwrite1Chan
  ipersist fwrite2Chan
  ipersist frmwChan
  ipersist freadChan
  ipersist fwriteChan
  ipersist fread1ChanProxied
  ipersist fread2ChanProxied
  ipersist fwrite1ChanProxied
  ipersist fwrite2ChanProxied
  ipersist fwrite1ReplyChan
  ipersist fwrite1TimeoutChan
  ipersist fwrite2ConcurrentTimeoutChan
  ipersist fwrite2ReplyChan
  ipersist fread1ChanRepl
  ipersist fread2ChanRepl
  ipersist fread1ReplyChan
  ipersist fread2ReplyChan
  ipersist fforceWriteChan
  ipersist fread1
  ipersist fread2
  ipersist fwrite1
  ipersist fwrite2
  ipersist ffastOverwriteTime
  ipersist fforceWritePeriod
  ihave %Hnl := registeredAs_len γ k id nodes $$ Hreg
  ihave Hgb : genericBuilt gR id nodes [] [] $$ [Hgb]
  · unfold genericBuilt; iexact Hgb
  icases genericBuilt_N gR id nodes [] [] $$ Hgb with ⟨Hgb, %nN, #HN, %HnN⟩
  have hN : nN = W64 3 := by
    have h1 := HnN.1; rw [Hnl.1] at h1
    have h2 := HnN.2
    have : sint.Z nN = 3 := by
      have : ((sint.nat nN : Nat) : Int) = sint.Z nN := Int.toNat_of_nonneg h2
      omega
    word
  subst hN
  imod ghost_map_alloc_empty (K := Prod Int Int) (V := Loc) with ⟨%gp, Hgp⟩
  imod mono_nat_own_alloc 0 with ⟨%gc0, Hgc0, -⟩
  imod mono_nat_own_alloc 0 with ⟨%gc1, Hgc1, -⟩
  imod mono_nat_own_alloc 0 with ⟨%gc2, Hgc2, -⟩
  ihave Hgc := crt_list gc0 gc1 gc2 $$ [Hgc0 Hgc1 Hgc2]
  · iframe
  unfold gryffGlobals
  icases Hglob with ⟨Hstack, Hpa, Hea, Hec, Hecs, Hcon, Hhap, Hslow, Hweird, Hcpc, Hcpm, -, -, -, -, Hbf⟩
  wp_apply (NewEPaxosRMWHandler_wp ⟨uint.nat id, hid⟩ «$r0_ptr» gR id nodes [] gp
    (gcf gc0 gc1 gc2)) $$ [Hgb Hgp Hgc Hpa Hea Hec Hecs Hcon Hhap Hslow Hweird Hcpc Hcpm Hbf]
    as %h ⟨%ex, %euS, %es, %γs, %γr, %γeo, #HhR, #Hhex, #Hexr, #Hhbo, %Hesl, Hgb, Hregs, Hrec, Heo,
      #Heu, Heuo, Hbf, Hepw⟩
  · iframe; iframe #
    unfold hGlobals; iframe
  try wp_auto
  ipersist frmwHandler
  -- B3: the generic replica's rest (its channels' names), the tables kept for the registrations
  icases genericBuilt_split gR id nodes (hRegs es) $$ Hgb with ⟨Htbl, Hrest⟩
  iunfold netN.builtRest at Hrest
  icases Hrest with ⟨%sl', %pS, %rS, %wS, %aS, %ppoS, %ewS, %dS, %dlS, %stl, %smR, %propC, %beaC,
    %occ, %pc, %crm, %cwm, %mu, %st, %dac, %γprop, %γbea, %γocc, %γp, %γda, %ps, %ms, %mls, %Hl,
    #HN', #HId, #HPAL, Hsl', #HPeers, HpS, #HPR, HrS, #HPW, HwS, #HAl, HaS, HList, #HSt, HStore,
    HsmR, #HPC, #HpropC, HpropO, #HBC, #HbeaC, HbeaO, #HSd, #HTh, #HEx, #HDr, HBeacon, HDurable,
    #HPPO, HppoS, #HEw, HewS, #HOCC, #HoccC, HoccO, #HcC, #HPing, #HpingB, #HCR, Hcrm, #HCW, Hcwm,
    #HMu, Hmu, #HStats, HstatsOk, #HDAC, #HdacC, HdacO, #HdR, HdS, Hms, #HdlR, HdlS, Hmls⟩
  -- the replica's names
  imod ghostVar_alloc xs0 with ⟨%gxs, Hxs⟩
  imod ghostVar_alloc true with ⟨%gboot, Hboot⟩
  imod ghost_map_alloc_empty (K := w32) (V := Loc) with ⟨%gw, Hw⟩
  imod ghost_map_alloc_empty (K := w32) (V := Loc) with ⟨%gesc, Hesc⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Repl2Names, ρ = ⟨gxs, gp, gcf gc0 gc1 gc2, gw, gboot,
      chansOf γc6 γc7 γc5 γfw [γs1, γs2, γs3, γs4, γs5, γs6, γs7, γs8, γs9, γs10, γs11, γs12] γs
        γr γeo γbea γocc γda γprop ⟨gesc, gesc, gesc, gesc, gesc, W64 0⟩⟩ := ⟨_, rfl⟩
  have hρp : ρ.ptrs = gp ∧ ρ.crt = gcf gc0 gc1 gc2 := by subst hρ; exact ⟨rfl, rfl⟩
  have hρxs : ρ.xs = gxs := by subst hρ; rfl
  have hρboot : ρ.boot = gboot := by subst hρ; rfl
  have hρeo : ρ.chans "executeOverwrite" = γeo := by subst hρ; rfl
  have hρrec : ρ.chans "recover" = γr := by subst hρ; rfl
  let kr : Fin 3 := ⟨uint.nat id, hid⟩
  ihave Hep := Hepw $$ %ρ %hρp
  icases ghostVar_halves _ _ $$ Hxs with ⟨Hxs1, Hxs2⟩
  icases ghostVar_halves _ _ $$ Hboot with ⟨Hboot1, Hboot2⟩
  -- the lock, in its boot state
  ihave Hlk : replicaLockInv γ ρ kr «$r0_ptr» p $$ [Hep Hxs1 Hboot1]
  · unfold replicaLockInv lockBoot
    iright
    iexists h, xs0
    rw [hρxs, hρboot]
    unfold handlerIface
    iframe; iframe #
  imod sync.init_Mutex (replicaLockInv γ ρ kr «$r0_ptr» p) ⊤ «$v44_ptr» $$ [«$v44»] [Hlk]
    with #Hmu
  · iexact «$v44»
  · inext; iexact Hlk
  -- the executor's two channels
  iunfold hChanRaw at Heo
  icases Heo with ⟨%eoc, #Heof, #Heoc, Heoo⟩
  iunfold hChanRaw at Hrec
  icases Hrec with ⟨%rcc, #Hrcf, #Hrcc, Hrco⟩
  imod start_bag (eoChanP γ kr) (.Buffered []) eoc γeo trivial $$ Heoc Heoo with #Heob
  imod start_bag (recoverChanP ρ) (.Buffered []) rcc γr trivial $$ Hrcc Hrco with #Hrcb
  ihave #Hgi : gryffInv2 γ.proto $$ []
  · ihave #Hp := sharedInvs_proto γ $$ Hsh
    iunfold protoInvs at Hp; icases Hp with ⟨#H, -⟩; iexact H
  have hrid : rid32 kr = W32 (sint.Z id) := by
    have h1 : sint.Z id = uint.Z id := by
      have : uint.Z id < 3 := by have := hid; simp only [uint.nat, uint.Z] at this ⊢; omega
      word
    rw [h1]; unfold rid32; simp only [kr, uint.nat]; try (congr 1; omega)
  ihave #HisExec : isExec γ ρ kr «$r0_ptr» h $$ []
  · unfold isExec bagAt
    iexists gR, «$v44_ptr», ex, p
    rw [hrid, hρeo, hρrec]
    unfold handlerIface
    iframe #
  -- `go e.executeCommands()` (H-X-2: the empty search state)
  try wp_auto
  wp_apply wp_fork $$ [Hxs2 Hstack Heuo]
  · wp_apply (X.executeCommands_wp γ ρ kr «$r0_ptr» h xs0) $$ [Hxs2 Hstack Heuo]
    · iframe #
      isplitl
      · iapply execPriv2_init ρ h euS
        rw [hρxs]
        iframe; iframe #
      ipureintro; exact xs0_facts
    itrivial
  try wp_auto
  -- `rand.Seed(time.Now().UnixNano() << 4 | int64(id))`
  ihave #Hrand : isPkgInit (PROP := IProp GF) pkg_id.math.rand $$ []
  · iPkgInit
  wp_apply time.wp_Now as %tn -
  try wp_auto
  wp_apply (time.Time.wp_UnixNano' tn) as %un -
  try wp_auto
  wp_apply (randA.seed _) $$ [Hrand]
  try wp_auto
  -- `myPreferredPeerOrder` (a field no predicate mentions)
  icombine HN HN' gives %HNe
  have hN3 : sl'.len = W64 3 := HNe.symm
  rw [hN3]
  wp_apply (wp_slice_make2 (V := w32) (W64 3)) as %mppS ⟨HmppS, -⟩
  · ipureintro; decide
  try wp_auto
  ihave %Hml := ownSlice_len _ _ _ $$ HmppS
  have hml : sint.Z mppS.len = 3 := by
    have h1 := Hml.1; simp only [List.length_replicate] at h1
    have h2 := Int.toNat_of_nonneg Hml.2
    simp only [sint.nat] at h1 h2
    simp only [sint.Z] at h2 ⊢
    omega
  rw [if_pos (by rw [hml]; decide)]
  wp_apply wp_store_slice_index mppS (sint.Z (W64 0)) _ _ $$ [HmppS] as HmppS
  · iframe; ipureintro
    have e2 : sint.Z (W64 0) = 0 := rfl
    simp only [List.length_replicate, e2]; omega
  try wp_auto
  ihave IHp : iprop(∃ (j : w64) (xs : List w32), "i" ∷ i_ptr ↦ j ∗ "Hm" ∷ mppS ↦* xs ∗
      "%Hj" ∷ ⌜1 ≤ sint.Z j ∧ sint.Z j ≤ 3 ∧ xs.length = 3⌝) $$ [i HmppS]
  · iexists _, _; iframe; ipureintro
    simp only [List.length_set, List.length_replicate]
    exact ⟨by decide, by decide, by simp⟩
  wp_for IHp
  wp_if_destruct
  · try wp_auto
    have hj3 : sint.Z j < 3 := by
      have : sint.Z (W64 3) = 3 := rfl
      omega
    rw [if_pos ⟨by omega, by rw [hml]; omega⟩]
    wp_apply wp_store_slice_index mppS (sint.Z j) xs _ $$ [Hm] as Hm
    · iframe; ipureintro; omega
    wp_for_post
    iframe
    iexists _, _; iframe; ipureintro
    simp only [List.length_set]
    refine ⟨by word, by word, Hj.2.2⟩
  try wp_auto
  -- the participant, the coordinator
  ihave #Hgc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  ihave #Hdlp : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog : globalAddr gryff.src.dlog.DLOG ↦□ false $$ []
  · iapply replica.dlog_init_access; iexact Hdlp
  rw [← hrid]
  wp_apply (NewGryffParticipant_wp kr _) as %pa Hpa
  try wp_auto
  ipersist fparti
  wp_apply (wp_Replica_Printf «$r0_ptr»)
  · iframe #
  try wp_auto
  wp_apply (NewGryffCoordinator_wp ρ kr _) as %co Hco
  try wp_auto
  ipersist fcoord
  -- the registrations: two client kinds, the eight proxied kinds, `rmw`
  have hlen14 : (hRegs es).length = 14 := by simp [hRegs, hKinds, Hesl.1]
  wp_alloc oc1 as Hoc1o
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterClientRPC_tbl gR _ _ _ _ cc6) $$ [Htbl] as Htbl
  · iframe #; iframe; ipureintro; simp
  try wp_auto
  wp_alloc oc2 as Hoc2o
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterClientRPC_tbl gR _ _ _ _ cc7) $$ [Htbl] as Htbl
  · iframe #; iframe; ipureintro; simp [src.clientproto.Gryff_READ, src.clientproto.Gryff_WRITE]
  try wp_auto
  wp_alloc or1 as Hor1
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_tbl gR _ _ _ cs1) $$ [Htbl] as %cd1 ⟨Htbl, %Hcd1⟩
  · iframe #; iframe; ipureintro; simp [hlen14]
  try wp_auto
  ipersist fread1RPC
  wp_alloc or2 as Hor2
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_tbl gR _ _ _ cs2) $$ [Htbl] as %cd2 ⟨Htbl, %Hcd2⟩
  · iframe #; iframe; ipureintro; simp [hlen14]
  try wp_auto
  ipersist fread2RPC
  wp_alloc or3 as Hor3
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_tbl gR _ _ _ cs3) $$ [Htbl] as %cd3 ⟨Htbl, %Hcd3⟩
  · iframe #; iframe; ipureintro; simp [hlen14]
  try wp_auto
  ipersist fwrite1RPC
  wp_alloc or4 as Hor4
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_tbl gR _ _ _ cs4) $$ [Htbl] as %cd4 ⟨Htbl, %Hcd4⟩
  · iframe #; iframe; ipureintro; simp [hlen14]
  try wp_auto
  ipersist fwrite2RPC
  wp_alloc or5 as Hor5
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_tbl gR _ _ _ cs11) $$ [Htbl] as %cd5 ⟨Htbl, %Hcd5⟩
  · iframe #; iframe; ipureintro; simp [hlen14]
  try wp_auto
  ipersist fread1ReplyRPC
  wp_alloc or6 as Hor6
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_tbl gR _ _ _ cs12) $$ [Htbl] as %cd6 ⟨Htbl, %Hcd6⟩
  · iframe #; iframe; ipureintro; simp [hlen14]
  try wp_auto
  ipersist fread2ReplyRPC
  wp_alloc or7 as Hor7
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_tbl gR _ _ _ cs5) $$ [Htbl] as %cd7 ⟨Htbl, %Hcd7⟩
  · iframe #; iframe; ipureintro; simp [hlen14]
  try wp_auto
  ipersist fwrite1ReplyRPC
  wp_alloc or8 as Hor8
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_tbl gR _ _ _ cs8) $$ [Htbl] as %cd8 ⟨Htbl, %Hcd8⟩
  · iframe #; iframe; ipureintro; simp [hlen14]
  try wp_auto
  ipersist fwrite2ReplyRPC
  wp_alloc oc3 as Hoc3o
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterClientRPC_tbl gR _ _ _ _ cc5) $$ [Htbl] as Htbl
  · iframe #; iframe; ipureintro
    simp [src.clientproto.Gryff_READ, src.clientproto.Gryff_WRITE, src.clientproto.Gryff_RMW]
  try wp_auto
  -- the run loop's channels as bags (`replicaChans`)
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, rfl⟩ := list14 es Hesl.1
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, rfl⟩ := list14 γs Hesl.2
  isimp [hKinds, List.zip_cons_cons, List.zip_nil_right, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil, hRegOwn] at Hregs
  icases Hregs with ⟨⟨#Hf0, #Hc0, Ho0, #Hr0⟩, ⟨#Hf1, #Hc1, Ho1, #Hr1⟩, ⟨#Hf2, #Hc2, Ho2, #Hr2⟩, ⟨#Hf3, #Hc3, Ho3, #Hr3⟩, ⟨#Hf4, #Hc4, Ho4, #Hr4⟩, ⟨#Hf5, #Hc5, Ho5, #Hr5⟩, ⟨#Hf6, #Hc6, Ho6, #Hr6⟩, ⟨#Hf7, #Hc7, Ho7, #Hr7⟩, ⟨#Hf8, #Hc8, Ho8, #Hr8⟩, ⟨#Hf9, #Hc9, Ho9, #Hr9⟩, ⟨#Hf10, #Hc10, Ho10, #Hr10⟩, ⟨#Hf11, #Hc11, Ho11, #Hr11⟩, ⟨#Hf12, #Hc12, Ho12, #Hr12⟩, ⟨#Hf13, #Hc13, Ho13, #Hr13⟩, -⟩
  have c_read1 : ρ.chans "read1" = γs1 := by subst hρ; rfl
  have c_read2 : ρ.chans "read2" = γs2 := by subst hρ; rfl
  have c_write1 : ρ.chans "write1" = γs3 := by subst hρ; rfl
  have c_write2 : ρ.chans "write2" = γs4 := by subst hρ; rfl
  have c_write1Reply : ρ.chans "write1Reply" = γs5 := by subst hρ; rfl
  have c_w1timeout : ρ.chans "w1timeout" = γs6 := by subst hρ; rfl
  have c_w2timeout : ρ.chans "w2timeout" = γs7 := by subst hρ; rfl
  have c_write2Reply : ρ.chans "write2Reply" = γs8 := by subst hρ; rfl
  have c_read1Reply : ρ.chans "read1Reply" = γs11 := by subst hρ; rfl
  have c_read2Reply : ρ.chans "read2Reply" = γs12 := by subst hρ; rfl
  have c_read : ρ.chans "read" = γc6 := by subst hρ; rfl
  have c_write : ρ.chans "write" = γc7 := by subst hρ; rfl
  have c_rmw : ρ.chans "rmw" = γc5 := by subst hρ; rfl
  have c_forceWrite : ρ.chans "forceWrite" = γfw := by subst hρ; rfl
  have c_beacon : ρ.chans "beacon" = γbea := by subst hρ; rfl
  have c_doneAdapting : ρ.chans "doneAdapting" = γda := by subst hρ; rfl
  have c_onClientConnect : ρ.chans "onClientConnect" = γocc := by subst hρ; rfl
  have c_prepare : ρ.chans "prepare" = g0 := by subst hρ; rfl
  have c_prepareReply : ρ.chans "prepareReply" = g1 := by subst hρ; rfl
  have c_preAccept : ρ.chans "preAccept" = g2 := by subst hρ; rfl
  have c_preAcceptReply : ρ.chans "preAcceptReply" = g3 := by subst hρ; rfl
  have c_preAcceptOK : ρ.chans "preAcceptOK" = g4 := by subst hρ; rfl
  have c_accept : ρ.chans "accept" = g5 := by subst hρ; rfl
  have c_acceptReply : ρ.chans "acceptReply" = g6 := by subst hρ; rfl
  have c_commit : ρ.chans "commit" = g7 := by subst hρ; rfl
  have c_commitShort : ρ.chans "commitShort" = g8 := by subst hρ; rfl
  have c_tryPreAccept : ρ.chans "tryPreAccept" = g9 := by subst hρ; rfl
  have c_tryPreAcceptReply : ρ.chans "tryPreAcceptReply" = g10 := by subst hρ; rfl
  have c_executed : ρ.chans "executed" = g11 := by subst hρ; rfl
  have c_preAcceptOKReply : ρ.chans "preAcceptOKReply" = g12 := by subst hρ; rfl
  have c_acceptOKReply : ρ.chans "acceptOKReply" = g13 := by subst hρ; rfl
  imod start_bag (msgChanP γ ρ kr "read1") (.Buffered []) cs1 γs1 trivial $$ Hcs1 Hos1 with #B_read1
  imod start_bag (msgChanP γ ρ kr "read2") (.Buffered []) cs2 γs2 trivial $$ Hcs2 Hos2 with #B_read2
  imod start_bag (msgChanP γ ρ kr "write1") (.Buffered []) cs3 γs3 trivial $$ Hcs3 Hos3 with #B_write1
  imod start_bag (msgChanP γ ρ kr "write2") (.Buffered []) cs4 γs4 trivial $$ Hcs4 Hos4 with #B_write2
  imod start_bag (msgChanP γ ρ kr "write1Reply") (.Buffered []) cs5 γs5 trivial $$ Hcs5 Hos5 with #B_write1Reply
  imod start_bag ((fun (_ : GoInterface) => iprop(False))) (.Buffered []) cs6 γs6 trivial $$ Hcs6 Hos6 with #B_w1timeout
  imod start_bag ((fun (_ : GoInterface) => iprop(False))) (.Buffered []) cs7 γs7 trivial $$ Hcs7 Hos7 with #B_w2timeout
  imod start_bag (msgChanP γ ρ kr "write2Reply") (.Buffered []) cs8 γs8 trivial $$ Hcs8 Hos8 with #B_write2Reply
  imod start_bag (msgChanP γ ρ kr "read1Reply") (.Buffered []) cs11 γs11 trivial $$ Hcs11 Hos11 with #B_read1Reply
  imod start_bag (msgChanP γ ρ kr "read2Reply") (.Buffered []) cs12 γs12 trivial $$ Hcs12 Hos12 with #B_read2Reply
  imod start_bag (reqChanP γ ρ kr "read") (.Buffered []) cc6 γc6 trivial $$ Hcc6 Hoc6 with #B_read
  imod start_bag (reqChanP γ ρ kr "write") (.Buffered []) cc7 γc7 trivial $$ Hcc7 Hoc7 with #B_write
  imod start_bag (reqChanP γ ρ kr "rmw") (.Buffered []) cc5 γc5 trivial $$ Hcc5 Hoc5 with #B_rmw
  imod start_bag ((fun (_ : Bool) => iprop(True))) (.Buffered []) cfw γfw trivial $$ Hcfw Hofw with #B_forceWrite
  imod start_bag ((fun (_ : Loc) => iprop(False))) (.Buffered []) beaC γbea trivial $$ HbeaC HbeaO with #B_beacon
  imod start_bag ((fun (_ : Bool) => iprop(False))) (.Buffered []) dac γda trivial $$ HdacC HdacO with #B_doneAdapting
  imod start_bag ((fun (_ : Bool) => iprop(False))) (.Buffered []) occ γocc trivial $$ HoccC HoccO with #B_onClientConnect
  imod start_bag (msgChanP γ ρ kr "prepare") (.Buffered []) e0.2.2 g0 trivial $$ Hc0 Ho0 with #B_prepare
  imod start_bag (msgChanP γ ρ kr "prepareReply") (.Buffered []) e1.2.2 g1 trivial $$ Hc1 Ho1 with #B_prepareReply
  imod start_bag (msgChanP γ ρ kr "preAccept") (.Buffered []) e2.2.2 g2 trivial $$ Hc2 Ho2 with #B_preAccept
  imod start_bag (msgChanP γ ρ kr "preAcceptReply") (.Buffered []) e3.2.2 g3 trivial $$ Hc3 Ho3 with #B_preAcceptReply
  imod start_bag (msgChanP γ ρ kr "preAcceptOK") (.Buffered []) e4.2.2 g4 trivial $$ Hc4 Ho4 with #B_preAcceptOK
  imod start_bag (msgChanP γ ρ kr "accept") (.Buffered []) e5.2.2 g5 trivial $$ Hc5 Ho5 with #B_accept
  imod start_bag (msgChanP γ ρ kr "acceptReply") (.Buffered []) e6.2.2 g6 trivial $$ Hc6 Ho6 with #B_acceptReply
  imod start_bag (msgChanP γ ρ kr "commit") (.Buffered []) e7.2.2 g7 trivial $$ Hc7 Ho7 with #B_commit
  imod start_bag ((fun (_ : GoInterface) => iprop(False))) (.Buffered []) e8.2.2 g8 trivial $$ Hc8 Ho8 with #B_commitShort
  imod start_bag ((fun (_ : GoInterface) => iprop(False))) (.Buffered []) e9.2.2 g9 trivial $$ Hc9 Ho9 with #B_tryPreAccept
  imod start_bag ((fun (_ : GoInterface) => iprop(False))) (.Buffered []) e10.2.2 g10 trivial $$ Hc10 Ho10 with #B_tryPreAcceptReply
  imod start_bag (msgChanP γ ρ kr "executed") (.Buffered []) e11.2.2 g11 trivial $$ Hc11 Ho11 with #B_executed
  imod start_bag ((fun (_ : GoInterface) => iprop(False))) (.Buffered []) e12.2.2 g12 trivial $$ Hc12 Ho12 with #B_preAcceptOKReply
  imod start_bag ((fun (_ : GoInterface) => iprop(False))) (.Buffered []) e13.2.2 g13 trivial $$ Hc13 Ho13 with #B_acceptOKReply
  ihave Hchans : replicaChans γ ρ kr «$r0_ptr» gR h $$ []
  · unfold replicaChans bagAt
    rw [c_read1, c_read2, c_write1, c_write2, c_write1Reply, c_w1timeout, c_w2timeout, c_write2Reply, c_read1Reply, c_read2Reply, c_read, c_write, c_rmw, c_forceWrite, c_beacon, c_doneAdapting, c_onClientConnect, c_prepare, c_prepareReply, c_preAccept, c_preAcceptReply, c_preAcceptOK, c_accept, c_acceptReply, c_commit, c_commitShort, c_tryPreAccept, c_tryPreAcceptReply, c_executed, c_preAcceptOKReply, c_acceptOKReply]
    iframe #
  -- `genericOk`: the tables (persisted)
  iunfold tblB at Htbl
  icases Htbl with ⟨%rt, %ct, %M, %CM, #Hrt, HM, -, %Hcodes, Hent, #Hct, HCM, Hcent⟩
  imod ownMap_persist rt _ M $$ HM with #HM
  imod ownMap_persist ct _ CM $$ HCM with #HCM
  simp [hRegs, hKinds, List.range_succ] at Hcodes
  isimp [hRegs, hKinds, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil] at Hent
  isimp [BigSepL.bigSepL_cons, BigSepL.bigSepL_nil] at Hcent
  obtain ⟨he0, he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, he11, he12, he13, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩ := Hcodes
  icases Hent with ⟨⟨%p0, %hp0, #Hp0⟩, ⟨%p1, %hp1, #Hp1⟩, ⟨%p2, %hp2, #Hp2⟩, ⟨%p3, %hp3, #Hp3⟩, ⟨%p4, %hp4, #Hp4⟩, ⟨%p5, %hp5, #Hp5⟩, ⟨%p6, %hp6, #Hp6⟩, ⟨%p7, %hp7, #Hp7⟩, ⟨%p8, %hp8, #Hp8⟩, ⟨%p9, %hp9, #Hp9⟩, ⟨%p10, %hp10, #Hp10⟩, ⟨%p11, %hp11, #Hp11⟩, ⟨%p12, %hp12, #Hp12⟩, ⟨%p13, %hp13, #Hp13⟩, ⟨%p14, %hp14, #Hp14⟩, ⟨%p15, %hp15, #Hp15⟩, ⟨%p16, %hp16, #Hp16⟩, ⟨%p17, %hp17, #Hp17⟩, ⟨%p18, %hp18, #Hp18⟩, ⟨%p19, %hp19, #Hp19⟩, ⟨%p20, %hp20, #Hp20⟩, ⟨%p21, %hp21, #Hp21⟩, -⟩
  icases Hcent with ⟨⟨%q0, %hq0, #Hq0⟩, ⟨%q1, %hq1, #Hq1⟩, ⟨%q2, %hq2, #Hq2⟩, -⟩
  -- the client maps' mutex and the writers' escrow
  have hρw : ρ.writers = gw := by subst hρ; rfl
  icases (ghostMapAuth_halves gw (∅ : GMap w32 Loc)).1 $$ Hw with ⟨Hw1, Hw2⟩
  imod sync.init_Mutex (iprop(∃ (RM WM : GMap w32 Loc), crm ↦$ RM ∗ cwm ↦$ WM ∗
      ghostMapAuth ρ.writers (1 : Qp).half WM ∗
      [∗map] hs ↦ _w ∈ WM, ∃ c : Nat, clientConnAt γ hs c ∗ placedConn γ c)) ⊤ mu
      $$ [Hmu] [Hcrm Hcwm Hw1] with #Hcmu
  · iexact Hmu
  · inext; iexists ∅, ∅; rw [hρw]; iframe; iapply BigSepM.bigSepM_empty.2; itrivial
  iapply fupd_wp
  imod inv_alloc netN.escrowN ⊤ (iprop(∃ WM : GMap w32 Loc, ghostMapAuth ρ.writers (1 : Qp).half WM ∗
      [∗map] hs ↦ w ∈ WM, netN.clientWriterB γ hs w ∨
        ghostMapElem (escrowName ρ) hs (DFrac.own 1) w)) $$ [Hw2] with #Hescinv
  · inext; iexists ∅; rw [hρw]; iframe; iapply BigSepM.bigSepM_empty.2; itrivial
  imodintro
  iunfold netN.statsOkB at HstatsOk
  icases HstatsOk with #HstatsOk
  ipersist Hsl'
  ihave #Hgp : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto $$ []
  · iPkgInit
  ihave #Hep : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto $$ []
  · iPkgInit
  ipersist HppoS
  ihave #HPPOk : ∃ pS' : GoSlice, gR.[src.genericsmr.Replica, go!"PreferredPeerOrder"] ↦□ pS' ∗
      pS' ↦*□ [W32 (((kr.val : Int) + 1) % 3), W32 (((kr.val : Int) + 2) % 3), rid32 kr] $$ []
  · have hps3 := ppo_list id hid ps (by rw [Hl.2.2.1, Hnl.1]) (by
      intro m hm; have := Hl.2.2.2.2.2 m (by rw [Hnl.1]; exact hm); rw [hN3] at this; exact this)
    have e : [W32 (((kr.val : Int) + 1) % 3), W32 (((kr.val : Int) + 2) % 3), rid32 kr] = ps := by
      rw [hps3]; rfl
    iexists ppoS
    rw [e]
    iframe #
  icases HPPOk with ⟨%pS', #HPPO', #HpS'⟩
  ihave #HgOk : genericOk γ ρ kr «$r0_ptr» gR h $$ []
  · unfold genericOk genericFixed
    imodintro
    iexists rt, ct, st, mu, cwm, crm, M, CM
    isimp [netKinds, reqKinds, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil, c_prepare,
      c_prepareReply, c_preAccept, c_preAcceptReply, c_preAcceptOK, c_accept,
      c_acceptReply, c_commit, c_executed, c_read1, c_read2, c_write1, c_write2, c_read1Reply,
      c_read2Reply, c_write1Reply, c_write2Reply, c_read, c_write, c_rmw, kindTy, reqTy, reqCode,
      netN.kindCode, netN.statsOkB]
    iframe #
    ipureintro
    rw [he0, he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, he11, he12, he13, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8] at *
    simp only [gryffRead, gryffWrite, gryffRMW]
    refine ⟨⟨⟨_, rfl, hp0⟩, ⟨_, rfl, hp1⟩, ⟨_, rfl, hp2⟩, ⟨_, rfl, hp3⟩, ⟨_, rfl, hp4⟩,
      ⟨_, rfl, hp5⟩, ⟨_, rfl, hp6⟩, ⟨_, rfl, hp7⟩, ⟨_, rfl, hp11⟩, ⟨_, rfl, hp14⟩, ⟨_, rfl, hp15⟩,
      ⟨_, rfl, hp16⟩, ⟨_, rfl, hp17⟩, ⟨_, rfl, hp18⟩, ⟨_, rfl, hp19⟩, ⟨_, rfl, hp20⟩,
      ⟨_, rfl, hp21⟩⟩, ⟨⟨_, rfl, hq0⟩, ⟨_, rfl, hq1⟩, ⟨_, rfl, hq2⟩⟩, Hnl.1, ?_⟩
    simp
  -- the handle
  ipersist HBeacon
  ipersist HDurable
  ihave #HisRep : isReplica γ ρ kr «$r0_ptr» $$ [Hchans]
  · unfold isReplica
    iexists gR, h
    iframe; iframe #
  -- `connectRes`: what `run` starts from
  have hesc : escrowName ρ = gesc := by subst hρ; rfl
  have c_propose : ρ.chans "propose" = γprop := by subst hρ; rfl
  obtain ⟨haddr, haddr2⟩ := addrOf_split k hk
  icases predsSet_at γ.proto kr $$ Hpreds with ⟨%ws, #Hpw⟩
  iunfold idSlotRes at Hslot
  icases Hslot with ⟨Htr, Hr0, Hr1, Hr2⟩
  ihave ⟨Hrxp, Hrxk⟩ := rxCur_split γ.proto kr $$ [Hr0 Hr1 Hr2]
  · iframe
  ipersist HStore
  ipersist HdS
  iapply fupd_wp
  imod registry_ports γ k id nodes kr $$ [] with Hregistry
  · iframe #
  imodintro
  ihave #Hlisk : replicaLis γ k $$ []
  · have hmem : k ∈ [0, 1, 2] := by rcases k with _ | _ | _ | k <;> simp; omega
    iapply BigSepL.bigSepL_mem (Φ := fun j => replicaLis γ j) hmem $$ Hprotos
  ihave #Hpinv := sharedInvs_proto γ $$ Hsh
  iunfold replicaLis at Hlisk
  ihave HconnRes : connectRes γ ρ kr «$r0_ptr» gR $$ [HpS HrS HwS HaS HList Htr Hrxp
      Hrxk Hproph Hboot2 Hpa Hco HsmR HpropO «$v34» «$v35» «$v36» «$v37» Hesc Hms Hregistry]
  · unfold connectRes
    iexists sl', pS, rS, wS, aS, nodes, portAddr k, ws
    rw [Hnl.1] at *
    rw [hρboot]
    icases Hregistry with ⟨Hreg1, Hreg2⟩
    iframe; iframe #
    isplitr
    · ipureintro; refine ⟨rfl, ?_⟩; have := Hnl.2; simp only [kr]; rw [this]; congr 1
    isplitl [Htr Hproph Hpa Hco HsmR HpropO «$v34» «$v35» «$v36» «$v37»]
    · unfold bootRest
      iexists p, gR, pa, co, h
      rw [stOf_nil]
      unfold replicaIface handlerIface
      iframe; iframe #
      isplitl [HsmR]
      · unfold valOwn; iexists stl, smR, ∅; iframe; iframe #
        ipureintro; exact ⟨fun _ _ => by simp, by simp [RState.init]⟩
      isplitl [HpropO]
      · unfold proposeOwn; iexists propC, []; rw [c_propose]; iframe; iframe #
        isplitr
        · ipureintro; rfl
        iapply BigSepL.bigSepL_nil.2; iempintro
      isplitl [«$v34» «$v35» «$v36» «$v37»]
      · unfold scratchOwn; iexists _, _, _, _, _, _, _, _; iframe; iframe #
        ipureintro; rfl -- H1e-1: the zero `Read1Proxied`'s `D` is `dep0`
      ipureintro; rfl
    unfold clientsOwn
    isplitl [Hesc]
    · iexists ∅; rw [hesc]; iframe; iapply BigSepM.bigSepM_empty.2; itrivial
    iexists dS, ms; iframe #
    isplitr
    · ipureintro; rw [← Hnl.1]; exact Hl.2.2.2.1
    iapply BigSepL.bigSepL_mono $$ Hms
    intro i mp hmp
    iintro Hm; iexists ∅; iframe; ipureintro; intro c b hc; simp at hc
  -- `go r.run()`, then `return r`
  wp_apply wp_fork $$ [HconnRes]
  · wp_apply (wp_run γ ρ kr «$r0_ptr» gR) $$ [HconnRes]
    · iframe; iframe #
    itrivial
  try wp_auto
  iapply HΦ
  isplitr
  · iapply replicaOk_intro L RL γ «$r0_ptr» gR hr0nn; iframe #
  iexists ρ, kr
  iframe #
  ipureintro; rfl

end

end Perennial.gryff.unitB
