/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ConsensusInit.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/roles/server/layers/consensus.ConsensusInit`.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.Spec
public import Dsverify.Proof.rabia.internal.logger.Spec
public import Perennial.Proof.sync

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model NetConn Dsv rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions]

theorem ConsensusInit.wp_proof
    (wp_InitLogger : rabia.internal.logger.InitLogger.spec (GF := GF) (hG := hG))
    (wp_heapInit : rabia.internal.queue.heapInit.spec (GF := GF) (hG := hG)) :
    ConsensusInit.spec (GF := GF) := by
  intro γ cf k γl γc ch id wg ledger hid hk
  have hbl : cf.blockLen ≤ 10 := by
    unfold RCfg.blockLen
    generalize cf.blocks = b
    match b with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | _ + 4 => simp
  wp_start as ⟨#Hconf, #Hch, #Hled, #Hsi, Hsr, Hboot⟩
  ihave #Hlog : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.logger $$ [Hpkg]
  · iPkgInit
  wp_alloc res0 as Hres0
  wp_pures
  wp_apply (wp_alloc (V := GoSlice) (t := Ledger.ty) ledger) as %pled Hpled
  wp_apply wp_InitLogger $$ [$Hlog $Hconf] as %lg0 _
  wp_apply wp_InitLogger $$ [$Hlog $Hconf] as %lg2 _
  ihave ⟨%cps, #Hc⟩ := rabia.internal.config.confRO_val $$ Hconf
  iStructNamed Hc
  wp_apply (wp_slice_make2 (V := ConsensusObj) (st := PQueue.ty) (W64 0)) as %qsl ⟨Hqsl, Hqcap⟩
  · ipureintro; decide
  wp_pures
  irename «$v9» => Hqlk
  wp_apply (wp_map_make1 (K := w64) (V := Bool) go.uint64 go.bool) as %dmap Hdmap
  wp_apply (wp_slice_make2 (V := w64) (st := go.GoType.SliceType go.int) _) as %rsl ⟨Hrsl, Hrcap⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := w64) (st := go.GoType.SliceType go.int) _) as %psl ⟨Hpsl, Hpcap⟩
  · ipureintro; word
  iStructNamed «$r0»
  ihave #Hq : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.queue $$ [Hpkg]
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ [Hpkg]
  · iPkgInit
  have hInit := wp_heapInit (structFieldRef Consensus go!"Queue" «$r0_ptr») []
  simp only [pqIface] at hInit
  wp_apply +noauto hInit $$ [$Hq Queue Hqsl Hqcap] as ⟨%xs, %Hxs, Hpq⟩
  · unfold pqOwn
    iexists qsl, []
    iframe
    isplitr
    · ipureintro; rfl
    · iapply BigSepL.bigSepL_nil.2; iempintro
  have Hxs' : xs = [] := List.Perm.nil_eq Hxs.symm |>.symm
  subst Hxs'
  iapply fupd_wp
  imod sync.init_Mutex (pqInv γ cf γl «$r0_ptr») ⊤ «$v9_ptr» $$ Hqlk [Hpq] with #Hqm
  · inext; unfold pqInv; iexists []; iframe Hpq; iapply BigSepL.bigSepL_nil.2; iempintro
  imod sync.init_Mutex (statInv «$r0_ptr») ⊤ (structFieldRef Consensus go!"StatLock" «$r0_ptr»)
    $$ StatLock [NormalSlots UnmatchedSlots NullSlots NumClientBatchedRequests] with #Hsm
  · inext; unfold statInv; iexists _, _, _, _; iframe
  ipersist SvrId
  ipersist Wg
  ipersist Done
  ipersist NetToMsgHandler
  ipersist MsgHandlerToNet
  ipersist NetToConExecutor
  ipersist ConExecutorToNet
  ipersist QLock
  ipersist Ledger
  imodintro
  wp_auto
  have hid' : id = W32 (k : Int) := by
    apply BitVec.eq_of_toNat_eq; subst hid; simp
  subst hid'
  unfold consensusBootRes
  icases Hboot with ⟨Hn2h, He2n, Hex, Hkp, #Hkeys⟩
  unfold consSlotsRes
  icases Hsr with ⟨Hfrz, Hsl⟩
  icases (BigSepL.bigSepL_sep_eqv (Φ := fun s e => slotChan (GF := GF) γ cf γc s e)
    (Ψ := fun s e => iprop(slotExecPart (GF := GF) γl γc s e ∗ slotHandlerPart γl γc s))).1 $$ Hsl
    with ⟨#Hchans, Hsl⟩
  icases (BigSepL.bigSepL_sep_eqv (Φ := fun s e => slotExecPart (GF := GF) γl γc s e)
    (Ψ := fun s _e => slotHandlerPart (GF := GF) γl γc s)).1 $$ Hsl with ⟨Hexs, Hhs⟩
  ihave #Hro : consRO γ cf k γl γc ch «$r0_ptr» $$ []
  · unfold consRO
    iexists ledger, «$v9_ptr», wg
    iframe #
  iapply HΦ
  isplitl [SvrSeq Coin Discard Hdmap CurrConsecutiveNulls MaxConsecutiveNulls
    MaxConsecutiveNullsEndSeq TotalRounds NumOfRoundsDist Hrsl Hexs He2n Hex Hkp]
  · unfold consExecRes
    have e : (W64 (2 ^ 64 - 1) : w64) = W64 (-1) := by decide
    rw [e]
    iframe Hro SvrSeq Hexs He2n Hex Hkp
    isplitl [Coin]
    · iexists _; iexact Coin
    isplitl [Discard Hdmap]
    · iexists dmap; iframe
    isplitl [CurrConsecutiveNulls MaxConsecutiveNulls MaxConsecutiveNullsEndSeq]
    · iexists _, _, _; iframe
    isplitl [TotalRounds]
    · iexists _; iexact TotalRounds
    · isplitl [NumOfRoundsDist Hrsl]
      · iexists rsl, _
        iframe
        ipureintro
        simp only [List.length_replicate]
        word
      · ipureintro; exact hk
  isplitl [OlderThanTermMsg Hfrz Hhs Hn2h]
  · unfold consHandlerRes
    iframe Hro Hfrz Hhs Hn2h
    iexists _; iexact OlderThanTermMsg
  · unfold consStatsRO
    iexact Hsm

end proof
end Perennial.rabia.roles.server.layers.consensus
