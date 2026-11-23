/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/Helpers.lean`, run `rabia-r1wake-1`.)

The consensus package's small helpers' specs (internal): the term checks (no slot is reused: the
term is always 0), the pending queue (`QPush`, `QPop`), `toNet`, the coin.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.Basics
public import Dsverify.Proof.math.rand.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

/-- Discharge the bounds check of an `IndexRef`. -/
local macro "slice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions] [π : NetProtoGS]

/-- `c.UpdateTermIfNecessary(seq, pan)` of a slot number below `LenLedger`: the term is 0.
(Its branch that resets a slot under `Slot.Lock` is unreachable in this scope, no slot being
reused; were it reachable, it would need a spec of `Reset` under the lock, from `slotInv` and
`Slot.wp_wakeWaiters` (R1-wake), which `Slot.Reset.spec`, about a zero slot, is not.) -/
theorem wp_UpdateTermIfNecessary (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) (seq : w32) (pan : Bool) (hs : seq.toNat < lenLedger) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ confRO cf ∗
        consRO γ cf k γl γc ch c }}
      (App (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"UpdateTermIfNecessary"))
        (Val #seq)) (Val #pan))
    {{ RET #true; True }} := by
  wp_start as ⟨#Hconf, #Hro⟩
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  unfold consRO
  icases Hro with ⟨%ledger, %ql, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
    #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
  unfold ledgerRO
  icases HLro with ⟨#Hsl, %Hlen, #Hslots⟩
  have hlen : (W32 10000).toNat = 10000 := by decide
  obtain ⟨e, he⟩ : ∃ e, γl.slots[seq.toNat]? = some e :=
    Option.isSome_iff_exists.mp (by simp [Hlen]; exact hs)
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  unfold lenLedger at hs Hl
  ihave #Hse := (BigSepL.bigSepL_lookup
    (Φ := fun _ e => iprop(isSlot (GF := GF) e.loc e.γ e.q)) he) $$ Hslots
  ihave ⟨#Hq, #Ht⟩ := isSlot_queue e.loc e.γ e.q $$ Hse
  wp_auto
  have hmod : seq % W32 10000 = seq := by word
  have hdiv : seq / W32 10000 = W32 0 := by word
  rw [hmod, hdiv]
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z seq))) _ _ e.loc (by word) $$ [Hsl]
    with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z seq))).toNat = seq.toNat by word]
    simp [he]
  wp_auto
  iapply HΦ; itrivial

/-- `c.IsTermMatched(seq)` of a slot number below `LenLedger`. -/
theorem wp_IsTermMatched (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) (seq : w32) (hs : seq.toNat < lenLedger) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ confRO cf ∗
        consRO γ cf k γl γc ch c }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"IsTermMatched")) (Val #seq))
    {{ RET #true; True }} := by
  wp_start as ⟨#Hconf, #Hro⟩
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  unfold consRO
  icases Hro with ⟨%ledger, %ql, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
    #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
  unfold ledgerRO
  icases HLro with ⟨#Hsl, %Hlen, #Hslots⟩
  have hlen : (W32 10000).toNat = 10000 := by decide
  obtain ⟨e, he⟩ : ∃ e, γl.slots[seq.toNat]? = some e :=
    Option.isSome_iff_exists.mp (by simp [Hlen]; exact hs)
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  unfold lenLedger at hs Hl
  ihave #Hse := (BigSepL.bigSepL_lookup
    (Φ := fun _ e => iprop(isSlot (GF := GF) e.loc e.γ e.q)) he) $$ Hslots
  ihave ⟨#Hq, #Ht⟩ := isSlot_queue e.loc e.γ e.q $$ Hse
  wp_auto
  have hmod : seq % W32 10000 = seq := by word
  have hdiv : seq / W32 10000 = W32 0 := by word
  rw [hmod, hdiv]
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z seq))) _ _ e.loc (by word) $$ [Hsl]
    with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z seq))).toNat = seq.toNat by word]
    simp [he]
  iapply HΦ; itrivial


/-- `c.PanicTermNotMatched(seq)` of a slot number below `LenLedger`: no panic. -/
theorem wp_PanicTermNotMatched (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) (seq : w32) (hs : seq.toNat < lenLedger) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ confRO cf ∗
        consRO γ cf k γl γc ch c }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"PanicTermNotMatched"))
        (Val #seq))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hconf, #Hro⟩
  wp_auto
  wp_apply wp_IsTermMatched γ k γl γc ch c seq hs $$ [$Hconf $Hro]
  iapply HΦ; itrivial

/-- `c.QPush(obj)`: a pending object into the pending queue. -/
theorem wp_QPush (hPush : heapPush.spec (GF := GF)) (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) (v : ConsensusObj) (o : ObjV) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗
        consRO γ cf k γl γc ch c ∗ objRep v o ∗ pendOk γ cf γl o }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"QPush")) (Val #v))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hro, #Hv, Hok⟩
  unfold consRO
  icases Hro with ⟨%ledger, %ql, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
    #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$HQm] as ⟨Hlocked, Hinv⟩
  unfold pqInv
  icases Hinv with ⟨%xs, Hq, Hoks⟩
  ihave #Hqpkg : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.queue $$ [Hpkg]
  · iPkgInit
  have hP := hPush (structFieldRef Consensus go!"Queue" c) xs v o
  simp only [pqIface] at hP
  wp_apply hP $$ [$Hqpkg $Hq $Hv] as ⟨%xs', %hperm, Hq⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$HQm $Hlocked Hq Hoks Hok]
  · inext
    iexists xs'
    iframe Hq
    iapply (BigSepL.bigSepL_perm (PROP := IProp GF) (Φ := fun o => pendOk (GF := GF) γ cf γl o) hperm).2
    iapply BigSepL.bigSepL_cons.2
    iframe
  iapply HΦ; itrivial

/-- `c.QPop()`: a pending object, or none. -/
theorem wp_QPop (hPop : heapPop.spec (GF := GF)) (hLen : PQueue.Len.spec (GF := GF))
    (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗
        consRO γ cf k γl γc ch c }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"QPop")) (Val #()))
    {{ (v : ConsensusObj) (ok : Bool), RET (PairV #v #ok);
        if ok then ∃ o, objRep v o ∗ pendOk γ cf γl o else True }} := by
  wp_start as #Hro
  unfold consRO
  icases Hro with ⟨%ledger, %ql, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
    #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
  ihave #Hqpkg : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.queue $$ [Hpkg]
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$HQm] as ⟨Hlocked, Hinv⟩
  unfold pqInv
  icases Hinv with ⟨%xs, Hq, Hoks⟩
  wp_apply hLen (structFieldRef Consensus go!"Queue" c) xs slice.nil $$ [$Hqpkg $Hq] as Hq
  wp_if_destruct
  · wp_apply sync.Mutex.wp_Unlock $$ [$HQm $Hlocked Hq Hoks]
    · inext; iexists xs; iframe
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · have hne : xs ≠ [] := by
      intro h; subst h; simp at *
    have hP := hPop (structFieldRef Consensus go!"Queue" c) xs hne
    simp only [pqIface] at hP
    wp_apply hP $$ [$Hqpkg $Hq] as %v ⟨%o, %xs', %hperm, #Hv, Hq⟩
    ihave ⟨Hok, Hoks⟩ := (BigSepL.bigSepL_cons (PROP := IProp GF)
      (Φ := fun _ o => pendOk (GF := GF) γ cf γl o)).1 $$
      [Hoks]
    · iapply (BigSepL.bigSepL_perm (PROP := IProp GF) (Φ := fun o => pendOk (GF := GF) γ cf γl o)
        hperm).2 $$ Hoks
    wp_apply sync.Mutex.wp_Unlock $$ [$HQm $Hlocked Hq Hoks]
    · inext; iexists xs'; iframe
    iapply HΦ
    simp only [↓reduceIte]
    iexists o; iframe Hok Hv

/-- `c.toNet(msg)`: the executor's next message of `E_k`. -/
theorem wp_toNet (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) (v : Msg) (sent : List Msg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗
        consRO γ cf k γl γc ch c ∗ spscProducer γl.e2n sent ∗ e2nP γ cf k γl sent.length v }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"toNet")) (Val #v))
    {{ RET #(); spscProducer γl.e2n (sent ++ [v]) }} := by
  wp_start as ⟨#Hro, Hp, HP⟩
  unfold consRO
  icases Hro with ⟨%ledger, %ql, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
    #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
  unfold srvChans
  icases HCh with ⟨-, -, -, -, -, #He, -⟩
  wp_auto
  wp_apply wp_spsc_send γl.e2n ch.e2n (e2nP γ cf k γl) (fun _ => iprop(False)) sent v $$ [$He $Hp $HP]
    as Hp
  iapply HΦ $$ Hp

/-- The `Coin` field holds a usable `*rand.Rand` (owned by the executor). -/
def coinOk (c : Loc) : IProp GF :=
  iprop(∃ (r : Loc) (v : math.rand.Rand), structFieldRef Consensus go!"Coin" c ↦ r ∗ r ↦ v)

/-- `c.ResetCommonCoin()`: a fresh `Rand` in `Coin`. -/
theorem wp_ResetCommonCoin [math.rand.Hyps GF] (c : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗
        ∃ coin : Loc, structFieldRef Consensus go!"Coin" c ↦ coin }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"ResetCommonCoin")) (Val #()))
    {{ RET #(); coinOk c }} := by
  wp_start as ⟨%coin, Hc⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.math.rand $$ [Hpkg]
  · iPkgInit
  wp_auto
  wp_apply (math.rand.Hyps.NewSource (GF := GF)) $$ [$Hrpkg] as %src -
  wp_apply (math.rand.Hyps.New (GF := GF)) $$ [$Hrpkg] as %r ⟨%v, Hr⟩
  iapply HΦ
  unfold coinOk
  iexists r, v
  iframe

/-- `c.CommonCoinFlip()`: some bit. -/
theorem wp_CommonCoinFlip [math.rand.Hyps GF] (c : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ coinOk c }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"CommonCoinFlip")) (Val #()))
    {{ (x : w32), RET #x; coinOk c ∗ ⌜x.toNat ≤ 1⌝ }} := by
  wp_start as H
  unfold coinOk
  icases H with ⟨%r, %v, Hc, Hr⟩
  wp_auto
  wp_apply (math.rand.Hyps.Rand_Intn (GF := GF)) r v (W64 2) (by decide) $$ [$Hr] as %x ⟨Hr, %hx⟩
  iapply HΦ
  isplitl
  · iexists r, v; iframe
  · ipureintro; word

end spec

end Perennial.rabia.roles.server.layers.consensus
