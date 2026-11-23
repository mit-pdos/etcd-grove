/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/FastAckLemmas.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Lemmas for `fastAckFromLeader` (round 10, notes/prove-swift.md §16): a replica's own
pre-acceptance fact (`sp.preacc γ r b y D`) is its row (`sp.preacc_own`, `swift.preacc_row`):
at the ballot's leader, its own ack's witness (`sp.fastAckOk`: `preacc γ L b x D`) says that
`x`'s row token is pre-accepted, so (`rowAcc`) the descriptor has its proposal and
`afterPropagate`'s condition is true. These open `sp.inv`'s body (T2-1, as Steps.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcceptPre
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.IdBound
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp
section ghost
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]
variable {γ : Names} {γc γm γl : GName}

/-- A replica's own pre-acceptance fact is in its state (an identity step of `node_step`). -/
theorem preacc_own (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (b : Nat) (y : CmdId) (D : List CmdId) (hr : r < N)
    (hk : nodeOf l r = some k) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ preacc γ r b y D ⊢
    |={E}=> nodeSt γ k (1 : Qp).half st ∗ ⌜st.preAt b y = some D⌝ := by
  iintro ⟨#Hinv, #Hcfg, Hst, #Hpre⟩
  imod node_step E hE N fr l r k st none
    (fun s' => iprop(⌜s' = st ∧ st.preAt b y = some D⌝)) hr hk $$ [Hst]
    with ⟨%st', Hst, -, %Heq⟩
  · iframe Hinv Hcfg Hst
    isplitl []
    · iunfold predPre; itrivial
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    iunfold preacc at Hpre
    ihave %HlkP := ghost_map_lookup $$ HP Hpre
    have hpre : S.pre r b y = some D := by rw [← Hrepr.pre]; exact HlkP
    have hrow := (HI.rows_ok r b).2.2.1 y
    imodintro
    iexists S, mL, mS, mA, mP, mCo, mR, mPa
    iframe
    ipureintro
    refine ⟨⟨HI, Hsr, Hrepr, rfl, rfl, PState.le_refl S, fun _ _ => rfl, rfl⟩, Hrs, ?_⟩
    rw [Hrs] at hrow; rw [← hrow]; exact hpre
  obtain ⟨rfl, h⟩ := Heq
  imodintro
  iframe Hst
  ipureintro; exact h

/-- A replica's own acceptance fact is in its state (round 30, G15; `preacc_own`'s analog). -/
theorem accepted_own (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (b : Nat) (y : CmdId) (hr : r < N)
    (hk : nodeOf l r = some k) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ accepted γ r b y ⊢
    |={E}=> nodeSt γ k (1 : Qp).half st ∗ ⌜(b, y) ∈ st.accR⌝ := by
  iintro ⟨#Hinv, #Hcfg, Hst, #Hacc⟩
  imod node_step E hE N fr l r k st none
    (fun s' => iprop(⌜s' = st ∧ (b, y) ∈ st.accR⌝)) hr hk $$ [Hst]
    with ⟨%st', Hst, -, %Heq⟩
  · iframe Hinv Hcfg Hst
    isplitl []
    · iunfold predPre; itrivial
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    iunfold accepted at Hacc
    ihave %HlkA := ghost_map_lookup $$ HA Hacc
    have hacc : S.acc r b y := (Hrepr.acc r b y).1 (by simp [HlkA])
    have hrow := (HI.rows_ok r b).2.1 y
    imodintro
    iexists S, mL, mS, mA, mP, mCo, mR, mPa
    iframe
    ipureintro
    refine ⟨⟨HI, Hsr, Hrepr, rfl, rfl, PState.le_refl S, fun _ _ => rfl, rfl⟩, Hrs, ?_⟩
    rw [Hrs] at hrow; exact hrow.1 hacc
  obtain ⟨rfl, h⟩ := Heq
  imodintro
  iframe Hst
  ipureintro; exact h

/-- **A pre-acceptance's dependencies are few** (round 47, 46-2): `pre_ok` makes them `depsIn` of
the replica's sequence, whose ids are registered and distinct (`loc_ok`), hence small (the
invariant's client bound, `swift.small_ids_len`); so `D` has fewer than `2 ^ 62` entries (what
`replyPre` asks of an adopted dependency list, `swift.repPre_adopt`). -/
theorem preacc_depWf (r b : Nat) (y : CmdId) (D : List CmdId) :
    inv γ γc γm γl ∗ preacc γ r b y D ⊢ |={↑spN}=> ⌜D.length < 2 ^ 62⌝ := by
  unfold inv preacc
  iintro ⟨#Hinv, #Hp⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, HS, HA, >HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, >Hproto, HQs, >%Hcl, >%HDom, Hcmds, Hconns⟩
  ihave %Hlk := ghost_map_lookup $$ HP Hp
  have hpre : S.pre r b y = some D := by rw [← Hrepr.pre]; exact Hlk
  icases Hproto with (%He | ⟨%N, %fr, %l, #Hcfg, %Hq⟩)
  · exfalso; rw [He.1.2.2.2.1 r b y] at hpre; cases hpre
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    isplitr
    · iright; iexists N, fr, l; iframe Hcfg; ipureintro; exact Hq
    ipureintro; exact ⟨Hcl, HDom⟩
  imodintro
  ipureintro
  obtain ⟨-, -, -, hD, -⟩ := Hq.1.pre_ok r b y D hpre
  obtain ⟨hnd, hreg, -⟩ := Hq.1.loc_ok r b
  have hsm : ∀ z ∈ S.loc r b, swift.idSmall z := fun z hz => by
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hreg z hz)
    have hlk : mC.lookup z = some c := by rw [Hrepr.cmds]; exact hc
    obtain ⟨⟨n, hn, -⟩, -⟩ := Hcl z c hlk
    exact HDom.2 z.cl n hn
  have h1 := swift.small_ids_len _ hnd hsm
  have h2 := depsIn_length (S.seqOf (S.loc r b)) y
  have h3 : (S.seqOf (S.loc r b)).length ≤ (S.loc r b).length := List.length_filterMap_le _ _
  rw [hD]; omega

/-- **A pre-acceptance is not of the ballot's base** (round 56, D79 (2), R2-a): `pre_ok` gives the
command a path, and `path_ok` keeps it out of `base b`, the order of `b`'s `MSync`. -/
theorem preacc_notBase (r b : Nat) (y : CmdId) (D : List CmdId) (M : SyncMsg) :
    inv γ γc γm γl ∗ preacc γ r b y D ∗ syncIs γ b M ⊢ |={↑spN}=> ⌜y ∉ syncOrder M⌝ := by
  unfold inv preacc syncIs
  iintro ⟨#Hinv, #Hp, #HM⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, >HS, HA, >HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, >Hproto, HQs, >%Hcl, >%HDom, Hcmds, Hconns⟩
  ihave %Hlk := ghost_map_lookup $$ HP Hp
  have hpre : S.pre r b y = some D := by rw [← Hrepr.pre]; exact Hlk
  ihave %HlkM := ghost_map_lookup $$ HS HM
  have hS : S.sync b = some M := by rw [← Hrepr.sync]; exact HlkM
  icases Hproto with (%He | ⟨%N, %fr, %l, #Hcfg, %Hq⟩)
  · exfalso; rw [He.1.2.2.2.1 r b y] at hpre; cases hpre
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    isplitr
    · iright; iexists N, fr, l; iframe Hcfg; ipureintro; exact Hq
    ipureintro; exact ⟨Hcl, HDom⟩
  imodintro
  ipureintro
  obtain ⟨-, -, -, -, hpath⟩ := Hq.1.pre_ok r b y D hpre
  obtain ⟨P, hP⟩ := Option.ne_none_iff_exists'.mp hpath
  obtain ⟨-, hnb, -⟩ := Hq.1.path_ok r b y P hP
  unfold PState.base at hnb
  rw [hS] at hnb
  exact hnb

end ghost
end sp

section dstep
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- **The replica's own pre-acceptance of `y` in its epoch `b` is `y`'s row token's**. -/
theorem swift.preacc_row (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N r k : Nat)
    (fr : Bool) (l : List GoString) (q : Qp) (b : Nat) (y : sp.CmdId) (D : List sp.CmdId)
    (rv : swift.RowV) (hr : r < N) (hk : nodeOf l r = some k) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv ∗ sp.preacc γ r b y D ⊢
    |={⊤}=> swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv ∗ ⌜rv.1 = some D⌝ := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hep, Htok, #Hpre⟩
  iapply (swift.desc_upd γ γv γe γo k q b y rv rv (fun st => st) iprop(⌜rv.1 = some D⌝)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ _ hacc => hacc)
    (fun st hrv b' y' => by
      split
      · rename_i h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hrv.symm
      · rfl))
  iframe Hninv Hep Htok
  iintro %st ⟨%hb, %hc, %hrv, %hyl⟩ Hst
  subst hb
  imod (sp.preacc_own (⊤ \ ↑swift.nodeN) swift.nodeN_diff N fr l r k st st.ballot y D hr hk)
    $$ [Hst] with ⟨Hst, %h⟩
  · iframe Hinv Hcfg Hst Hpre
  imodintro
  iframe Hst
  ipureintro
  rw [hrv]; simp only [swift.rowsOf]; exact h

/-- **The replica's own acceptance of `y` in its epoch `b` is in `y`'s row token** (round 30,
G15: refutes a sync entry's `pdOk` against a proposal's fresh token). -/
theorem swift.accepted_row (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N r k : Nat)
    (fr : Bool) (l : List GoString) (q : Qp) (b : Nat) (y : sp.CmdId)
    (rv : swift.RowV) (hr : r < N) (hk : nodeOf l r = some k) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv ∗ sp.accepted γ r b y ⊢
    |={⊤}=> swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv ∗ ⌜rv.2.2.1 = true⌝ := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hep, Htok, #Hacc⟩
  iapply (swift.desc_upd γ γv γe γo k q b y rv rv (fun st => st) iprop(⌜rv.2.2.1 = true⌝)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ _ hacc => hacc)
    (fun st hrv b' y' => by
      split
      · rename_i h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hrv.symm
      · rfl))
  iframe Hninv Hep Htok
  iintro %st ⟨%hb, %hc, %hrv, %hyl⟩ Hst
  subst hb
  imod (sp.accepted_own (⊤ \ ↑swift.nodeN) swift.nodeN_diff N fr l r k st st.ballot y hr hk)
    $$ [Hst] with ⟨Hst, %h⟩
  · iframe Hinv Hcfg Hst Hacc
  imodintro
  iframe Hst
  ipureintro
  rw [hrv]; simp only [swift.rowsOf]; simp [h]

end dstep

end Perennial.github_com.imdea_software.swiftpaxos
