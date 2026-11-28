/-
(hraft_robust R5b) **`NewRaft` after the restore**: reading gprot's facts of the boot's crash state
(`bootPeek`), the restore's post in one form (`restore_unify`), and the configuration scan's facts
(`cfgFacts`, a copy of `Raft__appendEntries`' `aeCfg.cfgFacts`, whose module is a proof). A defs module of
`NewRaft`'s proof.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.NewRaftBoot
public import Dsverify.Proof.github_com.hashicorp.raft.InstallBase
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.CfgLog

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section pure
variable [GooseExts]

/-- (hraft_robust R5b) The latest snapshot's index and term as Go values (`0`: none). -/
def latIdxW (lat : SnapLatest) : w64 :=
  match lat with
  | none => W64 0
  | some (m, _) => m.Index'

def latTermW (lat : SnapLatest) : w64 :=
  match lat with
  | none => W64 0
  | some (m, _) => m.Term'

theorem latIdxW_nat (lat : SnapLatest) : uint.nat (latIdxW lat) = latIdx lat := by
  rcases lat with _ | ⟨m, b⟩ <;> rfl

theorem latTermW_nat (lat : SnapLatest) : uint.nat (latTermW lat) = latTerm lat := by
  rcases lat with _ | ⟨m, b⟩ <;> rfl

/-- (hraft_robust R5b) The restore's configurations: none (no snapshot), or the latest snapshot's, both
committed and latest. -/
def cfgBoot (lat : SnapLatest) (ccfg : Configuration) (cidx : w64) (cfg : Configuration) (li : w64) : Prop :=
  match lat with
  | none => ccfg = zero_val Configuration ∧ cidx = W64 0 ∧ cfg = zero_val Configuration ∧ li = W64 0
  | some (m, _) => ccfg = m.Configuration' ∧ cidx = m.ConfigurationIndex' ∧ cfg = m.Configuration' ∧
      li = m.ConfigurationIndex'

/-- (hraft_robust R5b) What `NewRaft` needs of the protocol state `s` at the boot (`boot_facts`). -/
def bootF (γ : GNames) (s : SState) (lat : SnapLatest) (dp : Option DiscPend) : Prop :=
  s.log.length < 2 ^ 62 ∧ s.dur.1 ≤ s.log.length ∧
  (∀ k e, ent s.log k = some e →
    (e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kBarrier ∨ e.kind = kConfig) ∧
    (e.kind = kConfig → ∃ ss : List Server, e.data = encodeServers ss ∧ srvsOk γ ss)) ∧
  (∀ d, dp = some d → s.dur.1 < d.x) ∧
  (dp = none → latIdx lat ≤ s.dur.1 ∧ (lat ≠ none → ∃ e, ent s.log (latIdx lat) = some e ∧ e.term = latTerm lat))

theorem gprotN_durN : (↑gprotN : CoPset) ⊆ ⊤ \ ↑durN := gprotN_diff_raft "dur"

end pure

section scan
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
include hRB

variable (γ : GNames) (rc : RCtx GF) (i : SID)

instance latDurLb_timeless (lat : SnapLatest) (dp : Option DiscPend) : Timeless (latDurLb (GF := GF) γ i lat dp) := by
  unfold latDurLb durLb; rcases lat with _ | ⟨_, _⟩ <;> infer_instance

theorem durStores_dlb (X : SrvDur) (hp : X.pend = none) :
    durStores γ rc i X ⊢ durStores γ rc i X ∗ latDurLb γ i X.lat X.dp := by
  unfold durStores
  iintro ⟨HL, HS, HSS, Hld⟩
  ihave ⟨Hld, #Hdl⟩ := latestDur_dlb γ rc i X.lat X.pend X.dp hp $$ Hld
  iframe
  iexact Hdl

/-- (hraft_robust R5b) **gprot's facts of the boot's crash state**: with the invariant opened (the main
goroutine's view pins the protocol state `s`), a ghost update of `srvOwn γ i s` that gives `Q`. -/
theorem bootPeek {E : CoPset} (hE : ↑durN ⊆ E) (A : LogAbs) (lat : SnapLatest) (s : SState)
    (tp : Option TermPend) (dp : Option DiscPend) (Q : IProp GF) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ∗ srvVP rc s tp dp ∗
      ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
      (∀ X : SrvDur, ⌜X.A = A ∧ X.lat = lat ∧ X.s = s ∧ X.tp = tp ∧ X.dp = dp ∧ durPure X⌝ -∗
        latDurLb γ i lat dp -∗ srvOwn γ i X.s ={E \ ↑durN}=∗ srvOwn γ i X.s ∗ Q) ⊢
      |NC={E}=> bootV rc A lat ∗ srvVP rc s tp dp ∗
        ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗ Q := by
  iintro ⟨#Hi, Hv, Hsv, Hpe, HQ⟩ Hnc
  imod (bootOpen γ rc i hE A lat) $$ [Hv] Hnc with ⟨Hnc, %X, %HX, Hc, Hs, Hcl⟩
  · iframe #; iframe
  ihave ⟨Hc, %Hp⟩ := durCoreB_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCoreB_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  iunfold durCoreB at Hc
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, %Hp', H10, H11, H12, H13, H14⟩
  icombine Hpe H11 gives %hpe
  ihave Hs := later_mono (durStores_dlb γ rc i X hpe.2.symm) $$ Hs
  icases Hs with ⟨Hs, >#Hdl⟩
  have hpq : X.A = A ∧ X.lat = lat ∧ X.s = s ∧ X.tp = tp ∧ X.dp = dp ∧ durPure X :=
    ⟨HX.1, HX.2, Hag.1, Hag.2.1, Hag.2.2, Hp⟩
  obtain ⟨hA, hlat⟩ := HX
  obtain ⟨hs, htp, hdp⟩ := Hag
  subst hA hlat htp hdp
  imod HQ $$ %X %hpq Hdl H1 with ⟨H1, HQ⟩
  imod Hcl $$ %X [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14] Hs with Hv
  · iunfold durCoreB; iframe; ipureintro; exact Hp'
  imodintro
  iframe

/-- (hraft_robust R5b) **The restore's post in one form** (for both cases of the latest snapshot). -/
theorem restore_unify {E : CoPset} (r : Loc) (lat : SnapLatest) (dp : Option DiscPend) (li lt : w64) :
    latFacts γ rc i lat ∗
    (match lat with
      | none => (monoNatAuthOwn rc.dur.applied (1 : Qp).half 0 ∨ ⌜∃ d, dp = some d⌝) ∗
          dghostVar rc.names.llb (DFrac.own (1 : Qp).half) (some (li, lt, W64 0, W64 0)) ∗
          r.[Raft, go!"configurations"] ↦ configurations.mk (zero_val Configuration) (W64 0)
            (zero_val Configuration) (W64 0) ∗
          sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) null ∗
          rc.fsmOwn 0
      | some (m, _) =>
          (monoNatAuthOwn rc.dur.applied (1 : Qp).half (uint.nat m.Index') ∨ ⌜∃ d, dp = some d⌝) ∗
          applLb rc (uint.nat m.Index') ∗
          dghostVar rc.names.llb (DFrac.own (1 : Qp).half) (some (li, lt, m.Index', m.Term')) ∗
          r.[Raft, go!"configurations"] ↦ configurations.mk m.Configuration' m.ConfigurationIndex'
            m.Configuration' m.ConfigurationIndex' ∗
          (∃ (p : Loc) (c' : Configuration) (ss : List Server),
            sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p ∗
            p ↦□ c' ∗ c'.Servers' ↦* ss ∗ m.Configuration'.Servers' ↦*□ ss) ∗
          (∃ (k0 : Nat) (res : GoInterface), rc.fsmOwn k0 ∗ ⌜k0 ≤ uint.nat m.Index'⌝ ∗
            noCmdBetween γ k0 (uint.nat m.Index' + 1) ∗ (⌜k0 = 0⌝ ∨ rc.respP k0 res))) ⊢
    |={E}=> (monoNatAuthOwn rc.dur.applied (1 : Qp).half (latIdx lat) ∨ ⌜∃ d, dp = some d⌝) ∗
      (match lat with | none => iprop(True) | some (m, _) => applLb rc (uint.nat m.Index')) ∗
      dghostVar rc.names.llb (DFrac.own (1 : Qp).half) (some (li, lt, latIdxW lat, latTermW lat)) ∗
      (∃ (ccfg cfg : Configuration) (cidx li' : w64) (p : Loc),
        r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li' ∗ ⌜cfgBoot lat ccfg cidx cfg li'⌝ ∗
        sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p ∗
        (⌜p = null⌝ ∨ ∃ c' : Configuration, p ↦□ c' ∗ cfgOpt γ c')) ∗
      (∃ (k0 : Nat) (res : GoInterface), rc.fsmOwn k0 ∗ ⌜k0 ≤ latIdx lat⌝ ∗
        noCmdBetween γ k0 (latIdx lat + 1) ∗ (⌜k0 = 0⌝ ∨ rc.respP k0 res)) := by
  rcases lat with _ | ⟨m, b⟩
  · iintro ⟨-, Ha, Hllb, Hcfgs, Hp, Hf⟩
    simp only [latIdx, latIdxW, latTermW]
    imodintro
    iframe Ha Hllb
    isplitl [Hcfgs Hp]
    · iexists _, _, _, _, null
      iframe Hcfgs Hp
      isplitr; · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      ileft; ipureintro; rfl
    iexists 0, interface.nil
    iframe Hf
    isplitr; · ipureintro; exact Nat.le_refl _
    isplitr
    · unfold noCmdBetween; simp only [Nat.sub_self, List.range'_zero]
      iapply BigSepL.bigSepL_nil.2; itrivial
    ileft; ipureintro; rfl
  · iintro ⟨#Hlat, Ha, #Hlb, Hllb, Hcfgs, ⟨%p, %c', %ss, Hp, #Hpc, Hss, #Hmss⟩, Hf⟩
    unfold latFacts
    icases Hlat with ⟨-, -, -, ⟨%ss0, #Hcv, -⟩, -⟩
    unfold cfgVal
    icases Hcv with ⟨#Hss0, %Hok⟩
    ihave %Heq := ownSlice_agree _ _ _ _ _ $$ Hss0 Hmss
    subst Heq
    imod ownSlice_persist $$ Hss with #Hss
    simp only [latIdx, latIdxW, latTermW]
    imodintro
    iframe Ha Hllb Hf
    isplitr; · iexact Hlb
    iexists _, _, _, _, p
    iframe Hcfgs Hp
    isplitr; · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    iright; iexists c'; iframe Hpc
    unfold cfgOpt; iexists ss0; iframe Hss; ipureintro; right; exact Hok

/-- (hraft_robust R5b) **`NewRaft`'s state after fix 2 (`b = false`) and fix 4 (`b = true`)**: the protocol state
`s` (the crash state's, or after fix 2's discard), the stores' pinned state `A`, the main goroutine's views, the
`lastApplied` half at the latest snapshot's index, `lastLog` (`lp`'s value `lv`, the lock's fields): the protocol
log's last entry, or (only before fix 4) below the snapshot, whose index is then the log's length. -/
def fixPost (b : Bool) (lat : SnapLatest) (D : StableAbs) (g : w64) (t : Nat) (lp : Loc) : IProp GF :=
  iprop(∃ (s : SState) (A : LogAbs) (lv : Log) (c : Nat),
    bootV rc A lat ∗ srvVP rc s none none ∗
    ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
    ghostVar rc.dur.pw 1 (none : Option Pend) ∗ stVS rc D g ∗
    monoNatAuthOwn rc.dur.comp (1 : Qp).half c ∗ monoNatAuthOwn rc.dur.applied (1 : Qp).half (latIdx lat) ∗
    dghostVar rc.names.llb (DFrac.own (1 : Qp).half) (some (lv.Index', lv.Term', latIdxW lat, latTermW lat)) ∗
    ghostVar rc.names.lastLog (1 : Qp).half (uint.nat lv.Index', uint.nat lv.Term') ∗ lp ↦ lv ∗
    ⌜s.term = t ∧ s.cidx = 0 ∧ voteMatches D s ∧ uint.nat g ≤ s.dur.1 ∧ latIdx lat ≤ s.dur.1 ∧
      c ≤ latIdx lat ∧ (∀ k, latIdx lat < k → k ≤ s.log.length → A.m.lookup k = ent s.log k) ∧
      ((uint.nat lv.Index' = s.log.length ∧ uint.nat lv.Term' = lastTerm s.log ∧ latIdx lat ≤ uint.nat lv.Index') ∨
        (b = false ∧ uint.nat lv.Index' < latIdx lat ∧ s.log.length = latIdx lat ∧ lastTerm s.log = latTerm lat))⌝)

/-- (hraft_robust R5b) **gprot's facts at the boot** of the protocol state `s`: its bounds, its entries' kinds and
configurations, and against the latest snapshot `lat`: with a discard `dp` pending, the durable prefix below the
snapshot (else the log would match it there); with none, the snapshot's index durable and its entry the log's. -/
theorem boot_facts {E : CoPset} (hE : ↑gprotN ⊆ E) (s : SState) (lat : SnapLatest) (dp : Option DiscPend)
    (hcv : γ.cv = cfgDec γ.srvs) (hdl : ∀ d, dp = some d → latIdx lat = d.x ∧ latTerm lat = d.st) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ latFacts γ rc i lat ∗ latDurLb γ i lat dp ∗ dpRes γ i s dp ⊢ |={E}=>
      srvOwn γ i s ∗ ⌜bootF γ s lat dp⌝ := by
  iintro ⟨#HI, Hs, #Hlat, #Hdl, #Hdp⟩
  imod gprot.srvOwn_facts γ E hE i s $$ [$HI $Hs] with ⟨Hs, -, %Hf⟩
  obtain ⟨-, hdl1, -, -, -, -, hlen, hcfg, hkind⟩ := Hf
  have hents : ∀ k e, ent s.log k = some e →
      (e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kBarrier ∨ e.kind = kConfig) ∧
      (e.kind = kConfig → ∃ ss : List Server, e.data = encodeServers ss ∧ srvsOk γ ss) := by
    intro k e he
    refine ⟨hkind k e he, fun hk => ?_⟩
    have hv := hcfg k e he hk
    rw [hcv] at hv
    obtain ⟨ss, hd, hss⟩ := cfgDec_valid γ.srvs e.data hv.1
    exact ⟨ss, hd, hss⟩
  rcases lat with _ | ⟨m, b⟩
  · -- no snapshot: no discard pending
    rcases dp with _ | d
    · imodintro; iframe Hs; ipureintro
      exact ⟨by omega, hdl1, hents, (fun d h => by cases h), fun _ => ⟨Nat.zero_le _, fun h => absurd rfl h⟩⟩
    · have := (hdl d rfl).1; simp only [latIdx] at this
      unfold dpRes
      icases Hdp with ⟨-, -, %Hd⟩
      exfalso; omega
  · unfold latFacts
    icases Hlat with ⟨-, ⟨%e, #HCe, %He⟩, -, -, -⟩
    rcases dp with _ | d
    · unfold latDurLb
      icases Hdl with (%h | #Hd)
      · exact absurd rfl h
      imod srvOwn_ent_durLb γ i (E := E) hE s _ e $$ [$HI $Hs $Hd $HCe] with ⟨Hs, %Hx⟩
      imodintro; iframe Hs; ipureintro
      refine ⟨by omega, hdl1, hents, (fun d h => by cases h), fun _ => ⟨Hx.2.1, fun _ => ⟨e, Hx.1, He.1⟩⟩⟩
    · unfold dpRes
      icases Hdp with ⟨-, -, %Hd⟩
      obtain ⟨hx, ht⟩ := hdl d rfl
      simp only [latIdx, latTerm] at hx ht
      imod gprot.srvOwn_durLb γ E hE i s $$ [$HI $Hs] with ⟨Hs, #Hdur⟩
      by_cases hlt : s.dur.1 < d.x
      · imodintro; iframe Hs; ipureintro
        refine ⟨by omega, hdl1, hents, (fun d' h => by cases h; exact hlt), (fun h => by cases h)⟩
      · ihave #Hdx := gprot.durLb_mono γ i _ (uint.nat m.Index') (by omega) $$ Hdur
        imod srvOwn_ent_durLb γ i (E := E) hE s _ e $$ [$HI $Hs $Hdx $HCe] with ⟨Hs, %Hx⟩
        exfalso
        apply Hd.2.2
        rw [← hx, ← ht]
        right
        refine ⟨(proto.ent_le_length Hx.1).2, ?_⟩
        rw [proto.termAt_of_ent Hx.1, He.1]

/-! ### The configuration scan (a copy of `Raft__appendEntries`' `aeCfg`) -/

/-- The persistent facts of the `configurations` field over the log `L` scanned up to `n`
(`mainOwnAt`'s at `n = |L|`). -/
def nrCfgFacts (L : RLog) (n a T : Nat) (cfg ccfg : Configuration) (cidx li : w64) : IProp GF :=
  iprop(cfgAtIs γ L (uint.nat li) cfg ∗ cfgAtIs γ L (uint.nat cidx) ccfg ∗
    ⌜uint.nat li = lastCfgIdx (L.take n) ∧
      (cidx = li ∨ (uint.nat cidx = lastCfgIdx (L.take (uint.nat li - 1)) ∧ a < uint.nat li))⌝ ∗
    cmtIdx γ T L (uint.nat cidx))

instance nrCfgFacts_persistent L n a T cfg ccfg cidx li :
    Persistent (nrCfgFacts (GF := GF) γ L n a T cfg ccfg cidx li) := by
  unfold nrCfgFacts; infer_instance

/-- The scan of an entry that is no configuration entry. -/
theorem nrCfgFacts_step_other (L : RLog) (n a T : Nat) (cfg ccfg : Configuration)
    (cidx li : w64) (e : Entry) (he : ent L (n + 1) = some e) (hk : e.kind ≠ kConfig) :
    nrCfgFacts (GF := GF) γ L n a T cfg ccfg cidx li ⊢ nrCfgFacts γ L (n + 1) a T cfg ccfg cidx li := by
  unfold nrCfgFacts
  iintro ⟨#H1, #H2, %H, #H3⟩
  iframe H1 H2 H3
  ipureintro
  rw [lastCfgIdx_take_succ L n e he, if_neg hk]
  exact H

/-- The scan of a configuration entry at `n + 1` (`processConfigurationLogEntry`): the latest becomes
the committed configuration (committed by `cfgPrevCommitted`), the entry the latest. -/
theorem nrCfgFacts_step_cfg (L : RLog) (n a T : Nat) (cfg ccfg c : Configuration)
    (cidx li : w64) (e : Entry) (ss : List Server) (he : ent L (n + 1) = some e)
    (hk : e.kind = kConfig) (hd : e.data = encodeServers ss) (hss : srvsOk γ ss) (ha : a < n + 1)
    (hn : n + 1 < 2 ^ 64) :
    nrCfgFacts (GF := GF) γ L n a T cfg ccfg cidx li ∗ c.Servers' ↦*□ ss ∗
      cmtIdx γ T L (lastCfgIdx (L.take n)) ⊢
      nrCfgFacts γ L (n + 1) a T c cfg li (W64 (n + 1 : Nat)) := by
  unfold nrCfgFacts
  iintro ⟨⟨#H1, #H2, %H, #H3⟩, #Hc, #Hp⟩
  have hw : uint.nat (W64 (n + 1 : Nat)) = n + 1 := by word
  rw [hw]
  isplitr
  · unfold cfgAtIs
    iright
    iexists ss, e
    unfold cfgVal
    iframe Hc
    ipureintro; exact ⟨hss, by omega, he, hk, hd⟩
  iframe H1
  isplitr
  · ipureintro
    rw [lastCfgIdx_take_succ L n e he, if_pos hk]
    refine ⟨rfl, Or.inr ⟨?_, ha⟩⟩
    rw [Nat.add_sub_cancel]; exact H.1
  rw [H.1]; iexact Hp

/-- The commit index reaching the latest configuration (`setCommittedConfiguration(latest)`). -/
theorem nrCfgFacts_commit (L : RLog) (n a T : Nat) (cfg ccfg : Configuration) (cidx li : w64) :
    nrCfgFacts (GF := GF) γ L n a T cfg ccfg cidx li ∗ cmtIdx γ T L (uint.nat li) ⊢
      nrCfgFacts γ L n a T cfg cfg li li := by
  unfold nrCfgFacts
  iintro ⟨⟨#H1, #H2, %H, #H3⟩, #H4⟩
  iframe H1 H4
  ipureintro
  exact ⟨H.1, Or.inl rfl⟩

/-- (hraft_robust R5b) **The scan's start**: the restore's configurations are the log's at the latest snapshot's
index `x` (durable), committed. -/
theorem nrCfgFacts_boot {E : CoPset} (hE : ↑gprotN ⊆ E) (s : SState) (lat : SnapLatest) (a : Nat)
    (ccfg cfg : Configuration) (cidx li : w64) (hx : latIdx lat ≤ s.dur.1) (hb : cfgBoot lat ccfg cidx cfg li) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ latFacts γ rc i lat ⊢ |={E}=>
      srvOwn γ i s ∗ nrCfgFacts γ s.log (latIdx lat) a s.term cfg ccfg cidx li := by
  iintro ⟨#HI, Hs, #Hlat⟩
  rcases lat with _ | ⟨m, b⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hb
    imodintro
    iframe Hs
    unfold nrCfgFacts
    isplitr
    · unfold cfgAtIs; ileft; isplitr; · ipureintro; rfl
      iapply ownSlice_nil
    isplitr
    · unfold cfgAtIs; ileft; isplitr; · ipureintro; rfl
      iapply ownSlice_nil
    isplitr
    · ipureintro
      have : lastCfgIdx ([] : RLog) = 0 := by have := (lastCfgIdx_spec ([] : RLog)).1; simpa using this
      refine ⟨?_, Or.inl rfl⟩
      simp only [latIdx, List.take_zero, this]; rfl
    rw [show uint.nat (W64 0) = 0 from rfl]
    iapply cmtIdx_zero
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hb
    unfold latFacts
    icases Hlat with ⟨-, -, -, ⟨%ss, #Hcv, #Hsc⟩, -⟩
    unfold cfgVal
    icases Hcv with ⟨#Hss, %Hok⟩
    imod snapProof.install_cfgs γ E hE i s (uint.nat m.Index') (uint.nat m.ConfigurationIndex') ss
      m.Configuration' hx $$ [$HI $Hs $Hsc $Hss] with ⟨Hs, #Hca, #Hcm, %Hf⟩
    imodintro
    iframe Hs
    unfold nrCfgFacts
    iframe Hca Hcm
    ipureintro
    exact ⟨Hf.1.symm, Or.inl rfl⟩

end scan

end github_com.hashicorp.raft

end Perennial
