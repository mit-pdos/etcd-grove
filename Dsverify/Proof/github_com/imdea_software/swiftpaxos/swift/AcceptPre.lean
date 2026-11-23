/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/AcceptPre.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The leader's pre-acceptance suffices for a follower's acceptance** (the law
`fastAckFromLeader` needs; notes/prove-swift.md §13's blocker (a), with HUB-REQUEST M3).

`fastAckFromLeader`'s witness of the leader's ack (`sp.fastAckOk`) gives `sp.preacc γ L b x D`
(`L` the ballot's leader), not a `locLb` of `L` (the invariant keeps no copy of the sequences'
fragments, so none can be minted). The model's `PInv.pre_ok` says what the acceptance needs of
the leader's sequence: `x ∈ S.loc L b` and `D = depsIn (S.seqOf (S.loc L b)) x`, i.e. `x` is in
the ballot's order (`S.ord N b`) with the dependencies `D` there (`depsIn (S.ordSeq N b) x`).
So the acceptance is stated over the leader's `preacc` instead of a `locLb`:
* `sp.upd_accept_pre`: as `sp.upd_accept'` (Steps.lean) with `preacc γ (leaderOf N b) b y D` in
  place of the `locLb`, N2 over `D`;
* `swift.accept_dstep_pre`: as `swift.accept_dstep` (DescNode.lean), through `nodeInvD`.
These open `sp.inv`'s body (T2-1, as Steps.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescNode
import all Spec.swift.Inv

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

/-- **An acceptance by the leader's pre-acceptance** (`fastAckFromLeader`): replica `r` accepts
`y` of its own sequence of its ballot `b`, the leader of `b` having pre-accepted `y` with `D`,
every `d ∈ D` accepted or committed by `r` in `b` first (N2), unless `r` is the leader (SWB-9). -/
theorem upd_accept_pre (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (y : CmdId) (D : List CmdId) (hr : r < N)
    (hk : nodeOf l r = some k) (hnot : (st.ballot, y) ∉ st.accR)
    (hloc : y ∈ st.locAt st.ballot) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.accept st.ballot y, W')) ∗
      preacc γ (leaderOf N st.ballot) st.ballot y D ∗
      (⌜r = leaderOf N st.ballot⌝ ∨
        [∗list] d ∈ D, iprop(accepted γ r st.ballot d ∨ committed γ r st.ballot d)) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.accepted st.ballot y) ∗ predPost γ k (some (PEv.accept st.ballot y, W')) ∗ accepted γ r st.ballot y := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpp, #Hpre, #Hdeps⟩
  imod node_step E hE N fr l r k st (some (PEv.accept st.ballot y, W'))
    (fun s' => iprop(⌜s' = st.accepted st.ballot y⌝ ∗ accepted γ r st.ballot y)) hr hk $$ [Hst Hpp]
    with ⟨%st', Hst, Hpost, %Heq, #Hc⟩
  · iframe Hinv Hcfg Hst Hpp
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrows := HI.rows_ok r st.ballot
    rw [Hrs] at hrows
    iunfold preacc at Hpre
    ihave %HlkP := ghost_map_lookup $$ HP Hpre
    have hpre : S.pre (leaderOf N st.ballot) st.ballot y = some D := by
      rw [← Hrepr.pre]; exact HlkP
    obtain ⟨-, -, hyL, hD, -⟩ := HI.pre_ok _ _ _ _ hpre
    ihave %HN2 : ⌜r ≠ leaderOf N st.ballot → ∀ d ∈ D,
        (mA.lookup (r, st.ballot, d)).isSome ∨ (mCo.lookup (r, st.ballot, d)).isSome⌝ $$ [HA HCo]
    · icases Hdeps with (%HL | #Hd)
      · ipureintro; intro hne; exact absurd HL hne
      · ihave %H := accCom_lookups (γ := γ) r st.ballot D mA mCo $$ [HA HCo Hd]
        · iframe HA HCo Hd
        ipureintro; exact fun _ => H
    have hord : y ∈ S.ord N st.ballot := hyL
    have hdeps : depsIn (S.ordSeq N st.ballot) y = D := by
      unfold PState.ordSeq PState.ord; exact hD.symm
    have hfresh : mA.lookup (r, st.ballot, y) = none := by
      rcases e : mA.lookup (r, st.ballot, y) with _ | v
      · rfl
      · exact absurd ((hrows.2.1 y).1 ((Hrepr.acc r _ y).1 (by simp [e]))) hnot
    imod ghost_map_insert_persist _ () hfresh $$ HA with ⟨HA, #Hnew⟩
    imodintro
    iexists S.accept r st.ballot y, mL, mS, _, mP, mCo, mR, mPa
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_accept HI r _ y hr (by rw [Hrs]) (by rw [hrows.1]; exact hloc) hord
          (fun hne d hd => by
            rw [hdeps] at hd
            rcases HN2 hne d hd with h | h
            · exact Or.inl ((Hrepr.acc r _ d).1 h)
            · exact Or.inr ((Hrepr.com r _ d).1 h)),
        syncRows_mono Hsr rfl (fun r' p hp => by simp only [PState.accept]; exact hp),
        ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, fun r' b' y' => ?_, Hrepr.pre, Hrepr.path, Hrepr.com,
          Hrepr.rep⟩, rfl, rfl, PState.le_accept _ _ _, fun r' h => ?_, ⟨[], ⟨⟨hr, by rw [Hrs], by rw [hrows.1]; exact hloc, hord, fun hne d hd => by rw [hdeps] at hd; exact (HN2 hne d hd).imp ((Hrepr.acc r _ d).1) ((Hrepr.com r _ d).1)⟩, trivial⟩, rfl⟩⟩
      · rw [GMap.lookup_insert_eq_iff]
        by_cases e : (r, st.ballot, y) = (r', b', y')
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
          simp [PState.accept]
        · rw [if_neg e, Hrepr.acc]
          simp only [PState.accept]
          constructor
          · exact Or.inl
          · rintro (h | ⟨rfl, rfl, rfl⟩)
            · exact h
            · exact absurd rfl e
      · simp [PState.accept, h]
    isplitr
    · ipureintro; simp [PState.accept, Hrs, RState.accepted]
    · unfold accepted; iexact Hnew
  subst Heq
  imodintro
  iframe Hst Hpost
  iexact Hc

end ghost

end sp

section dstep
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- **An acceptance from `y`'s descriptor by the leader's pre-acceptance**
(`fastAckFromLeader`) in its epoch `b`: `upd_accept_pre` through `nodeInvD`. -/
theorem swift.accept_dstep_pre (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N r k : Nat)
    (fr : Bool) (l : List GoString) (q : Qp) (b : Nat) (y : sp.CmdId) (D : List sp.CmdId)
    (rv : swift.RowV) (hr : r < N) (hk : nodeOf l r = some k) (hrv : rv.2.2.1 = false)
    (W' : List w64) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv ∗
      sp.preacc γ (sp.leaderOf N b) b y D ∗
      (⌜r = sp.leaderOf N b⌝ ∨ [∗list] d ∈ D, iprop(sp.accepted γ r b d ∨ sp.committed γ r b d)) ∗
      sp.predPre γ k (some (sp.PEv.accept b y, W')) ⊢
    |={⊤}=> swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y (rv.1, rv.2.1, true, rv.2.2.2) ∗
      (sp.predPost γ k (some (sp.PEv.accept b y, W')) ∗ sp.accepted γ r b y) := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hep, Htok, #Hpre, #Hdeps, Hpp⟩
  iapply (swift.desc_upd γ γv γe γo k q b y rv (rv.1, rv.2.1, true, rv.2.2.2)
    (fun st => st.accepted b y) iprop(sp.predPost γ k (some (sp.PEv.accept b y, W')) ∗
      sp.accepted γ r b y)
    (fun _ => rfl) (fun _ => rfl)
    (fun st _ hc hacc b' x hx => by
      rcases List.mem_cons.mp hx with h | h
      · cases h; show b ≤ st.cballot; omega
      · exact hacc b' x h)
    (fun st hrv' b' y' => by rw [swift.rowsOf_accepted, ← hrv']))
  iframe Hninv Hep Htok
  iintro %st ⟨%hb, %hc, %hrv', %hyl⟩ Hst
  subst hb
  have hnot : (st.ballot, y) ∉ st.accR := by
    intro h
    have := congrArg (fun v : swift.RowV => v.2.2.1) hrv'
    simp only [swift.rowsOf] at this
    rw [hrv] at this
    exact absurd h (by simpa using this)
  iapply (sp.upd_accept_pre (⊤ \ ↑swift.nodeN) swift.nodeN_diff N fr l r k st y D hr hk hnot hyl W')
  iframe Hinv Hcfg Hst Hpre Hdeps Hpp


/-- **A repeated acceptance from `y`'s descriptor** (D91, `fastAckFromLeader` with the row already
accepted): `upd_reaccept` through `nodeInvD`; the token's value is unchanged (stated in
`accept_dstep_pre`'s form). -/
theorem swift.reaccept_dstep (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N r k : Nat)
    (fr : Bool) (l : List GoString) (q : Qp) (b : Nat) (y : sp.CmdId)
    (rv : swift.RowV) (hr : r < N) (hk : nodeOf l r = some k) (hrv : rv.2.2.1 = true)
    (W' : List w64) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv ∗
      sp.predPre γ k (some (sp.PEv.accept b y, W')) ⊢
    |={⊤}=> swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y (rv.1, rv.2.1, true, rv.2.2.2) ∗
      sp.predPost γ k (some (sp.PEv.accept b y, W')) := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hep, Htok, Hpp⟩
  iapply (swift.desc_upd γ γv γe γo k q b y rv (rv.1, rv.2.1, true, rv.2.2.2)
    (fun st => st.accepted b y) iprop(sp.predPost γ k (some (sp.PEv.accept b y, W')))
    (fun _ => rfl) (fun _ => rfl)
    (fun st _ hc hacc b' x hx => by
      rcases List.mem_cons.mp hx with h | h
      · cases h; show b ≤ st.cballot; omega
      · exact hacc b' x h)
    (fun st hrv' b' y' => by rw [swift.rowsOf_accepted, ← hrv']))
  iframe Hninv Hep Htok
  iintro %st ⟨%hb, %hc, %hrv', %hyl⟩ Hst
  subst hb
  have hacc : (st.ballot, y) ∈ st.accR := by
    have := congrArg (fun v : swift.RowV => v.2.2.1) hrv'
    simp only [swift.rowsOf] at this
    rw [hrv] at this
    simpa using this.symm
  iapply (sp.upd_reaccept (⊤ \ ↑swift.nodeN) swift.nodeN_diff N fr l r k st y hr hk hacc W')
  iframe Hinv Hcfg Hst Hpp

/-- **A repeated commit from `y`'s descriptor** (D91, the acks handler with the row already
committed): `upd_recommit` through `nodeInvD`; the token's value is unchanged (stated in
`commit_dstep'`'s form). -/
theorem swift.recommit_dstep (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N r k : Nat)
    (fr : Bool) (l : List GoString) (q : Qp) (b : Nat) (y : sp.CmdId)
    (rv : swift.RowV) (hr : r < N) (hk : nodeOf l r = some k) (hrv : rv.2.2.2 = true)
    (W' : List w64) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv ∗
      sp.predPre γ k (some (sp.PEv.commit b y, W')) ⊢
    |={⊤}=> swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y (rv.1, rv.2.1, rv.2.2.1, true) ∗
      sp.predPost γ k (some (sp.PEv.commit b y, W')) := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hep, Htok, Hpp⟩
  iapply (swift.desc_upd γ γv γe γo k q b y rv (rv.1, rv.2.1, rv.2.2.1, true)
    (fun st => st.committed b y) iprop(sp.predPost γ k (some (sp.PEv.commit b y, W')))
    (fun _ => rfl) (fun _ => rfl) (fun st _ _ hacc => hacc)
    (fun st hrv' b' y' => by rw [swift.rowsOf_committed, ← hrv']))
  iframe Hninv Hep Htok
  iintro %st ⟨%hb, %hc, %hrv', %hyl⟩ Hst
  subst hb
  have hcom : (st.ballot, y) ∈ st.comR := by
    have := congrArg (fun v : swift.RowV => v.2.2.2) hrv'
    simp only [swift.rowsOf] at this
    rw [hrv] at this
    simpa using this.symm
  iapply (sp.upd_recommit (⊤ \ ↑swift.nodeN) swift.nodeN_diff N fr l r k st y hr hk hcom W')
  iframe Hinv Hcfg Hst Hpp
end dstep

end Perennial.github_com.imdea_software.swiftpaxos
