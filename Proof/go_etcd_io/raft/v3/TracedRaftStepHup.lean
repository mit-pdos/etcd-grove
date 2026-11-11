/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on `MsgHup` at a follower or
candidate** (2026-11-10, trace-check Q8 stage 1 slice 19a, `notes/decisions.md`, "Q8 stage 1 (slice
19a)"): the campaign's lines.

- **The `BecomeCandidate` line**: its phase step (`phaseStepB_becomeCandidate`: the idle server of `s`
  to that of `becomeCandidate id s`, the share's server `candC`, `candOf`'s) and its facts
  (`fxPres_timeout`: the specification's `Timeout`, `specInv_timeout` with the leader completeness of
  the facts; the node's `srvFacts` at the new term by `commitIn_agree`; the bags unchanged).
- **The vote request's and the self-vote's lines**: their phase steps (`phaseStepB_send_pin` with
  `lineEffect_requestVote`, `lineEffect_selfVote`) and their facts (`fxPres_plain`: a message with no
  entries that is not an append request, `MsgOk` from the node's term).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepLocal
public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The share's server after a `Timeout` (`candOf`'s, read through `toC`). -/
def candC (i : Etcdraft.ID) (cs : ServerC) : ServerC :=
  { cs with state := Etcdraft.candidate, currentTerm := cs.currentTerm + 1, votedFor := i, lead := Etcdraft.nil,
            votesResponded := [], votesGranted := [] }

theorem toC_candOf (srv : Etcdraft.SetIds) (i : Etcdraft.ID) (a : Etcdraft.Server) :
    toC srv (candOf i a) = candC i (toC srv a) := rfl

/-- **A node and its server after `becomeCandidate`**: `candOf`'s. -/
theorem simServerR_becomeCandidate (C : List w64) (bl : Nat) (id : w64) (s : NState) (a : Etcdraft.Server)
    (hR : SimServerR C bl (toPState s) a) (hnw : uint.Z s.term + 1 < 2 ^ 64) :
    SimServerR C bl (toPState (becomeCandidate id s)) (candOf (idAbs id) a) := by
  obtain ⟨h1, -, -, -, h5, h6, h7, h8, h9, -, -⟩ := hR
  have ht : uint.Z (s.term + W64 1) = uint.Z s.term + 1 := by word
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show a.currentTerm + 1 = uint.Z (s.term + W64 1); rw [ht, h1]; rfl
  · rfl
  · rfl
  · rfl
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · intro _
    refine ⟨?_, ?_⟩ <;>
      simp [candOf, toPState, becomeCandidate, resetTo, resetTo0, Etcdraft.SetIds.mk]
    exact tallyGranted_empty
  · intro h; cases h

theorem logShapeOk_becomeCandidate (bl : Nat) (id : w64) (s : NState) (h : LogShapeOk bl (toPState s)) :
    LogShapeOk bl (toPState (becomeCandidate id s)) := h

/-- **The idle relation's server part after `becomeCandidate`**, its share's server `candC`. -/
theorem simIdleS_becomeCandidate (C : List w64) (id : w64) (s : NState) (cs : ServerC)
    (h : SimIdleS C s cs) (hT : uint.Z s.term + 1 < 2 ^ 63) :
    SimIdleS C (becomeCandidate id s) (candC (idAbs id) cs) := by
  obtain ⟨a, rfl, hR, hs, bt, bc, bl⟩ := h
  have ht : uint.Z (s.term + W64 1) = uint.Z s.term + 1 := by word
  exact ⟨candOf (idAbs id) a, rfl, simServerR_becomeCandidate C C.length id s a hR (by omega),
    logShapeOk_becomeCandidate _ id s hs, by show uint.Z (s.term + W64 1) < _; omega, bc, bl⟩

/-- The idle relation's server part reads a non-leader's `Progress` values not at all. -/
theorem simIdleS_prvals_nl (C : List w64) (s : NState) (pvs : GMap w64 Progress) (h : s.role ≠ .leader) :
    SimIdleS C { s with prvals := pvs } = SimIdleS C s := by
  unfold SimIdleS
  rw [toPState_prvals_nl s pvs h]

end pure

section phases
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The `BecomeCandidate` line's phase step, pinned**: from the idle server of `s` to that of
`becomeCandidate id s`, the share's server `candC`, its list kept (`lineEffect_becomeCandidate`). -/
theorem phaseStepB_becomeCandidate (id : w64) (c : CfgM) (s : NState) (o : List Msg)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg)
    (hnl : s.role ≠ .leader) (hT : uint.Z s.term + 1 < 2 ^ 63) :
    PhaseStepB id c (NodeEvOf (W64 1) id (becomeCandidate id s) c) (PinAt s C0 cs0 P0 o)
      (PinAtG (fun C => SimIdleS C (becomeCandidate id s)) C0 (candC (idAbs id) cs0) P0 o) := by
  rintro C cs P ⟨rfl, rfl, rfl, ⟨a0, ha0, hR0, hs, bt, bc, bl⟩, hP⟩ ⟨hin, hout, hC⟩ e he
  have hname' : gsStr e.name = "BecomeCandidate" := by
    have hname := he.1
    simp only [evtNames] at hname
    have : e.name = go!"BecomeCandidate" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  refine ⟨he.2.1, by rw [hname']; decide, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha0.trans ha.symm) hR0
  have ht : uint.Z (s.term + W64 1) = uint.Z s.term + 1 := by word
  have hrl : a.state = Etcdraft.follower ∨ a.state = Etcdraft.candidate := by
    rw [hR.2.1]
    have := proleRole_not_leader s.role hnl
    simp only [toPState]
    cases h : proleRole s.role
    · exact .inl rfl
    · exact .inr rfl
    · exact absurd h this
  refine ⟨candOf (idAbs id) a, [], ⟨rfl, ?_, by simp, ⟨?_, by simpa using hP⟩⟩, by simp, ?_⟩
  · rw [toC_candOf, ha, ← ha0]
  · exact ⟨candOf (idAbs id) a, rfl, simServerR_becomeCandidate C C.length id s a hR (by omega),
      logShapeOk_becomeCandidate _ id s hs, by show uint.Z (s.term + W64 1) < _; omega, bc, bl⟩
  · exact lineEffect_becomeCandidate C e id (becomeCandidate id s) c a _ he hout hC hrl
      (by rw [hR.2.2.2.2.2.2.2.1]) rfl (by rw [hR.1]; show uint.Z s.term + 1 = uint.Z (s.term + W64 1); omega)
      (by show uint.Z (s.term + W64 1) < _; omega)

/-- The vote request's and the self-vote's numbers (`Msg.TrOk`). -/
theorem campMsg_trOk (id T y : w64) (e : entryID) (cl : List w8) (ht : uint.nat T < traceNumBound)
    (hi : uint.nat e.index' < traceNumBound) (hl : uint.nat e.term' < traceNumBound) :
    (campMsg false id T e cl y).TrOk := by
  intro _
  have h0 : uint.nat (W64 0) = 0 := rfl
  have hb : (0 : Nat) < traceNumBound := by unfold traceNumBound; omega
  unfold campMsg
  split
  · refine ⟨ht, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Msg.plain, List.length_nil, h0] <;> exact hb
  · refine ⟨ht, ?_, hl, hi, ?_, ?_⟩ <;> simp only [campReq, List.length_nil, h0] <;> exact hb

/-- **A vote request's or the self-vote's phase step, pinned** (`phaseStepB_send_pin` with
`lineEffect_requestVote`, `lineEffect_selfVote`), at the campaign's state `s1` (a candidate with no votes
yet): the request's last entry the log's (`hidx`, `hlt`), the destination a voter. -/
theorem phaseStepB_campMsg (id : w64) (c : CfgM) (s1 : NState) (o : List Msg) (y : w64) (cl : List w8)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (ma0 : Etcdraft.Msg)
    (hma : TraceSim.msgAbs C0 C0.length
      (campMsg false id s1.term (plogLast (toPState s1).base (toPState s1).log) cl y) = some ma0)
    (hrole : s1.role = .candidate) (hvotes : s1.votes = ∅) (hy : y ∈ elements c.incoming)
    (hlt : uint.Z (plogLast (toPState s1).base (toPState s1).log).term' < 2 ^ 63) :
    PhaseStepB id c
      (SendEvOf (if y = id then W64 15 else W64 13) id s1 c
        (campMsg false id s1.term (plogLast (toPState s1).base (toPState s1).log) cl y))
      (PinAt s1 C0 cs0 P0 o)
      (PinAt s1 C0 cs0 (P0 ++ [ma0]) (o ++ [campMsg false id s1.term (plogLast (toPState s1).base (toPState s1).log) cl y])) := by
  have hw : ∀ w, (toPState s1).votes !! w = none := by
    intro w; simp [toPState, hrole, hvotes]
  have hrl : (toPState s1).role = .candidate ∨ s1.role = .candidate := .inr hrole
  by_cases hyi : y = id
  · subst hyi
    have hm : campMsg false y s1.term (plogLast (toPState s1).base (toPState s1).log) cl y =
        Msg.plain .voteResp y y s1.term false := by simp [campMsg, vrespTy]
    rw [if_pos rfl]
    rw [hm] at hma ⊢
    apply phaseStepB_send_pin y c s1 _ o _ C0 cs0 P0 ma0 hma rfl
      (fun e he => ⟨he.2.1, sendEvOf_notBoot he (by decide) (by decide) (by decide)⟩)
    intro C e a he hin hout hC hR hs bt bc bl
    refine ⟨_, rfl, ?_⟩
    exact lineEffect_selfVote C e y s1 c _ a _ he hin hout hC hR hs hrole rfl rfl rfl (hw y) rfl rfl bt bc bl
  · rw [if_neg hyi]
    have hm : campMsg false id s1.term (plogLast (toPState s1).base (toPState s1).log) cl y =
        campReq false id y s1.term (plogLast (toPState s1).base (toPState s1).log) cl := by
      simp [campMsg, hyi]
    rw [hm] at hma ⊢
    apply phaseStepB_send_pin id c s1 _ o _ C0 cs0 P0 ma0 hma rfl
      (fun e he => ⟨he.2.1, sendEvOf_notBoot he (by decide) (by decide) (by decide)⟩)
    intro C e a he hin hout hC hR hs bt bc bl
    refine ⟨_, rfl, ?_⟩
    have hwf := hs.2.1
    have hidx : uint.Z (plogLast (toPState s1).base (toPState s1).log).index' =
        plogLastIndexZ (toPState s1).base (toPState s1).log := plogLast_index _ _ hwf
    exact lineEffect_requestVote C e id s1 c _ a _ he hin hout hC (hin.mem_iff.1 hy) hR hs hrole rfl rfl hyi
      (hw y) rfl rfl rfl bt bc bl
      (by show uint.Z (plogLast (toPState s1).base (toPState s1).log).index' < _
          rw [hidx]; unfold plastIndex at bl
          have := plogLastIndexZ_nonneg (toPState s1).base (toPState s1).log
          have h64 := hidx ▸ (uint_Z_lt _ : uint.Z (plogLast (toPState s1).base (toPState s1).log).index' < 2 ^ 64)
          have : uint.Z (W64 (plogLastIndexZ (toPState s1).base (toPState s1).log)) =
            plogLastIndexZ (toPState s1).base (toPState s1).log := by word
          omega)
      hlt

end phases

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A non-leader's facts after a `Timeout`**: the same log and commit (no pending entries), the
commit certificate at the new term (`commitIn_agree`). -/
theorem srvFacts_candOf (γ : RaftNames) (C : List w64) (j : w64) (i : Etcdraft.ID) (v : Etcdraft.Server)
    (hnl : v.state ≠ Etcdraft.leader) (hbt : v.currentTerm + 1 < 2 ^ 63) :
    srvFacts (GF := GF) γ C j v ⊢ srvFacts γ C j (candOf i v) := by
  unfold srvFacts
  iintro ⟨%es, %pend, %Hp, #Hr, #Hc, -, #Hci⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := Hp
  have hpend : pend = [] := h9 hnl
  subst hpend
  iexists es, []
  have hcl : (candOf i v).state = Etcdraft.candidate := rfl
  rw [hcl, if_neg (by decide), show (candOf i v).commitIndex = v.commitIndex from rfl,
    show (candOf i v).currentTerm = v.currentTerm + 1 from rfl, show (candOf i v).log = v.log from rfl]
  isplitr
  · ipureintro
    exact ⟨h1, h2, h3, h4, h5, h6, by omega, by omega, fun _ => rfl, fun e he => by simp at he⟩
  isplitr
  · iexact Hr
  isplitr
  · iexact Hc
  isplitr
  · ipureintro; trivial
  · iapply commitIn_agree γ es es (W64 v.commitIndex) (W64 v.currentTerm) (W64 (v.currentTerm + 1)) (by word)
      rfl rfl
    iexact Hci

/-- **The facts of a `BecomeCandidate` line** (the specification's `Timeout`, pre-vote off): at phases
that make the share's server `candC` of a follower's or candidate's and keep its list, the facts after
the line follow from those before: `specInv_timeout` (its leader completeness from the facts,
`allFacts_leaderCompleteness`, `allFacts_commitOk`), the node's `srvFacts` by `srvFacts_candOf`, the bags
unchanged (`AppSlices` by `appSlices_mono`: no new leader). -/
theorem fxPres_timeout (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (hC : ∀ C cs P, Φ C cs P → id ∈ C)
    (hst : ∀ C cs P, Φ C cs P → cs.state = Etcdraft.follower ∨ cs.state = Etcdraft.candidate)
    (hcfg : ∀ C cs P, Φ C cs P → cs.config.incoming = confAbs C)
    (hbt : ∀ C cs P, Φ C cs P → cs.currentTerm + 1 < 2 ^ 63)
    (hΦ' : ∀ C cs P cs' P', Φ C cs P → Φ' C cs' (P ++ P') → cs' = candC (idAbs id) cs ∧ P' = []) :
    ⊢ FxPres (GF := GF) γ id E Φ Φ' := by
  iunfold FxPres
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨hΦ, -, hcs, hΦ1, -, hsrv, hσa, hpv, -, -⟩ := hpre
  obtain ⟨hcs', hP'⟩ := hΦ' C cs P _ P' hΦ hΦ1
  subst hP'
  have hidC := hC C cs P hΦ
  have hrl := hst C cs P hΦ
  have hcf := hcfg C cs P hΦ
  have hb := hbt C cs P hΦ
  rw [← hcs] at hrl hcf hb
  simp only [toC] at hrl hcf hb
  have hi : idAbs id ∈ σ.server := by rw [hsrv]; exact (mem_confAbs C id).2 hidC
  have hnl : a.state ≠ Etcdraft.leader := by
    rcases hrl with h | h <;> rw [h] <;> decide
  have hto : σ.timeout (idAbs id) = some (σ.upd (idAbs id) (candOf (idAbs id))) := by
    unfold Etcdraft.State.timeout Etcdraft.State.timeoutEnabled Etcdraft.Server.timeoutRoleOk
      Etcdraft.State.getConfig
    have hcont : (confAbs C).contains (idAbs id) = true := by
      rw [List.contains_iff_mem, mem_confAbs]; exact hidC
    rw [hσa]
    rcases hrl with h | h <;> simp only [h, hcf, hcont, hpv, beq_self_eq_true, Bool.true_or, Bool.or_true,
      Bool.true_and, Bool.not_false, ↓reduceIte] <;> rfl
  ihave #Hfx0 := Hfx
  iunfold simFx at Hfx0
  icases Hfx0 with ⟨#Hal, #Hmf, %Hp⟩
  obtain ⟨hsi, hq, hu, hsh, has⟩ := Hp
  icases allFacts_commitOk γ C σ hsrv $$ Hal with %hco
  icases persistent_entails_right (allFacts_leaderCompleteness (GF := GF) γ C σ hsrv hsi.commitWithinLeader)
    $$ [$Htbl $Hal] with ⟨%hlc0, Htbl, -⟩
  have hlc : TraceSpecInv.LeaderComplete σ (idAbs id) ((σ.s (idAbs id)).currentTerm + 1) := by
    refine ⟨(hco _ hi).2, ?_⟩
    intro l hl hll hlt idx0 hidx hgt
    exact hlc0 _ hi idx0 hidx l (List.mem_filter.2 ⟨hl, by simp [hll]⟩) hgt (by omega)
  have hsi' := TraceSpecInv.specInv_timeout hsi hi hlc hto
  -- the facts at `σ.upd`, then at the line's result (the same up to `toC`)
  ihave #H1 : simFx (GF := GF) γ C (σ.upd (idAbs id) (candOf (idAbs id))) $$ []
  · iunfold simFx
    isplitl
    · iunfold allFacts
      iunfold allFacts at Hal
      imodintro
      iintro %j %hj
      by_cases hji : idAbs j = idAbs id
      · have := idAbs_inj.1 hji
        subst this
        rw [TraceSpecInv.upd_s_self]
        iapply srvFacts_candOf γ C j (idAbs j) _ (by rw [hσa]; exact hnl) (by rw [hσa]; exact hb)
        iapply Hal $$ %j %hj
      · rw [TraceSpecInv.upd_s_ne _ _ _ _ hji]
        iapply Hal $$ %j %hj
    isplitl
    · imodintro
      iintro %x %hx
      iapply Hmf
      ipureintro; exact hx
    ipureintro
    refine ⟨hsi', ?_, hu, hsh, ?_⟩
    · refine quorumLogF_congr σ (σ.upd (idAbs id) (candOf (idAbs id))) rfl ?_ ?_ ?_ hq
      · intro k; by_cases hk : k = idAbs id
        · subst hk; rw [TraceSpecInv.upd_s_self]; rfl
        · rw [TraceSpecInv.upd_s_ne _ _ _ _ hk]
      · intro k; by_cases hk : k = idAbs id
        · subst hk; rw [TraceSpecInv.upd_s_self]; rfl
        · rw [TraceSpecInv.upd_s_ne _ _ _ _ hk]
      · intro k; by_cases hk : k = idAbs id
        · subst hk; rw [TraceSpecInv.upd_s_self]; rfl
        · rw [TraceSpecInv.upd_s_ne _ _ _ _ hk]
    · refine appSlices_mono σ (σ.upd (idAbs id) (candOf (idAbs id))) has rfl (fun m hm => hm) ?_
      intro j _ hl
      by_cases hk : j = idAbs id
      · subst hk; rw [TraceSpecInv.upd_s_self] at hl
        exact absurd hl (show Etcdraft.candidate ≠ Etcdraft.leader by decide)
      · rw [TraceSpecInv.upd_s_ne _ _ _ _ hk] at hl ⊢
        exact .inl ⟨hl, rfl, List.prefix_refl _⟩
  have hs : ∀ j, toC (σ.upd (idAbs id) (candOf (idAbs id))).server
      ((withNode σ (idAbs id) a' _root_.id (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b)).s j) =
      toC (σ.upd (idAbs id) (candOf (idAbs id))).server ((σ.upd (idAbs id) (candOf (idAbs id))).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) = toC σ.server (if j = idAbs id then candOf (idAbs id) (σ.s (idAbs id)) else σ.s j)
    split
    · rw [hσa, hsrv, toC_candOf, hcs, hcs']
    · rfl
  ihave #H3 := simFx_congr γ C (σ.upd (idAbs id) (candOf (idAbs id)))
    (withNode σ (idAbs id) a' _root_.id (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b))
    rfl rfl rfl hs $$ H1
  iframe Htbl
  iexact H3

/-- **The facts of a send line of a message with no entries that is not an append request** (a vote
request, a vote response): at phases that keep the share's server and add the message `p` (canonical,
from the node), `MsgOk` from the node's server (`hok`), the facts after the line follow from those
before (`simFx_send`, `msgFacts_plain`; the message is pinned by its logged fields, `ContentLogged`). -/
theorem fxPres_plain (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (p : Etcdraft.Msg)
    (hp0 : canonMsg p = p) (hpt : p.type ≠ .appendEntriesRequest) (hpe : p.entries = [])
    (hok : ∀ C cs P, Φ C cs P → ∀ σ : Etcdraft.State, toC (confAbs C) (σ.s (idAbs id)) = cs →
      σ.server = confAbs C → TraceSpecInv.MsgOk σ p)
    (hΦ' : ∀ C cs P cs' P', Φ C cs P → Φ' C cs' (P ++ P') → cs' = cs ∧ P' = [p]) :
    ⊢ FxPres (GF := GF) γ id E Φ Φ' := by
  iunfold FxPres
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨hΦ, -, hcs, hΦ1, -, hsrv, hσa, -, -, -⟩ := hpre
  obtain ⟨hcs', hP'⟩ := hΦ' C cs P _ P' hΦ hΦ1
  subst hP'
  ihave #Hpf := msgFacts_plain (GF := GF) γ C p hpt hpe
  ihave #H2 := simFx_send γ C σ p (hok C cs P hΦ σ (by rw [hσa]; exact hcs) hsrv)
    hp0 (fun y _ => ContentLogged.pinned (fun h => absurd h hpt) y) (appSliceOf_nil σ p hpe) $$ [$Hfx $Hpf]
  have hs : ∀ j, toC (σ.send p).server
      ((withNode σ (idAbs id) a' _root_.id (fun b => [p].foldl Etcdraft.Bag.with b)).s j) =
      toC (σ.send p).server ((σ.send p).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) = toC σ.server (σ.s j)
    split
    · rename_i hj; subst hj; rw [hσa, hsrv, hcs', hcs]
    · rfl
  ihave #H3 := simFx_congr γ C (σ.send p)
    (withNode σ (idAbs id) a' _root_.id (fun b => [p].foldl Etcdraft.Bag.with b))
    rfl rfl rfl hs $$ H2
  iframe Htbl
  iexact H3

end facts

section pure2
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A non-leader's server is a follower or a candidate (a pre-candidate reads as a follower). -/
theorem roleAbs_nl (r : PRole) (h : r ≠ .leader) :
    roleAbs (proleRole r) = Etcdraft.follower ∨ roleAbs (proleRole r) = Etcdraft.candidate := by
  have := proleRole_not_leader r h
  cases hr : proleRole r
  · exact .inl rfl
  · exact .inr rfl
  · exact absurd hr this

/-- What the specification's counterpart of a campaign message is: no entries, not an append request
or response, from the node to `y`, of the campaign's term; a vote response is the node's granted vote
to itself. -/
theorem campMsg_abs (C : List w64) (bl : Nat) (id T y : w64) (e : entryID) (cl : List w8) (ma : Etcdraft.Msg)
    (h : TraceSim.msgAbs C bl (campMsg false id T e cl y) = some ma) :
    ma.type ≠ .appendEntriesRequest ∧ ma.type ≠ .appendEntriesResponse ∧ ma.entries = [] ∧
    ma.source = idAbs id ∧ ma.dest = idAbs y ∧ ma.term = uint.Z T ∧
    (ma.type = .requestVoteResponse → ma.voteGranted = true ∧ y = id) := by
  unfold campMsg at h
  split at h
  · rename_i hy
    subst hy
    simp only [TraceSim.msgAbs, Msg.plain, vrespTy] at h
    cases h
    refine ⟨by simp, by simp, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  · simp only [TraceSim.msgAbs, campReq, vreqTy] at h
    cases h
    refine ⟨by simp, by simp, rfl, rfl, rfl, rfl, fun h => by simp at h⟩

/-- `MsgHup` is none of the other types the gates name (decided on the constants). -/
theorem msgHup_ne :
    MsgHup ≠ MsgApp ∧ MsgHup ≠ MsgHeartbeat ∧ MsgHup ≠ MsgProp ∧ MsgHup ≠ MsgReadIndex ∧
    MsgHup ≠ MsgTransferLeader ∧ MsgHup ≠ MsgTimeoutNow ∧ MsgHup ≠ MsgVoteResp ∧
    MsgHup ≠ MsgPreVoteResp ∧ MsgHup ≠ MsgVote ∧ MsgHup ≠ MsgPreVote ∧ MsgHup ≠ MsgBeat := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [MsgHup, MsgApp, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgHup, MsgHeartbeat, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgHup, MsgProp, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgHup, MsgReadIndex, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgHup, MsgTransferLeader, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgHup, MsgTimeoutNow, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgHup, MsgVoteResp, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgHup, MsgPreVoteResp, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgHup, MsgVote, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgHup, MsgPreVote, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgHup, MsgBeat, ne_eq]; exact of_decide_eq_true rfl

/-- **`MsgHup` at a follower or candidate** (the campaign). -/
def LocalHup (s : NState) (m : MessageM) : Prop := m.Type' = MsgHup ∧ s.role ≠ .leader

/-- A campaign's end state's outbox is longer than the outbox it started from. -/
theorem campaignState_outbox_ne (id : w64) (s : NState) (pre : Bool) (peers : List w64) (cl : List w8)
    (pvs : GMap w64 Progress) :
    ({ campaignState id s pre peers cl with prvals := pvs } : NState).outbox ≠ s.outbox := by
  intro h
  have := congrArg List.length h
  cases pre <;> simp [campaignState, sendMsgs, becomeCandidate, becomePrecandidate, resetTo, resetTo0] at this

end pure2

section gates
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The log's terms at most the node's term (raft's ghost `TermsLe`, `ownRaftGhost_terms_le`). -/
theorem ownStepGhost_termsLe (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      ⌜∀ j x, plogTermAt (toPState s).base (toPState s).log j = some x → uint.Z x ≤ uint.Z s.term⌝ ∗
        ownStepGhost γ md c id s := by
  apply persistent_entails_right
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, -⟩
  icases ownRaftGhost_terms_le γ id (toPState s) $$ Hg with ⟨%h, -⟩
  ipureintro; exact h

/-- **The `BecomeCandidate` line's gate on a local path's family** (`hupGates`' `"Hgbc"`): the share
pinned, the line fired (`trCapB_hookGate`: `phaseStepB_becomeCandidate`, `fxPres_timeout`), the family
at the candidate's idle server. -/
theorem lineF_becomeCandidate (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64)
    (s : NState) (Λ : Option TraceEv → Prop) (htr : s.gh.tr = some γd) (hnl : s.role ≠ .leader)
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    lineF (GF := GF) γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) s.outbox ⊢
      HookGate s.gh.tr r (NodeEvOf (W64 1) id (becomeCandidate id s) c)
        (lineF γ md c r id s (fun C => SimIdleS C (becomeCandidate id s)) (stepLastEv Λ) s.outbox) := by
  unfold lineF trFam
  rw [htr]
  iintro ⟨Hgh, ⟨%bt, Hf⟩, %Hok⟩
  iapply hookGate_fupd
  imod ownStepGhost_traceBound (GF := GF) γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
  icases trCapB_pinMem γd γ r id c bt _ _ $$ Hf with ⟨%C0, %cs0, %P0, %HΦ0, Hf⟩
  icases trCapB_logger γd γ r id c bt _ _ $$ Hf with ⟨%tl, #Htl, Hf⟩
  have hT63 : uint.Z s.term + 1 < 2 ^ 63 := by unfold traceNumBound at hT; omega
  have hTn : uint.nat (s.term + W64 1) < traceNumBound := by unfold traceNumBound at hT ⊢; word
  ihave #Hfx := fxPres_timeout (GF := GF) γ id (NodeEvOf (W64 1) id (becomeCandidate id s) c)
    (PinAt s C0 cs0 P0 s.outbox)
    (PinAtG (fun C => SimIdleS C (becomeCandidate id s)) C0 (candC (idAbs id) cs0) P0 s.outbox)
    (fun C cs P h => by obtain ⟨rfl, -, -, -⟩ := h; exact HΦ0.2)
    (fun C cs P h => by
      obtain ⟨-, -, -, ⟨a, rfl, hR, -⟩, -⟩ := h
      show a.state = _ ∨ a.state = _
      rw [hR.2.1]; exact roleAbs_nl s.role hnl)
    (fun C cs P h => by
      obtain ⟨-, -, -, ⟨a, rfl, hR, -⟩, -⟩ := h
      show a.config.incoming = _
      rw [hR.2.2.2.2.2.2.2.1])
    (fun C cs P h => by
      obtain ⟨-, -, -, ⟨a, rfl, hR, -⟩, -⟩ := h
      show a.currentTerm + 1 < _
      rw [hR.1]; exact hT63)
    (fun C cs P cs' P' h h' => by
      obtain ⟨-, rfl, rfl, -⟩ := h
      obtain ⟨-, h1, h2, -⟩ := h'
      exact ⟨h1, by simpa using h2⟩)
  ihave Hfx := fxPres_upd γ id _ _ _ $$ Hfx
  imodintro
  iapply hookGate_mono (some γd) r _
    iprop(trCapB (some γd) γ r id c true
      (PinAtG (fun C => SimIdleS C (becomeCandidate id s)) C0 (candC (idAbs id) cs0) P0 s.outbox) (stepLastEv Λ) ∗ emp)
  isplitl [Hgh]
  · iintro ⟨Hc, -⟩
    iframe Hgh
    isplitl [Hc]
    · iexists true
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (fun _ _ _ h => h.2.2.2) $$ Hc
    ipureintro; exact Hok
  iapply trCapB_hookGate (some γd) γ r id c tl _ bt (PinAt s C0 cs0 P0 s.outbox) _ (stepLastEv Λ) (stepLastEv Λ)
    iprop(emp) (phaseStepB_becomeCandidate id c s s.outbox C0 cs0 P0 hnl hT63)
    (fun _ e he => by rw [nodeEvOf_name_candidate he]; rfl) (fun e _ => .inr rfl)
    (fun _ e he => nodeEvOf_ok (W64 1) id _ c e _ he (by decide) hTn Hb.1 Hb.2 (Nat.le_refl _))
    (fun h => by cases h)
  simp only [FxPresUT]
  iframe Htl Hf Hfx

/-- **A campaign message's gate on the candidate's family** (`hupGates`' `"#Hgsend"`): the share
pinned, the vote request's or the self-vote's line fired (`trCapB_hookGateOpt`: `phaseStepB_campMsg`,
`fxPres_plain`), the family at the outbox with the message. -/
theorem lineF_campSend (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64)
    (s : NState) (Λ : Option TraceEv → Prop) (pvs : GMap w64 Progress) (y : w64) (cl : List w8) (o : List Msg)
    (htr : s.gh.tr = some γd) (hy : y ∈ c.voters) (hlrn : c.learners = ∅)
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    lineF (GF := GF) γ md c r id s (fun C => SimIdleS C (becomeCandidate id s)) (stepLastEv Λ) o ⊢
      HookGateOpt s.gh.tr r
        (sendOutGate id { becomeCandidate id s with prvals := pvs } c
          (if y = id then vrespW32 false else vreqW32 false)
          [campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl y])
        (lineF γ md c r id s (fun C => SimIdleS C (becomeCandidate id s)) (stepLastEv Λ)
          (o ++ [campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl y])) := by
  have hgate : sendOutGate id { becomeCandidate id s with prvals := pvs } c
      (if y = id then vrespW32 false else vreqW32 false)
      [campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl y] =
      some (SendEvOf (if y = id then W64 15 else W64 13) id { becomeCandidate id s with prvals := pvs } c
        (campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl y)) := by
    split <;> exact sendOutGate_one id _ c _ _ _ rfl
  have hevt : uint.nat (if y = id then W64 15 else W64 13) ≠ 0 ∧ uint.nat (if y = id then W64 15 else W64 13) ≠ 2 ∧
      uint.nat (if y = id then W64 15 else W64 13) ≠ 6 ∧ uint.nat (if y = id then W64 15 else W64 13) ≠ 7 := by
    split <;> decide
  unfold lineF trFam
  rw [htr, hgate]
  iintro ⟨Hgh, ⟨%bt, Hf⟩, %Hok⟩
  iapply hookGateOpt_fupd
  imod ownStepGhost_traceBound (GF := GF) γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
  icases ownStepGhost_termsLe γ md c id s $$ Hgh with ⟨%Hterms, Hgh⟩
  icases trCapB_out γd γ r id c bt _ _ $$ Hf with ⟨%Hout, Hf⟩
  icases trCapB_pinMem γd γ r id c bt _ _ $$ Hf with ⟨%C0, %cs0, %P0, %HΦ0, Hf⟩
  icases trCapB_logger γd γ r id c bt _ _ $$ Hf with ⟨%tl, #Htl, Hf⟩
  obtain ⟨⟨a0, -, -, hs0, -⟩, -⟩ := HΦ0.1
  have hwf : PlogWf (toPState s).base (toPState s).log := hs0.2.1
  have hlt : uint.Z (plogLast (toPState s).base (toPState s).log).term' ≤ uint.Z s.term :=
    Hterms _ _ (plogTermAt_last _ _ hwf)
  have hidx : uint.Z (plogLast (toPState s).base (toPState s).log).index' =
      plogLastIndexZ (toPState s).base (toPState s).log := plogLast_index _ _ hwf
  have hbnd : traceNumBound = 2 ^ 61 := rfl
  have hTn : uint.nat (s.term + W64 1) < traceNumBound := by rw [hbnd] at hT ⊢; word
  have hin : uint.nat (plogLast (toPState s).base (toPState s).log).index' < traceNumBound := by
    have h2 := Hb.2
    unfold plastIndex at h2
    have : uint.Z (W64 (plogLastIndexZ (toPState s).base (toPState s).log)) =
        plogLastIndexZ (toPState s).base (toPState s).log := by
      have := uint_Z_lt (plogLast (toPState s).base (toPState s).log).index'
      have := plogLastIndexZ_nonneg (toPState s).base (toPState s).log
      word
    rw [hbnd] at h2 ⊢
    word
  have hln : uint.nat (plogLast (toPState s).base (toPState s).log).term' < traceNumBound := by
    rw [hbnd] at hT ⊢; word
  have hlt63 : uint.Z (plogLast (toPState s).base (toPState s).log).term' < 2 ^ 63 := by
    rw [hbnd] at hT; omega
  obtain ⟨ma0, hma⟩ : ∃ ma0, TraceSim.msgAbs C0 C0.length
      (campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl y) = some ma0 := by
    unfold campMsg; split <;> exact ⟨_, rfl⟩
  obtain ⟨hq, hqr, he, hsrc, hdst, hterm, hvr⟩ := campMsg_abs C0 C0.length id _ y _ cl ma0 hma
  have hyin : y ∈ elements c.incoming :=
    mem_incoming_of c y hlrn Hout ((GMap.elem_of_union _ _ _).2 (.inl hy))
  have hnlb : (becomeCandidate id s).role ≠ .leader := by simp [becomeCandidate]
  have hS1 : (fun C => SimIdleS C ({ becomeCandidate id s with prvals := pvs } : NState)) =
      (fun C => SimIdleS C (becomeCandidate id s)) :=
    funext fun C => simIdleS_prvals_nl C _ pvs hnlb
  have hps : PhaseStepB id c
      (SendEvOf (if y = id then W64 15 else W64 13) id { becomeCandidate id s with prvals := pvs } c
        (campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl y))
      (PinAtG (fun C => SimIdleS C (becomeCandidate id s)) C0 cs0 P0 o)
      (PinAtG (fun C => SimIdleS C (becomeCandidate id s)) C0 cs0 (P0 ++ [ma0])
        (o ++ [campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl y])) := by
    rw [← hS1]
    exact phaseStepB_campMsg id c { becomeCandidate id s with prvals := pvs } o y cl C0 cs0 P0 ma0 hma rfl rfl hyin hlt63
  have hcur : ∀ C cs P, PinAtG (fun C => SimIdleS C (becomeCandidate id s)) C0 cs0 P0 o C cs P →
      cs.currentTerm = uint.Z (s.term + W64 1) := by
    rintro C cs P ⟨-, -, -, ⟨a, rfl, hR, -⟩, -⟩
    exact hR.1
  ihave #Hfx := fxPres_plain (GF := GF) γ id
    (SendEvOf (if y = id then W64 15 else W64 13) id { becomeCandidate id s with prvals := pvs } c
      (campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl y))
    (PinAtG (fun C => SimIdleS C (becomeCandidate id s)) C0 cs0 P0 o)
    (PinAtG (fun C => SimIdleS C (becomeCandidate id s)) C0 cs0 (P0 ++ [ma0])
      (o ++ [campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl y]))
    ma0 (msgAbs_canon C0 C0.length _ ma0 hma) hq he
    (fun C cs P hΦ σ hσ hsrv => by
      have ht : (σ.s (idAbs id)).currentTerm = ma0.term := by
        rw [hterm, ← hcur C cs P hΦ, ← hσ]; rfl
      by_cases hvt : ma0.type = .requestVoteResponse
      · obtain ⟨hg, hyi⟩ := hvr hvt
        have hds : ma0.dest = idAbs id := by rw [hdst, hyi]
        exact TraceSpecInv.msgOk_vote σ ma0 he hvt (by rw [hsrc, ht]; exact Int.le_refl _)
          (fun _ => by rw [hds, ht]; exact Int.le_refl _)
          (fun l _ _ _ hd _ _ => by rw [hsrc, ← hds, hd])
      · exact TraceSpecInv.msgOk_plain σ ma0 he hq (fun h => absurd h hqr) (fun h => absurd h hvt)
          (by rw [hsrc, ht]; exact Int.le_refl _))
    (by
      rintro C cs P cs' P' ⟨-, rfl, rfl, -⟩ ⟨-, rfl, h, -⟩
      exact ⟨rfl, List.append_cancel_left h⟩)
  ihave Hfx := fxPres_upd γ id _ _ _ $$ Hfx
  have hmok := campMsg_trOk id (s.term + W64 1) y (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl
    hTn hin hln
  have hty : (campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl y).ty.traced = true := by
    unfold campMsg; split <;> rfl
  imodintro
  iapply hookGateOpt_mono (some γd) r _
    iprop(trCapB (some γd) γ r id c true (PinAtG (fun C => SimIdleS C (becomeCandidate id s)) C0 cs0 (P0 ++ [ma0])
      (o ++ [campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) cl y]))
      (stepLastEv Λ) ∗ emp)
  isplitl [Hgh]
  · iintro ⟨Hc, -⟩
    iframe Hgh
    isplitl [Hc]
    · iexists true
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (fun _ _ _ h => h.2.2.2) $$ Hc
    ipureintro
    exact outOk_snoc Hok hmok
  iapply trCapB_hookGateOpt (some γd) γ r id c tl _ bt _ _ (stepLastEv Λ) (stepLastEv Λ) iprop(emp) hps
    (fun e he => sendEvOf_notBoot he hevt.1 hevt.2.1 hevt.2.2.2)
    (fun e _ => .inr rfl)
    (fun _ e he => sendEvOf_ok _ id _ c _ e _ he ⟨hevt.1, hevt.2.2.1⟩ hTn Hb.1 Hb.2 (hmok hty) (Nat.le_refl _))
    (fun h => by cases h)
  simp only [FxPresUT]
  iframe Htl Hf Hfx

/-- **The closing wand's capability from a local path's family at another state's idle server** (`s1`,
whose server part the end state `s'` has): `lineF_close` at the phase of `s1`. -/
theorem lineF_closeAt (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s s1 s' : NState)
    (Λ : Option TraceEv → Prop) (hS : ∀ C, SimIdleS C s1 = SimIdleS C s') :
    lineF (GF := GF) γ md c r id s (fun C => SimIdleS C s1) Λ s'.outbox ⊢
      |={⊤}=> ownStepGhost γ md c id s ∗ (∃ b : Bool, trCapB s.gh.tr γ r id c b (fun C => SimIdle C s') Λ) ∗
        ⌜OutTrStep s s'⌝ := by
  unfold lineF
  iintro ⟨Hgh, ⟨%b, H⟩, %Hok⟩
  imod trFam_idle s.gh.tr γ r id c b s1 s' Λ hS $$ H with H
  imodintro
  iframe Hgh
  isplitl [H]
  · iexists b; iexact H
  ipureintro; exact outTrStep_of_outOk Hok

/-- `LocalHup`'s resources: before the campaign's first line, the family at the idle server of `s`
with the outbox `s`'s (`G0`, `G1`: what tells nothing done from a campaign at the close); after it,
the family at the candidate's idle server with the campaign's conditions (`GE`: what tells a campaign
from nothing done, `HupGuard` being exclusive); `False` where no path here goes. -/
def hupR (bt : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Λ : Option TraceEv → Prop) : StepG GF where
  G := trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ
  G0 := fun o => iprop(⌜o = s.outbox⌝ ∗ lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) o)
  G1 := fun o => iprop(⌜o = s.outbox⌝ ∗ lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) o)
  GE := fun o => iprop(⌜HupCampaigns c id s⌝ ∗
    lineF γ md c r id s (fun C => SimIdleS C (becomeCandidate id s)) (stepLastEv Λ) o)
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := fun _ => iprop(⌜False⌝)
  Gc := fun _ _ _ => iprop(⌜False⌝)

/-- **`raft.Step`'s traced bundle on `MsgHup` at a follower or candidate** (the campaign, pre-vote
off): the `BecomeCandidate` line (`lineF_becomeCandidate`), then each vote message's line
(`lineF_campSend`); the close tells nothing done (`G1`, the outbox `s`'s) from the campaign (`GE`, the
campaign's conditions) by `hup`'s exclusive result (`HupGuard`). -/
theorem stepBundle_hup_R (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (γd : GName)
    (Λ : Option TraceEv → Prop) (bt : Bool) (hp : LocalHup s m) (htr : s.gh.tr = some γd) (hpv : s.prevote = false)
    (hty : StepEndTy m.Type') (hT0 : m.Term' = W64 0) (hT : uint.Z s.term + 1 < traceNumBound)
    (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) (hlrn : c.learners = ∅) :
    (trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ ∗ TrNoSnap s.gh.tr s.logst : IProp GF) ⊢
      |={⊤}=> (hupR bt γ md c r id s Λ).G ∗
        stepGates c r id s m ents sn ctx rs (ghostIn γ md c id s (hupR bt γ md c r id s Λ)) ∗
        stepClose γ md c id m ents ctx s (hupR bt γ md c r id s Λ)
          (fun s' => iprop(∃ bt' : Bool, trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ))) := by
  have hnbf : ¬ PreBF m s := by
    unfold PreBF; rw [hT0]; intro h; have := h.1; simp at this
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => h.1 hT0
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hne := msgHup_ne
  have nX : ∀ x : w32, MsgHup ≠ x → m.Type' ≠ x := fun x hx h => hx (hp.1.symm.trans h)
  have hde : decide (campaignElection = campaignPreElection) = false := by
    simp (config := {decide := true}) [campaignElection, campaignPreElection]
  have hcne : campaignElection ≠ campaignPreElection := by simpa using hde
  have hht : hupType s = campaignElection := by simp [hupType, hpv]
  iintro ⟨Hcap, #Hnosnap⟩
  imodintro
  isplitl [Hcap]
  · dsimp only [hupR]; iexact Hcap
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, hupR]
    isplitr
    · -- the receive hook: no line for `MsgHup`
      iintro ⟨Hgh, Hc⟩
      have hrg : recvGate id s c ⟨m, ents, sn, ctx, rs⟩ = none := by
        apply recvGate_none_of
        intro ty hty'
        have hm1 : mtypeOf MsgHup = none := rfl
        simp only [hp.1, hm1] at hty'; cases hty'
      rw [hrg]
      iapply hookGateOpt_mono s.gh.tr r none (lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) s.outbox)
      isplitr [Hgh Hc]
      · iintro H; isplitr; · ipureintro; rfl
        iexact H
      iapply lineF_recv γd γ md c r id s Λ bt htr
      iframe Hgh Hc
    isplitr
    · unfold preGate
      iintro %_ HG0
      rw [if_neg hnbf]
      imodintro
      iexact HG0
    isplitr
    · iintro %h; exact (h.1 hT0).elim
    isplitr
    · iintro %h
      exact (h.elim (nX _ hne.2.2.2.2.2.2.2.2.1) (nX _ hne.2.2.2.2.2.2.2.2.2.1)).elim
    isplitr
    · -- the campaign
      iintro %_
      unfold hupGates
      rw [hht, if_neg hcne, hde, show campRoleState id s false = becomeCandidate id s from rfl]
      isplitr
      · iintro %hc ⟨-, HG⟩
        iapply hookGate_mono s.gh.tr r _
          (lineF γ md c r id s (fun C => SimIdleS C (becomeCandidate id s)) (stepLastEv Λ) s.outbox)
        isplitr [HG]
        · iintro H; isplitr; · ipureintro; exact hc
          iexact H
        iapply lineF_becomeCandidate γd γ md c r id s Λ htr hp.2 hT hfit
        iexact HG
      · imodintro
        iintro %pvs %y %o %hy ⟨%hc, HG⟩
        iapply hookGateOpt_mono s.gh.tr r _
          (lineF γ md c r id s (fun C => SimIdleS C (becomeCandidate id s)) (stepLastEv Λ)
            (o ++ [campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))
              (transferCtx campaignElection) y]))
        isplitr [HG]
        · iintro H; isplitr; · ipureintro; exact hc
          iexact H
        iapply lineF_campSend γd γ md c r id s Λ pvs y (transferCtx campaignElection) o htr hy hlrn hT hfit
        iexact HG
    isplitr
    · -- the step functions' gates, at `s` (no preamble): none reached for `MsgHup`
      unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      dsimp only
      isplit
      · iintro %hr
        unfold followerGates
        isplitr
        · iintro %h; exact (nX _ hne.1 h).elim
        isplitr
        · iintro %h; exact (nX _ hne.2.1 h).elim
        isplitr
        · iintro %h
          exact (h.elim (nX _ hne.2.2.1) (fun h => h.elim (nX _ hne.2.2.2.1) (nX _ hne.2.2.2.2.1))).elim
        isplitr
        · iintro %h; exact (nX _ hne.2.2.2.2.2.1 h).elim
        · imodintro; iintro %h; exact (nX _ hne.2.2.2.2.2.1 h).elim
      isplit
      · iintro %hr
        unfold candidateGates
        isplitr
        · iintro %h; exact (h.elim (nX _ hne.1) (nX _ hne.2.1)).elim
        isplitr
        · iintro %h; exact (nX _ hne.1 h).elim
        isplitr
        · iintro %h; exact (nX _ hne.2.1 h).elim
        isplitr
        · iintro %h; exact (nX _ hne.2.2.2.2.2.2.1 h.1).elim
        isplitr
        · iintro %h; exact h.elim
        isplitr
        · iintro %h; exact h.elim
        isplitr
        · imodintro; iintro %h; exact (nX _ hne.2.2.2.2.2.2.1 h.1).elim
        isplitr
        · iexact Hnosnap
        isplitr
        · iintro %h; exact (nX _ hne.2.2.2.2.2.2.2.1 h.1).elim
        isplitr
        · imodintro; iintro %h; exact (nX _ hne.2.2.2.2.2.2.2.1 h.1).elim
        · iintro %h
          exact (h.1.elim (fun h => nX _ hne.2.2.2.2.2.2.1 h.1)
            (fun h => nX _ hne.2.2.2.2.2.2.2.1 h.1)).elim
      · iintro %hr; exact (hp.2 hr).elim
    · ipureintro
      refine ⟨?_, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
      intro o o' h
      simp only
      rw [lineF_permInv γ md c r id s _ _ o o' h]
  · -- the closing wand: nothing done (`G0`, `G1`) or the campaign (`GE`), by `HupGuard`
    iunfold stepClose
    iintro %s' %B %recv %_ %hend Hout
    have hok' : HupOkC c id s s' := (hend (by rw [htr]; rfl) hty).2.1 hns hp.1
    obtain ⟨-, -, ⟨-, -, -, hpv', -⟩, -, hg⟩ := hok'
    unfold stepOut
    dsimp only [hupR]
    icases Hout with (⟨%ho, H⟩ | ⟨%ho, H⟩ | ⟨%hc, H⟩ | %hf | ⟨%b, %N, %hf⟩)
    · rcases hg with ⟨-, hss⟩ | ⟨-, pre, peers, pvs, cl, -, -, rfl⟩
      · subst s'
        iapply lineF_close γ md c r id s s (stepLastEv Λ) (fun _ => rfl) $$ H
      · exact absurd ho (campaignState_outbox_ne id s pre peers cl pvs)
    · rcases hg with ⟨-, hss⟩ | ⟨-, pre, peers, pvs, cl, -, -, rfl⟩
      · subst s'
        iapply lineF_close γ md c r id s s (stepLastEv Λ) (fun _ => rfl) $$ H
      · exact absurd ho (campaignState_outbox_ne id s pre peers cl pvs)
    · rcases hg with ⟨hnc, -⟩ | ⟨-, pre, peers, pvs, cl, hpp, -, rfl⟩
      · exact absurd hc hnc
      cases pre with
      | true =>
        have := hpp rfl; rw [hpv] at this; cases this
      | false =>
      have hS : ∀ C, SimIdleS C (becomeCandidate id s) =
          SimIdleS C ({ campaignState id s false peers cl with prvals := pvs } : NState) := by
        intro C
        rw [simIdleS_prvals_nl C _ pvs (by simp [campaignState, sendMsgs, becomeCandidate])]
        rfl
      iapply lineF_closeAt γ md c r id s (becomeCandidate id s) _ (stepLastEv Λ) hS $$ H
    · exact hf.elim
    · exact hf.elim

/-- **`raft.Step`'s traced bundle on `MsgHup` at a follower or candidate** (`stepBundle_hup_R`, the
resources `hupR`). -/
theorem stepBundle_traced_hup : stepBundle_traced.on (GF := GF) (hG := hG) LocalHup := by
  intro γ md c r id s m ents sn ctx rs γd Λ bt hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hsub _ _ _
  iintro ⟨Hcap, -, #Hnosnap⟩
  imod stepBundle_hup_R γ md c r id s m ents sn ctx rs γd Λ bt hp htr hpv hty (hloc (.inl hp.1)) hT hfit hlrn
    $$ [$Hcap $Hnosnap] with ⟨HG, Hgates, Hclose⟩
  imodintro
  iexists hupR bt γ md c r id s Λ
  iframe HG Hgates Hclose

/-- **`raft.tickElection` at a traced follower or candidate** (pre-vote and check-quorum off): the
capability idle at `s` in, idle at the end state out (`stepBundle_traced_hup` for the campaign's `Step`;
with no campaign the capability as it was). What a traced node API supplies: the capability and
`TrNoSnap`, the term's and the receipts' bounds, no learners. (2026-11-11, slice 22a, Q19) The
capability with any `booted` flag in, some flag out (a tick may come before the node's first `Ready`
line; `BecomeCandidate` is not bootstrap-named). -/
abbrev raft.tickElection.tracedTriple : Prop :=
  ∀ (c : CfgM) (md : GMode) (γ : RaftNames) (r : Loc) (id : w64) (s : NState) (γd : GName)
    (Λ : Option TraceEv → Prop) (bt : Bool),
  NStateWf s → md.Guard s → uint.Z s.logst.fl ≤ uint.Z s.logst.applied →
  s.gh.tr = some γd → s.prevote = false → s.cq = false → s.role ≠ .leader →
  uint.Z s.term + 1 < traceNumBound → receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  c.learners = ∅ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s ∗
      "Hcap" ∷ trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ ∗
      "#Hnosnap" ∷ TrNoSnap s.gh.tr s.logst }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"tickElection")) (Val #()))
  {{ (s' : NState), RET #();
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md c id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      "%Hcm" ∷ ⌜uint.Z s.logst.committed ≤ uint.Z s'.logst.committed ∧
        PVoteLe (toPState s) (toPState s')⌝ ∗
      "%Htick" ∷ ⌜TickStep s s'⌝ ∗
      "Hcap" ∷ ∃ bt' : Bool, trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ) }}

/-- `raft.tickElection.spec`'s traced instance (see `raft.tickElection.tracedTriple`). -/
theorem raft.tickElection.traced (h : raft.tickElection.spec (GF := GF) (hG := hG)) :
    raft.tickElection.tracedTriple (GF := GF) (hG := hG) := by
  intro c md γ r id s γd Λ bt Hwf Hpc Hfla htr hpv hcq hnl hT hfit hlrn
  iintro %Φ ⟨#Hinit, Hphys, Hghost, Hcap, #Hnosnap⟩ HΦ
  have hb : (tickMsg MsgHup id).Type' = MsgHup := rfl
  have hmt : mtypeOf (tickMsg MsgHup id).Type' = none := rfl
  imod stepBundle_hup_R (GF := GF) (hG := hG) γ md c r id s (tickMsg MsgHup id) [] none [] [] γd Λ bt
    ⟨hb, hnl⟩ htr hpv (by unfold StepEndTy; simp [hb]) rfl hT hfit hlrn
    $$ [$Hcap $Hnosnap] with ⟨HG, Hgates, Hclose⟩
  iapply h c md γ r id s (hupR bt γ md c r id s Λ)
    (fun s' => iprop(∃ bt' : Bool, trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ)))
    (by unfold traceNumBound at hT; omega) (fun h => by rw [hpv] at h; cases h) Hwf Hfla Hpc
    $$ [Hphys Hghost HG Hgates Hclose]
  · iframe Hinit Hphys Hghost HG Hgates Hclose
  inext
  iintro %s' H
  iapply HΦ $$ %s'
  iNamed H
  iframe Hphys Hghost
  isplitr
  · ipureintro; exact Hwf'
  isplitr
  · ipureintro; exact Hcm
  isplitr
  · ipureintro; exact Htick
  icases HG with (⟨%Hs, Hc⟩ | Hc)
  · subst s'
    dsimp only [hupR]
    iexists bt
    iapply trCapB_monoΛ s.gh.tr γ r id c bt _ Λ (stepLastEv Λ) (fun o h => .inl h) $$ Hc
  · iexact Hc

end gates

end EtcdGrove
end Perennial
