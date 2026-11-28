/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/gprot/Snap.lean (241f27e).
-/
/-
`gprot` (stage 2) — snapshots of the protocol state and the read bounds, as laws of the ghost
layer.

The invariant keeps the list of snapshots taken so far (`SnapG`, a `mono_list` of `proto.Snap`,
each known to the current state: `proto.SnapOK`). A goroutine takes a snapshot of the current
state with `histLb_now` (anywhere; with `S = []` for a first snapshot), `srvOwn_now` (the main goroutine: its own term and
durable prefix in it) or `termCouple_now` (a reader of the `currentTerm` atomic: the term it read
in it), and gets `histLb γ s`, persistent. Snapshots are ordered (`histLb_order`).

The read bounds (`proto.read_bound`, `proto.read_bound_barrier`) lifted: `read_bound_upd` (the
leader's verify, with a quorum of follower snapshots of its term) and `barrier_bound` (a barrier
appended after the read's snapshot and committed).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Laws

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft
namespace gprot

open proto

section snaps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
variable (γ : GNames)

/-! ## Snapshots -/

/-- **Snapshots are ordered** (no invariant needed: each `histLb` carries the ordered list of the
snapshots before it, and two such lists are prefixes of one another). -/
theorem histLb_order (s1 s2 : Snap) :
    histLb (GF := GF) γ s1 ∗ histLb γ s2 ⊢ ⌜snapLe s1 s2 ∨ snapLe s2 s1⌝ := by
  unfold histLb
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %hp := mono_list_lb_valid γ.hist L1 L2 $$ H1 H2
  ipureintro
  rcases hp with hp | hp
  · exact Or.inl (snapLe_of_prefix hp h2.2.2.1 h1.1 h2.1)
  · exact Or.inr (snapLe_of_prefix hp h1.2.2.1 h2.1 h1.1)

/-- **A snapshot's keys are the servers**, which are distinct (no invariant needed: `histLb`
carries them): so its frontier is bounded by any common bound of the servers' prefixes, and two
snapshots have the same keys. -/
theorem histLb_keys (s : Snap) :
    histLb (GF := GF) γ s ⊢
      ⌜s.terms.map (·.1) = γ.srvs ∧ s.durs.map (·.1) = γ.srvs ∧ γ.srvs.Nodup⌝ := by
  unfold histLb
  iintro ⟨%L, _, %h⟩
  ipureintro
  have hs := List.mem_of_getLast? h.1
  exact ⟨(h.2.2.2.2 s hs).1, (h.2.2.2.2 s hs).2, h.2.2.2.1⟩

/-- **A snapshot's frontier** (`Snap.maxDur_le` with `histLb_keys`): at most any common bound of the
servers' durable prefixes at the snapshot (hr3: the call frontier is within a read's position). -/
theorem histLb_maxDur (s : Snap) (X : Nat) (h : ∀ i ∈ γ.srvs, s.dur i ≤ X) :
    histLb (GF := GF) γ s ⊢ ⌜s.maxDur ≤ X⌝ := by
  iintro H
  ihave %hk := histLb_keys γ s $$ H
  ipureintro
  exact Snap.maxDur_le hk.2.1 hk.2.2 X h

/-- **A snapshot of now** (anywhere the invariant's mask is available): later than every snapshot
of `S` (the snapshots the caller holds, e.g. the registrations of the verify futures a heartbeat
answers), and covering the durable prefixes `ds` of servers the caller knows of (each `durLb`). -/
theorem histLb_now (E : CoPset) (hE : ↑gprotN ⊆ E) (S : List Snap) (ds : List (SID × Nat))
    (hds : ∀ p ∈ ds, p.1 ∈ γ.srvs) :
    Inv (GF := GF) γ ∗ ([∗list] s0 ∈ S, histLb γ s0) ∗ ([∗list] p ∈ ds, durLb γ p.1 p.2) ⊢ |={E}=>
      ∃ s, histLb γ s ∗ ⌜(∀ s0 ∈ S, snapLe s0 s) ∧ ∀ p ∈ ds, p.2 ≤ s.dur p.1⌝ := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, HS, HD⟩
  ihave ⟨Hs, %hD⟩ := srvs_durLbs γ σ ds $$ [Hs HD]
  · isplitl [Hs]; iexact Hs; iexact HD
  imod H_snap_take γ σ hg S $$ [Hh HS] with ⟨Hh, %n, #Hlb, %hle⟩
  · isplitl [Hh]; iexact Hh; iexact HS
  imodintro
  isplitl [Hh Hs Hr]
  · iapply InvInner_intro γ σ
    unfold InvBody
    iframe; ipureintro; exact hg
  iexists (snapOf σ n)
  isplitr; · iexact Hlb
  ipureintro
  refine ⟨hle, fun p hp => ?_⟩
  have hv := hds p hp
  rw [snapOf_dur, if_pos (by rw [hg.2.1]; exact hv)]
  exact hD p hp hv

/-- **The main goroutine's snapshot**: a snapshot of now, later than `s0`, in which `i`'s term and
durable prefix are its own state's (the leader-log length: `srvOwn_now_leader`). -/
theorem srvOwn_now (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (s0 : Snap) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ histLb γ s0 ⊢ |={E}=>
      srvOwn γ i s ∗ ∃ s', histLb γ s' ∗
        ⌜snapLe s0 s' ∧ s'.term i = s.term ∧ s'.dur i = s.dur.1⌝ := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho, #H0⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  imod H_snap_take γ σ hg [s0] $$ [Hh] with ⟨Hh, %n, #Hlb, %hle⟩
  · isplitl [Hh]; · iexact Hh
    iapply BigSepL.bigSepL_cons.2
    isplitr; · iexact H0
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imodintro
  isplitl [Hh Hs Hr]
  · iapply InvInner_intro γ σ
    unfold InvBody
    iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  iexists (snapOf σ n)
  isplitr; · iexact Hlb
  ipureintro
  refine ⟨hle s0 (List.mem_singleton_self _), ?_, ?_⟩
  · rw [snapOf_term, if_pos hi']; rfl
  · rw [snapOf_dur, if_pos hi']

/-- `srvOwn_now` for the leader of its term (held at the snapshot): the leader log's length in the
snapshot is its log's. -/
theorem srvOwn_now_leader (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (s0 : Snap) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ leaderIs γ s.term i ∗ histLb γ s0 ⊢ |={E}=>
      srvOwn γ i s ∗ ∃ s', histLb γ s' ∗
        ⌜snapLe s0 s' ∧ s'.term i = s.term ∧ s'.dur i = s.dur.1 ∧ s'.llen s.term = s.log.length⌝ := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho, #Hl, #H0⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ s.term i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have hLL : σ.log i = σ.llog (σ.term i) := leader_log σ i hP hi' hl
  have hmx : (σ.srv i).term ≤ σ.maxT := term_le_maxT σ i hP hi'
  imod H_snap_take γ σ hg [s0] $$ [Hh] with ⟨Hh, %n, #Hlb, %hle⟩
  · isplitl [Hh]; · iexact Hh
    iapply BigSepL.bigSepL_cons.2
    isplitr; · iexact H0
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imodintro
  isplitl [Hh Hs Hr]
  · iapply InvInner_intro γ σ
    unfold InvBody
    iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  iexists (snapOf σ n)
  isplitr; · iexact Hlb
  ipureintro
  refine ⟨hle s0 (List.mem_singleton_self _), ?_, ?_, ?_⟩
  · rw [snapOf_term, if_pos hi']; rfl
  · rw [snapOf_dur, if_pos hi']
  · rw [snapOf_llen, if_pos hmx]
    show (σ.llog (σ.term i)).length = (σ.log i).length
    rw [hLL]

/-- **A term reader's snapshot** (inside the `currentTerm` atomic's invariant, at the load; `i` a
voter): a snapshot of now, later than `s0`, in which `i`'s term is the value read. -/
theorem termCouple_now (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (t : Nat) (s0 : Snap) :
    Inv (GF := GF) γ ∗ isSrv γ i ∗ termCouple γ i t ∗ histLb γ s0 ⊢ |={E}=>
      termCouple γ i t ∗ ∃ s', histLb γ s' ∗ ⌜snapLe s0 s' ∧ s'.term i = t⌝ := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody isSrv
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hv, Hc, #H0⟩
  ihave ⟨Hh, %hv⟩ := H_voter_lookup γ σ i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hv
  have hi : i ∈ γ.srvs := by rw [← hg.2.1]; exact hv
  ihave ⟨Hi, Hcl⟩ := srvs_peek γ σ i hi $$ Hs
  ihave ⟨Hi, Hc, %ht⟩ := srvG_term_agree γ i (σ.srv i) t $$ [Hi Hc]
  · iframe
  ihave Hs := Hcl $$ Hi
  imod H_snap_take γ σ hg [s0] $$ [Hh] with ⟨Hh, %n, #Hlb, %hle⟩
  · isplitl [Hh]; · iexact Hh
    iapply BigSepL.bigSepL_cons.2
    isplitr; · iexact H0
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imodintro
  isplitl [Hh Hs Hr]
  · iapply InvInner_intro γ σ
    unfold InvBody
    iframe; ipureintro; exact hg
  isplitl [Hc]; · iexact Hc
  iexists (snapOf σ n)
  isplitr; · iexact Hlb
  ipureintro
  refine ⟨hle s0 (List.mem_singleton_self _), ?_⟩
  rw [snapOf_term, if_pos hv, ht]; rfl

/-- **A snapshot's frontier is committed**: the committed log extends some `L` at least as long as
the snapshot's largest durable prefix (`proto.maxDur_le_C`). -/
theorem histLb_C (E : CoPset) (hE : ↑gprotN ⊆ E) (s : Snap) :
    Inv (GF := GF) γ ∗ histLb γ s ⊢ |={E}=> ∃ L : RLog, CLb γ L ∗ ⌜s.maxDur ≤ L.length⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hs0⟩
  ihave ⟨Hh, %hok⟩ := H_histLb_ok γ σ s $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hs0
  ihave ⟨Hh, #HC⟩ := H_C_lb γ σ $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iexists σ.C
  isplitr; · iexact HC
  ipureintro; exact maxDur_le_C σ s hg.1 hok

/-! ## The read bounds -/

/-- The verify quorum's snapshots give the quorum's terms at `sc` (internal). -/
theorem snap_quorum_terms (sc : Snap) (T : Nat) (Q : List SID) :
    ([∗list] q ∈ Q, ∃ sq, histLb (GF := GF) γ sq ∗ ⌜snapLe sc sq ∧ sq.term q ≤ T⌝) ⊢
      ⌜∀ q ∈ Q, sc.term q ≤ T⌝ := by
  induction Q with
  | nil => iintro -; ipureintro; intro q h; simp at h
  | cons a Q ih =>
    iintro Hl
    ihave ⟨⟨%sq, -, %h0⟩, Hfs⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    ihave %hs := ih $$ Hfs
    ipureintro
    intro q hq
    rcases List.mem_cons.mp hq with h | h
    · subst h; exact Nat.le_trans (h0.1.2.1 q) h0.2
    · exact hs q h

/-- **The read bound** (the leader's verify, `proto.read_bound`): the leader `j` of `T` (with its
publications' bound `k`, `pubOwn`), its log `L` at the verify's snapshot `sc` (`llogPre`, of the
length the snapshot counted, past its election part: the no-op precedes every verify), and a quorum
`Q` of the latest configuration of `L` (stage 4) each of whose members had, at a snapshot after `sc`,
a term `≤ T` (the heartbeat responses of the verify): every server's durable prefix at `sc` is at
most `len0 T` or at most `k`. -/
theorem read_bound_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (sc : Snap) (T n0 k : Nat) (j : SID)
    (L : RLog) (Q : List SID) (hL : L.length = sc.llen T) (hn0 : n0 < L.length)
    (hQ : isQuorumOf (cfgOfC γ.cv L) Q) :
    Inv (GF := GF) γ ∗ histLb γ sc ∗ leaderIs γ T j ∗ len0Is γ T n0 ∗ llogPre γ T L ∗
      pubOwn γ j T k ∗
      ([∗list] q ∈ Q, ∃ sq, histLb γ sq ∗ ⌜snapLe sc sq ∧ sq.term q ≤ T⌝) ⊢ |={E}=>
      pubOwn γ j T k ∗ ⌜∀ i ∈ γ.srvs, sc.dur i ≤ n0 ∨ sc.dur i ≤ k⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hsc, #Hl, #Hl0, #Hp, Hpo, HQ⟩
  ihave %hq := snap_quorum_terms γ sc T Q $$ HQ
  ihave ⟨Hh, %hp⟩ := H_llogPre_lookup γ σ T L $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hp
  ihave ⟨Hh, %hok⟩ := H_histLb_ok γ σ sc $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hsc
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ T j $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, %hl0⟩ := H_len0_lookup γ σ T n0 $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl0
  ihave ⟨Hh, Hpo, %hpo⟩ := H_pubOwn_bound γ σ j T k $$ [Hh Hpo]
  · isplitl [Hh]; iexact Hh; iexact Hpo
  have hP := hg.1
  have hQ' : isQuorumOf (cfgOf σ ((σ.llog T).take (sc.llen T))) Q := by
    show isQuorumOf (cfgOfC σ.cv ((σ.llog T).take (sc.llen T))) Q
    rw [hg.2.2.2.1, ← hL, ← hp]; exact hQ
  have hln : σ.leader T ≠ none := by rw [hl]; simp
  have hn0 : σ.len0 T = n0 := by
    unfold len0F at hl0; rw [if_pos (Or.inl hln)] at hl0; cases hl0; rfl
  have hrb := read_bound σ sc T Q hP hok hln (by omega) hQ' hq
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Hpo]; · iexact Hpo
  ipureintro
  intro i hi
  rw [← hg.2.1] at hi
  rcases hrb i hi with h | ⟨k', hk', hp⟩
  · left; rw [← hn0]; exact h
  · right; exact Nat.le_trans hk' (hpo k' hp hl)

/-- **The read bound of a barrier** (`proto.read_bound_barrier`): the committed entry `e` at `b`
(`CIdx`: the FSM goroutine has it for each entry of a batch), appended after the snapshot `sc`
(`llog e.term` was shorter than `b` there): every server's durable prefix at `sc` is below `b`. -/
theorem barrier_bound (E : CoPset) (hE : ↑gprotN ⊆ E) (sc : Snap) (b : Nat) (e : Entry)
    (hnew : sc.llen e.term < b) :
    Inv (GF := GF) γ ∗ histLb γ sc ∗ CIdx γ b e ⊢ |={E}=>
      ⌜∀ i ∈ γ.srvs, sc.dur i < b⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hsc, #Hc⟩
  ihave ⟨Hh, %hok⟩ := H_histLb_ok γ σ sc $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hsc
  ihave ⟨Hh, %hc⟩ := H_C_lookup γ σ b e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro
  intro i hi
  rw [← hg.2.1] at hi
  exact read_bound_barrier σ sc b e hg.1 hok hc hnew i hi

/-! ## Entries in their own term's leader log -/

/-- An entry of any leader log at `k` is the entry at `k` of its own term's leader log (log
matching, `ILogs`). What a server passes to its log store for each entry it stores
(`iface/Stores.lean`, `StoreLogs`): two entries stored with one index and term are equal
(`llogIdx_agree`; hr3's `checker.stored`). -/
theorem llogIdx_own (E : CoPset) (hE : ↑gprotN ⊆ E) (T k : Nat) (e : Entry) :
    Inv (GF := GF) γ ∗ llogIdx γ T k e ⊢ |={E}=> llogIdx γ e.term k e := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hl⟩
  ihave ⟨Hh, %he⟩ := H_llog_lookup γ σ T k e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  have he' := LMok_ent ((PInv.logs hg.1).2.1 T) he
  ihave ⟨Hh, #Hl'⟩ := H_llog_get γ σ e.term k e he' $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iexact Hl'

/-- The genesis entry is term 1's leader-log entry at index 1 (what `BootstrapCluster` passes to
the log store's `StoreLog`, stage 2). -/
theorem llogIdx_genesis (E : CoPset) (hE : ↑gprotN ⊆ E) :
    Inv (GF := GF) γ ⊢ |={E}=> llogIdx γ 1 1 γ.g := by
  apply Inv_read0 γ E hE
  intro σ
  unfold InvBody
  iintro ⟨%hg, Hh, Hs, Hr⟩
  have he : ent (σ.llog 1) 1 = some γ.g := by
    rw [(PInv.gen hg.1).2.2.2.2.1, ← hg.2.2.1]; rfl
  ihave ⟨Hh, #Hl⟩ := H_llog_get γ σ 1 1 γ.g he $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iexact Hl

end snaps

end gprot
end github_com.hashicorp.raft

end Perennial
