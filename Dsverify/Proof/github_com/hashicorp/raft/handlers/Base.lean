/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/handlers/Base.lean (241f27e).
-/
/-
Shared lemmas of the RPC-handler proofs (agent MAIN-H): access to the package globals.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/- Shared by the handler proofs (appendEntries, requestVote, requestPreVote). -/
/-- A case of a `wp_join` with an early-return disjunct: the fall-through side. -/
macro "q_exec" : tactic => `(tactic| (ileft; isplitr; · ipureintro; first | rfl | trivial))
/-- A case of a `wp_join` with an early-return disjunct: the return side. -/
macro "q_ret" : tactic => `(tactic| (iright; isplitr; · ipureintro; first | rfl | trivial))

/-- Close a `wp_join` case whose postcondition is `(⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝) ∗ R`. -/
macro "q_any" : tactic => `(tactic| (iframe; first
  | (ileft; ipureintro; first | rfl | trivial) | (iright; ipureintro; first | rfl | trivial)))

namespace github_com.hashicorp.raft

open gprot in
theorem gprotN_logN : (↑gprotN : CoPset) ⊆ ⊤ \ ↑logN := by
  unfold gprotN logN raftN; solve_ndisj
open gprot in
theorem gprotN_termN : (↑gprotN : CoPset) ⊆ ⊤ \ ↑termN := by
  unfold gprotN termN raftN; solve_ndisj
open gprot in
theorem gprotN_cidxN : (↑gprotN : CoPset) ⊆ ⊤ \ ↑cidxN := by
  unfold gprotN cidxN raftN; solve_ndisj

namespace proto
theorem ent_some_bound (L : RLog) (k : Nat) (e : Entry) (h : ent L k = some e) :
    1 ≤ k ∧ k ≤ L.length := by
  unfold ent at h
  split at h
  · cases h
  · have := (List.getElem?_eq_some_iff.mp h).1; omega
theorem matched_step (L : RLog) (prev : Nat) (ents : RLog) (j : Nat)
    (h : matchedUpTo L prev ents j) (hj : j < ents.length) (hb : prev + 1 + j ≤ L.length)
    (ht : termAt L (prev + 1 + j) = termAt ents (j + 1)) : matchedUpTo L prev ents (j + 1) := by
  refine ⟨by omega, fun j' hj' => ?_⟩
  by_cases hjj : j' < j
  · exact h.2 j' hjj
  · have : j' = j := by omega
    subst this; exact ⟨hb, ht⟩

theorem matched_zero (L : RLog) (prev : Nat) (ents : RLog) : matchedUpTo L prev ents 0 :=
  ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem matched_trunc (L : RLog) (prev pt : Nat) (ents : RLog) (j : Nat)
    (hp : prevMatch L prev pt) (hm : matchedUpTo L prev ents j) (hb : prev + 1 + j ≤ L.length) :
    prevMatch (L.take (prev + j)) prev pt ∧ matchedUpTo (L.take (prev + j)) prev ents j ∧
      (L.take (prev + j)).length = prev + j := by
  have hlen : (L.take (prev + j)).length = prev + j := by simp; omega
  refine ⟨?_, ⟨hm.1, fun j' hj' => ?_⟩, hlen⟩
  · rcases hp with hp | ⟨h1, h2⟩
    · left; exact hp
    · right; refine ⟨by omega, ?_⟩; rw [termAt_take _ _ _ (by omega)]; exact h2
  · obtain ⟨h1, h2⟩ := hm.2 j' hj'
    refine ⟨by omega, ?_⟩
    rw [termAt_take _ _ _ (by omega)]; exact h2

theorem matched_store (L : RLog) (prev pt : Nat) (ents : RLog) (j : Nat)
    (hp : prevMatch L prev pt) (hm : matchedUpTo L prev ents j) (hl : L.length = prev + j)
    (hj : j ≤ ents.length) :
    prevMatch (L ++ ents.drop j) prev pt ∧ matchedUpTo (L ++ ents.drop j) prev ents ents.length := by
  refine ⟨?_, ⟨Nat.le_refl _, fun j' hj' => ?_⟩⟩
  · rcases hp with hp | ⟨h1, h2⟩
    · left; exact hp
    · right; refine ⟨by simp; omega, ?_⟩; rw [termAt_append_left _ _ _ h1]; exact h2
  · by_cases hjj : j' < j
    · obtain ⟨h1, h2⟩ := hm.2 j' hjj
      refine ⟨by simp; omega, ?_⟩
      rw [termAt_append_left _ _ _ h1]; exact h2
    · refine ⟨by simp; omega, ?_⟩
      rw [termAt_append_right _ _ _ (by omega), termAt_drop _ _ _ (by omega)]
      congr 1; omega

theorem len_eq_of_break (L : RLog) (prev pt : Nat) (ents : RLog) (k : Nat)
    (hp : prevMatch L prev pt) (hm : matchedUpTo L prev ents k) (hlt : L.length < prev + 1 + k)
    (h1 : 1 ≤ L.length) : L.length = prev + k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rcases hp with hp | ⟨hp, _⟩ <;> omega
  · have := (hm.2 (k - 1) (by omega)).1; omega

theorem ent_store (L ents : RLog) (prev j m : Nat) (hl : L.length = prev + j) :
    ent (L ++ ents.drop j) (prev + 1 + j + m) = ents[j + m]? := by
  rw [ent_append_right _ _ _ (by omega), ent_drop _ _ _ (by omega)]
  unfold ent
  rw [if_neg (by omega)]
  congr 1; omega


/-! ### The log store's map (stage 3) -/

instance logAbs_inhabited_h : Inhabited LogAbs := ⟨LogAbs.empty⟩

theorem logIns_lookup_h (es : RLog) : ∀ (m : GMap Nat Entry) (first k : Nat),
    (LogAbs.ins m first es).lookup k =
      if first ≤ k ∧ k < first + es.length then es[k - first]? else m.lookup k := by
  induction es with
  | nil => intro m first k; simp only [LogAbs.ins, List.length_nil]; rw [if_neg (by omega)]
  | cons e es ih =>
    intro m first k
    simp only [LogAbs.ins]
    rw [ih]
    by_cases hk : k = first
    · subst hk
      rw [if_neg (by omega), if_pos (by simp), GMap.lookup_insert_eq_iff, if_pos rfl]; simp
    · by_cases h1 : first + 1 ≤ k ∧ k < first + 1 + es.length
      · rw [if_pos h1, if_pos (by simp; omega)]
        rw [show k - first = (k - (first + 1)) + 1 by omega]; simp
      · rw [if_neg h1, if_neg (by simp; omega), GMap.lookup_insert_eq_iff, if_neg (Ne.symm hk)]

/-- `logCell`'s facts about the store's map `M` and the log `L` (from the frontier `lo`). -/
def logMapOk (M : GMap Nat Entry) (L : RLog) (lo : Nat) : Prop :=
  (∀ k e, M.lookup k = some e → ent L k = some e) ∧
    (∀ k, lo ≤ k → k ≤ L.length → M.lookup k = ent L k)

/-- A `DeleteRange(mn, |L|)` with the log cut to `mn - 1` entries. -/
theorem logMapOk_trunc (M : GMap Nat Entry) (L : RLog) (lo mn : Nat) (hmn : 1 ≤ mn)
    (h : logMapOk M L lo) :
    logMapOk (LogAbs.del M mn L.length) (L.take (mn - 1)) lo := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro k e hk
    simp only [LogAbs.del, GMap.lookup_filter] at hk
    cases hm : M.lookup k with
    | none => rw [hm] at hk; simp at hk
    | some e' =>
      rw [hm] at hk
      have he := h1 k e' hm
      have hb := ent_le_length he
      simp only [Option.filter, decide_eq_true_eq] at hk
      split at hk
      · rename_i hc
        cases hk
        rw [ent_take _ _ _ (by omega)]; exact he
      · cases hk
  · intro k hlo hk
    rw [List.length_take] at hk
    have hkl : k ≤ L.length := by omega
    have hkm : k < mn := by omega
    simp only [LogAbs.del, GMap.lookup_filter]
    rw [ent_take _ _ _ (by omega), ← h2 k hlo hkl]
    cases M.lookup k with
    | none => rfl
    | some e' => simp only [Option.filter, decide_eq_true_eq]; rw [if_pos (by omega)]

/-- A `StoreLogs` of `es` at `|L| + 1`. -/
theorem logMapOk_store (M : GMap Nat Entry) (L es : RLog) (lo : Nat) (h : logMapOk M L lo) :
    logMapOk (LogAbs.ins M (L.length + 1) es) (L ++ es) lo := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro k e hk
    rw [logIns_lookup_h] at hk
    split at hk
    · rename_i hc
      rw [ent_append_right _ _ _ (by omega)]
      rw [show k - L.length = (k - (L.length + 1)) + 1 by omega, ent_succ]; exact hk
    · have he := h1 k e hk
      rw [ent_append_left _ _ _ (ent_le_length he).2]; exact he
  · intro k hlo hk
    rw [logIns_lookup_h]
    split
    · rename_i hc
      rw [ent_append_right _ _ _ (by omega)]
      rw [show k - L.length = (k - (L.length + 1)) + 1 by omega, ent_succ]
    · rename_i hc
      have hkl : k ≤ L.length := by simp at hk; omega
      rw [ent_append_left _ _ _ hkl]; exact h2 k hlo hkl

end proto

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

theorem pkgGlobals_access :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ⊢ pkgGlobals (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.hashicorp.raft

instance hdrOk_persistent (h : RPCHeader) (snd : proto.SID) : Persistent (hdrOk (GF := GF) h snd) := by
  unfold hdrOk; infer_instance

open proto gprot in
theorem aeRespP_intro (γ : GNames) (i : SID) (T k : Nat) (hb : Prop) (ss : Snap) (l : Loc)
    (rpv : AppendEntriesResponse) :
    l ↦ rpv ∗ termOk γ (uint.nat rpv.Term') ∗
      (⌜rpv.Success' = false⌝ ∨ (⌜hb⌝ ∨ ackIs γ i T k) ∗ respWit γ i T ss) ∗
      hdrOk rpv.RPCHeader' i ⊢
    rpcRespP (GF := GF) AppendEntriesResponse.ty
      (fun q => iprop(∃ rp : AppendEntriesResponse, q ↦ rp ∗ aeResp γ rp i T k hb ss))
      (RPCResponse.mk (interface.mkOk (go.GoType.PointerType AppendEntriesResponse.ty) #l) interface.nil) := by
  iintro ⟨Hl, #Hok, Hs, #Hh⟩
  unfold rpcRespP
  iright
  iexists l
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iexists rpv
  iframe Hl
  unfold aeResp
  iframe Hok Hs
  iexists i; iexact Hh

open proto gprot in
/-- Writing the `CurrentTerm` key of the stable store keeps the last vote. -/
theorem voteMatches_term (sst : StableAbs) (s : SState) (v : w64) (t : Nat)
    (h : voteMatches sst s) :
    voteMatches { sst with ints := sst.ints.insert (go!"CurrentTerm" : List w8) v }
      { s with term := t } := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

open proto gprot in
/-- Reassembling the main goroutine's resources (a non-leader state). (Stage 3: the `lastApplied`
authority half, the pending-install half `none`, the compaction authority at `c ≤ a`.) -/
theorem mainOwnAt_intro (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32)
    (a : Nat) (sst : StableAbs) (cfg ccfg : Configuration) (cidx li : w64) (lch : Loc)
    (γl : ChanNames) (bs : List Bool) (c : Nat) (hvm : voteMatches sst s) (hst : st ≠ stLeader)
    (ha : a ≤ s.dur.1 ∧ s.cidx ≤ a) (hc : c ≤ a)
    (hcc : uint.nat li = lastCfgIdx s.log ∧
      (cidx = li ∨ (uint.nat cidx = lastCfgIdx (s.log.take (uint.nat li - 1)) ∧ a < uint.nat li)))
    (hcap : sint.Z γl.chanCap = 1 ∧ bs.length ≤ 1) :
    srvOwn γ i s ∗ durView γ i (1 : Qp).half s.dur.1 ∗ rc.ownS sst ∗
      ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
      ghostVar rc.names.state (1 : Qp).half st ∗ monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗
      fsmProd γ rc a ∗ r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
      cfgAtIs γ s.log (uint.nat li) cfg ∗ cfgAtIs γ s.log (uint.nat cidx) ccfg ∗
      cmtIdx γ s.term s.log (uint.nat cidx) ∗
      r.[Raft, go!"leaderCh"] ↦□ lch ∗ isChan lch γl Bool ∗
      ownChan γl Bool (.Buffered bs) ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
      verifyRegistry γ rc i ∗
      ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
      monoNatAuthOwn rc.dur.comp 1 c ⊢ mainOwnAt r γ rc i s st := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

open proto gprot in
theorem aeValid_ent (γ : GNames) (T prev pt : Nat) (ents : RLog) (lci j : Nat) (e : Entry)
    (h : ents[j]? = some e) :
    aeValid (GF := GF) γ T prev pt ents lci ⊢ llogIdx γ T (prev + 1 + j) e := by
  unfold aeValid
  iintro ⟨-, -, #Hl, -⟩
  iapply BigSepL.bigSepL_lookup h $$ Hl

open proto gprot in
theorem ptrs_drop (ptrs : List Loc) (ents : RLog) (prev j : Nat) :
    ([∗list] k ↦ p ∈ ptrs, ∃ e, ⌜ents[k]? = some e⌝ ∗ logPtr (GF := GF) p (prev + 1 + k) e) ⊢
      [∗list] k ↦ p ∈ ptrs.drop j, ∃ e, ⌜(ents.drop j)[k]? = some e⌝ ∗ logPtr p (prev + 1 + j + k) e := by
  iintro H
  ihave ⟨-, H⟩ := (BigSepL.bigSepL_take_drop (n := j)).1 $$ H
  iapply BigSepL.bigSepL_mono_of_forall ?_ $$ H
  intro k x
  iintro ⟨%e, %h, Hp⟩
  iexists e
  isplitr
  · ipureintro; rw [List.getElem?_drop]; exact h
  rw [show prev + 1 + j + k = prev + 1 + (j + k) by omega]
  iexact Hp

open proto gprot in
/-- Reassembling the main goroutine's resources (any state, with its leader witness). -/
theorem mainOwnAt_intro' (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (st : w32)
    (a : Nat) (sst : StableAbs) (cfg ccfg : Configuration) (cidx li : w64) (lch : Loc)
    (γl : ChanNames) (bs : List Bool) (c : Nat) (hvm : voteMatches sst s)
    (ha : a ≤ s.dur.1 ∧ s.cidx ≤ a) (hc : c ≤ a)
    (hcc : uint.nat li = lastCfgIdx s.log ∧
      (cidx = li ∨ (uint.nat cidx = lastCfgIdx (s.log.take (uint.nat li - 1)) ∧ a < uint.nat li)))
    (hcap : sint.Z γl.chanCap = 1 ∧ bs.length ≤ 1) :
    srvOwn γ i s ∗ durView γ i (1 : Qp).half s.dur.1 ∗ rc.ownS sst ∗
      ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
      ghostVar rc.names.state (1 : Qp).half st ∗
      (⌜st ≠ stLeader⌝ ∨ leaderIs γ s.term i ∗ (∃ m : Nat, pubOwn γ i s.term m ∗ ⌜m ≤ a⌝) ∗
        ccfgOwn γ i s.term (lastCfgIdx s.log) ∗
        ∃ n0 : Nat, len0Is γ s.term n0 ∗
          (⌜s.cidx ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜s.cidx ≤ k⌝) ∗
          (⌜cidx ≠ li ∨ uint.nat li ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s.term k p ∗ ⌜uint.nat li ≤ k⌝)) ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗
      fsmProd γ rc a ∗ r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
      cfgAtIs γ s.log (uint.nat li) cfg ∗ cfgAtIs γ s.log (uint.nat cidx) ccfg ∗
      cmtIdx γ s.term s.log (uint.nat cidx) ∗
      r.[Raft, go!"leaderCh"] ↦□ lch ∗ isChan lch γl Bool ∗
      ownChan γl Bool (.Buffered bs) ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
      verifyRegistry γ rc i ∗
      ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
      monoNatAuthOwn rc.dur.comp 1 c ⊢ mainOwnAt r γ rc i s st := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

open proto gprot in
theorem obsArg_state (γ : GNames) (i : SID) (s : SState) (st : w32) (h : st ≠ stLeader) :
    ⊢ obsArg (GF := GF) γ i s (interface.mkOk RaftState.ty #st) := by
  apply obsArg_other
  rotate_left
  · intro v hv; rw [interface_mkOk_inj] at hv; exact ⟨st, hv.2.symm⟩
  unfold leaderObs
  rw [Ne, interface_mkOk_inj]
  intro ⟨_, h2⟩
  apply h
  exact go.IntoValInj.intoVal_inj (V := w32) h2

open proto gprot in
theorem rvRespP_intro (γ : GNames) (i c : SID) (T : Nat) (l : Loc) (rpv : RequestVoteResponse) :
    l ↦ rpv ∗ termOk γ (uint.nat rpv.Term') ∗ (⌜rpv.Granted' = false⌝ ∨ voteIs γ i T c) ∗
      (∃ b : List w8, rpv.Peers' ↦*□ b) ∗ hdrOk rpv.RPCHeader' i ⊢
    rpcRespP (GF := GF) RequestVoteResponse.ty
      (fun q => iprop(∃ rp : RequestVoteResponse, q ↦ rp ∗ rvResp γ rp i c T))
      (RPCResponse.mk (interface.mkOk (go.GoType.PointerType RequestVoteResponse.ty) #l) interface.nil) := by
  iintro ⟨Hl, #Hok, Hs, #Hpe, #Hh⟩
  unfold rpcRespP
  iright
  iexists l
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iexists rpv
  iframe Hl
  unfold rvResp
  iframe Hok Hs Hpe
  iexists i; iexact Hh

open proto gprot in
theorem pvRespP_intro (γ : GNames) (i : SID) (T : Nat) (l : Loc) (rpv : RequestPreVoteResponse) :
    l ↦ rpv ∗ (⌜uint.nat rpv.Term' = T⌝ ∨ termOk γ (uint.nat rpv.Term')) ∗ hdrOk rpv.RPCHeader' i ⊢
    rpcRespP (GF := GF) RequestPreVoteResponse.ty
      (fun q => iprop(∃ rp : RequestPreVoteResponse, q ↦ rp ∗ pvResp γ rp T))
      (RPCResponse.mk (interface.mkOk (go.GoType.PointerType RequestPreVoteResponse.ty) #l) interface.nil) := by
  iintro ⟨Hl, Hok, #Hh⟩
  unfold rpcRespP
  iright
  iexists l
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iexists rpv
  iframe Hl
  unfold pvResp
  iframe Hok
  iexists i; iexact Hh

open proto gprot in
theorem aeReq_ver (γ : GNames) (rq : AppendEntriesRequest) snd T prev pt ents lci ss :
    aeReq (GF := GF) γ rq snd T prev pt ents lci ss ⊢ ⌜rq.RPCHeader'.ProtocolVersion' = W64 3⌝ := by
  unfold aeReq hdrOk; iintro ⟨-, ⟨%h, -⟩, -⟩; ipureintro; exact h

open proto gprot in
theorem rvReq_ver (γ : GNames) (rq : RequestVoteRequest) c T li lt :
    rvReq (GF := GF) γ rq c T li lt ⊢ ⌜rq.RPCHeader'.ProtocolVersion' = W64 3⌝ := by
  unfold rvReq hdrOk; iintro ⟨-, ⟨%h, -⟩, -⟩; ipureintro; exact h

open proto gprot in
theorem pvReq_ver (rq : RequestPreVoteRequest) c T :
    pvReq (GF := GF) rq c T ⊢ ⌜rq.RPCHeader'.ProtocolVersion' = W64 3⌝ := by
  unfold pvReq hdrOk; iintro ⟨-, %h, -⟩; ipureintro; exact h

section rb
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open proto gprot in
instance logCouple_timeless (γ : GNames) (i : SID) (L : RLog) :
    Timeless (logCouple (GF := GF) γ i L) := by
  unfold logCouple; infer_instance

open proto gprot in
instance termCouple_timeless (γ : GNames) (i : SID) (t : Nat) :
    Timeless (termCouple (GF := GF) γ i t) := by
  unfold termCouple; infer_instance

open proto gprot in
instance cidxCouple_timeless (γ : GNames) (i : SID) (c : Nat) :
    Timeless (cidxCouple (GF := GF) γ i c) := by
  unfold cidxCouple; infer_instance

open proto gprot in
/-- An atomic read of the log store (`GetLog`), by the main goroutine (`srvOwn`): (stage 3) every
entry the store holds is the server's log's. -/
theorem logCell_read (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (Ψ : LogAbs → IProp GF) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvOwn γ i s ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
      (∀ A : LogAbs, ⌜∀ k e, A.m.lookup k = some e → ent s.log k = some e⌝ -∗
        srvOwn γ i s -∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) -∗ Ψ A) ⊢
      |={⊤,∅}=> ▷ ∃ A, rc.ownL A ∗ (rc.ownL A ={∅,⊤}=∗ Ψ A) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

open proto gprot in
/-- The log store's `DeleteRange(prev+1+j, |log|)` by the main goroutine: the protocol step
`truncate` at its linearization point. -/
theorem logCell_truncate (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState)
    (prev pt : Nat) (ents : RLog) (lci j : Nat) (mn mx : w64)
    (hpre : prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents j ∧ j < ents.length ∧
      prev + 1 + j ≤ s.log.length ∧ termAt s.log (prev + 1 + j) ≠ termAt ents (j + 1))
    (hmn : uint.nat mn = prev + 1 + j) (hmx : uint.nat mx = s.log.length) (Ψ : IProp GF) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvOwn γ i s ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
      aeValid γ s.term prev pt ents lci ∗
      (srvOwn γ i { s with log := s.log.take (prev + j) } -∗
        ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) -∗ Ψ) ⊢
      |={⊤,∅}=> ▷ ∃ A, rc.ownL A ∗
        (∀ hi' : w64, rc.ownL ⟨LogAbs.del A.m (uint.nat mn) (uint.nat mx), hi'⟩ ={∅,⊤}=∗ Ψ) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

open proto gprot in
/-- The log store's `StoreLogs(ents[j:])` by the main goroutine (its log ends at `prev + j`):
the protocol step `followerStore` at its linearization point. -/
theorem logCell_store (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState)
    (prev pt : Nat) (ents : RLog) (lci j : Nat)
    (hpre : prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents j ∧ j < ents.length ∧
      s.log.length = prev + j) (Ψ : IProp GF) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvOwn γ i s ∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗
      aeValid γ s.term prev pt ents lci ∗
      (srvOwn γ i { s with log := s.log ++ ents.drop j } -∗
        ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) -∗ Ψ) ⊢
      |={⊤,∅}=> ▷ ∃ A, rc.ownL A ∗
        (rc.ownL (A.store (prev + 1 + j) (ents.drop j)) ={∅,⊤}=∗ Ψ) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

open proto gprot in
/-- The server's own term, as a persistent lower bound (from the term cell). -/
theorem termLb_of_srv (γ : GNames) (r : Loc) (i : SID) (s : SState) :
    Inv (GF := GF) γ ∗ termCell r γ rc i ∗ srvOwn γ i s ⊢ |={⊤}=> srvOwn γ i s ∗ termLb γ i s.term := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

open proto gprot in
/-- The ghost update run at the `currentTerm` store (`raftState.setCurrentTerm`): the protocol
step `setTerm`. -/
theorem setTerm_step (γ : GNames) (i : SID) (s : SState) (t : Nat) (ht : s.term ≤ t) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ termOk γ t ⊢
      ∀ t0 : Nat, termCouple γ i t0 ={⊤ \ ↑termN}=∗ termCouple γ i t ∗
        (srvOwn γ i { s with term := t } ∗ termLb γ i t) := by
  iintro ⟨#HI, Hs, #Hok⟩ %t0 Hcp
  imod termCouple_agree γ (⊤ \ ↑termN) gprotN_termN i s _ $$ [$HI $Hs $Hcp] with ⟨Hs, Hcp, %h0⟩
  subst h0
  imod setTerm_upd γ (⊤ \ ↑termN) gprotN_termN i s t ht $$ [$HI $Hs $Hcp $Hok] with ⟨Hs, Hcp, #Hlb⟩
  imodintro
  iframe
  iexact Hlb

open proto gprot in
/-- The ghost update run at the `commitIndex` store (`setCommitIndex`): the protocol step
`setCidx`. -/
theorem setCidx_step (γ : GNames) (i : SID) (s : SState) (c : Nat) (hc : c ≤ s.dur.1) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ⊢
      ∀ c0 : Nat, cidxCouple γ i c0 ={⊤ \ ↑cidxN}=∗ cidxCouple γ i c ∗
        srvOwn γ i { s with cidx := c } := by
  iintro ⟨#HI, Hs⟩ %c0 Hcp
  imod cidxCouple_agree γ (⊤ \ ↑cidxN) gprotN_cidxN i s _ $$ [$HI $Hs $Hcp] with ⟨Hs, Hcp, %h0⟩
  subst h0
  imod setCidx_upd γ (⊤ \ ↑cidxN) gprotN_cidxN i s c hc $$ [$HI $Hs $Hcp] with ⟨Hs, Hcp⟩
  imodintro
  iframe

open proto gprot in
theorem llogIdx_eq_one_g (γ : GNames) (E : CoPset) (hE : ↑gprotN ⊆ E) (T c : Nat) (e : Entry) :
    Inv (GF := GF) γ ∗ llogIdx γ T c e ⊢ |={E}=> ⌜c = 1 → e = γ.g⌝ := by
  by_cases hc : c = 1
  · subst hc
    iintro H
    imod llogIdx_one γ E hE T e $$ H with %h
    imodintro; ipureintro; intro _; exact h
  · iintro -
    imodintro; ipureintro; intro h; exact absurd h hc

open proto gprot in
theorem durView_halves (γ : GNames) (i : SID) (d : Nat) :
    durView (GF := GF) γ i (1 : Qp).half d ⊣⊢
      durView γ i (1 : Qp).half.half d ∗ durView γ i (1 : Qp).half.half d := by
  have h := durView_split (GF := GF) γ i (1 : Qp).half.half (1 : Qp).half.half d
  rw [Qp.half_add_half] at h
  exact h

open proto gprot in
/-- The `state` cell holds one of the three states (the main goroutine's half agrees). -/
theorem stateCell_val (r : Loc) (rc : RCtx GF) (st : w32) :
    stateCell r rc ∗ ghostVar rc.names.state (1 : Qp).half st ⊢ |={⊤}=>
      ghostVar rc.names.state (1 : Qp).half st ∗ ⌜st = stFollower ∨ st = stCandidate ∨ st = stLeader⌝ := by
  iintro ⟨#Hc, Hst⟩
  unfold stateCell
  iinv Hc with ⟨%st', Hpt, >Hg, >%Hv⟩ Hclose
  ihave %he := ghostVar_agree _ _ _ _ _ $$ Hst Hg
  subst he
  imod Hclose $$ [Hpt Hg] with -
  · inext; iexists st; iframe; ipureintro; exact Hv
  imodintro
  iframe; ipureintro; exact Hv

open proto gprot in
/-- The leader part of `mainOwnAt` survives handing more to the FSM. -/
theorem stl_mono (γ : GNames) (i : SID) (st : w32) (T a a' : Nat) (h : a ≤ a') :
    (⌜st ≠ stLeader⌝ ∨ leaderIs (GF := GF) γ T i ∗ ∃ m : Nat, pubOwn γ i T m ∗ ⌜m ≤ a⌝) ⊢
      (⌜st ≠ stLeader⌝ ∨ leaderIs γ T i ∗ ∃ m : Nat, pubOwn γ i T m ∗ ⌜m ≤ a'⌝) := by
  iintro (%H | ⟨#Hl, %m, Hp, %Hm⟩)
  · ileft; ipureintro; exact H
  · iright; iframe Hl; iexists m; iframe; ipureintro; omega

open proto gprot in
/-- The leader of a valid AppendEntries request. -/
theorem aeValid_leader (γ : GNames) (T prev pt : Nat) (ents : RLog) (lci : Nat) :
    aeValid (GF := GF) γ T prev pt ents lci ⊢ ∃ ℓ, leaderIs γ T ℓ := by
  unfold aeValid
  iintro ⟨⟨%ℓ, #Hl⟩, -⟩
  iexists ℓ; iexact Hl

open proto gprot in
/-- A leader of its current term receiving a valid AppendEntries request of that term: each entry
is already in its log (it is the leader log). -/
theorem aeValid_self (γ : GNames) (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState)
    (prev pt : Nat) (ents : RLog) (lci j : Nat) (e : Entry) (he : ents[j]? = some e) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ leaderIs γ s.term i ∗ aeValid γ s.term prev pt ents lci ⊢
      |={E}=> srvOwn γ i s ∗ ⌜ent s.log (prev + 1 + j) = some e⌝ := by
  iintro ⟨#HI, Hs, #Hl, #Hae⟩
  ihave #He := aeValid_ent γ s.term prev pt ents lci j e he $$ Hae
  iapply llogIdx_leader γ E hE i s (prev + 1 + j) e $$ [$HI $Hs $Hl $He]

open proto gprot in
/-- The post of `appendEntries` (and `processRPC`'s AppendEntries case): stepped down, or not
(a transfer candidate, `candidateFromLeadershipTransfer`): then the request's leader is `i` itself
(its log did not change) or another server (and `i` is a candidate). -/
theorem ae_post (γ : GNames) (i ℓ : SID) (st st1 : w32) (s s' : SState) (T : Nat)
    (hcase : st1 = stFollower ∨ (st1 = st ∧ T = s.term ∧ st ≠ stFollower ∧ (ℓ ≠ i → st = stCandidate)))
    (hterm : s'.term = T) (hlog : st1 ≠ stFollower → ℓ = i → s'.log = s.log) :
    leaderIs (GF := GF) γ T ℓ ⊢
      (⌜st1 = stFollower ∨ (st1 = st ∧ s'.term = s.term ∧ s'.log = s.log)⌝ ∨
       ⌜st1 = st ∧ st = stCandidate ∧ s'.term = s.term⌝ ∗ ∃ ℓ' : SID, ⌜ℓ' ≠ i⌝ ∗ leaderIs γ s.term ℓ') := by
  iintro #Hl
  rcases hcase with h | ⟨h1, h2, h3, h4⟩
  · ileft; ipureintro; left; exact h
  · by_cases hℓ : ℓ = i
    · ileft; ipureintro; right
      exact ⟨h1, by rw [hterm, h2], hlog (by rw [h1]; exact h3) hℓ⟩
    · iright
      isplitr
      · ipureintro; exact ⟨h1, h4 hℓ, by rw [hterm, h2]⟩
      iexists ℓ
      isplitr
      · ipureintro; exact hℓ
      rw [← h2]; iexact Hl

open proto gprot in
/-- The entries of a valid request from `j` on, each its own term's leader-log entry
(`gprot.llogIdx_own`): what the log store's `StoreLogs` takes (stage 2). -/
theorem aeValid_own_drop (γ : GNames) (E : CoPset) (hE : ↑gprotN ⊆ E) (T prev pt : Nat)
    (ents : RLog) (lci j : Nat) :
    Inv (GF := GF) γ ∗ aeValid γ T prev pt ents lci ⊢
      |={E}=> [∗list] k ↦ e ∈ ents.drop j, llogIdx γ e.term (prev + 1 + j + k) e := by
  iintro ⟨#HI, #Hae⟩
  unfold aeValid
  icases Hae with ⟨-, -, #Hl, -⟩
  ihave ⟨-, #Hd⟩ := (BigSepL.bigSepL_take_drop (n := j)).1 $$ Hl
  iapply BigSepL2.bigSepL_fupd
  ihave Hw := (BigSepL.bigSepL_intro (P := iprop(□ Inv (GF := GF) γ)) (l := ents.drop j)
    (Φ := fun k e => iprop(llogIdx (GF := GF) γ T (prev + 1 + (j + k)) e -∗
      |={E}=> llogIdx γ e.term (prev + 1 + j + k) e)) ?_) $$ HI
  · intro k e _
    iintro #HI' #He
    rw [show prev + 1 + (j + k) = prev + 1 + j + k by omega]
    iapply llogIdx_own γ E hE T (prev + 1 + j + k) e $$ [$HI' $He]
  iapply BigSepL.bigSepL_wand $$ Hd Hw

end rb

end lemmas

end github_com.hashicorp.raft

end Perennial
