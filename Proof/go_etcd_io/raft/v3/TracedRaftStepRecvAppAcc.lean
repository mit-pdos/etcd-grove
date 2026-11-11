/-
Lean-first (no Rocq counterpart). **An accepted `MsgApp`'s receive line: raft's facts of the new log and
the specification state's facts through the line** (2026-11-11, trace-check Q8 stage 1 slice 24c,
`notes/decisions.md`, "Q8 stage 1 (slice 24c)").

At a follower of the request's term whose log matches the request's previous entry (`HandleAppResult`'s
second exit, raft's `maybeAppend` succeeding), the specification's receive line is the truncations,
the append and `AppendEntriesAlreadyDone` (`lineEffect_appRecv`, `chain_appAccept`), through the
intermediate servers `appMid`: the log truncated to `k` entries (`p ≤ k`, past a conflict) or the new
log, the leader adopted. This file proves what the line's facts (`FxPresR`) need:

- **raft's facts of the new log** (`ownRaftGhost_appAccFacts`, `Step.appAccept`'s
  `ownRaftGhost_step_app_accept` without the step): the new log's records (the kept prefix's and the
  request's leader's), its commit certificate at the raised commit index (`commitIn_move`) and its
  committed prefix;
- **the intermediate states' facts** (`simFx_appLog`): a receiver's log replaced by one that keeps the
  committed prefix and every prefix the request agrees with (`QuorumLogF` by `quorumLogF_appLog`, the
  generalization of amendment A5's `quorumLogF_conflict` to any such log; `SpecInv` by
  `specInv_upd_followerLog`);
- **the end state's facts** (`simFx_appDone`): `AppendEntriesAlreadyDone` from the new log
  (`quorumLogF_alreadyDone`, `specInv_appendEntriesAlreadyDone`), the raised commit's certificate.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvAppRej
public import Proof.go_etcd_io.raft.v3.TracedQuorumLog
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUTResp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- **A conflict bounds every prefix the request agrees with**: a prefix `P` of the abstract log `L`
that an append request agrees with (`AppAgrees`) ends at or before the request's first conflict with
`L` (`ConflictBy ents L p k`, at a position `≤ k`), so is a prefix of `L`'s first `k` entries. -/
theorem prefix_take_of_conflict (C : List w64) (P : List Etcdraft.Entry) (L ents : List EntryM) (p k : Nat)
    (ma : Etcdraft.Msg) (hprev : ma.prevLogIndex = p) (hents : ma.entries = logAbs C C.length (p + 1) ents)
    (hbL : BootTerms C.length 1 L) (hbe : BootTerms C.length (p + 1) ents)
    (hP : P <+: logAbs C C.length 1 L) (hag : AppAgrees P ma) (hc : ConflictBy ents L p k) :
    P <+: logAbs C C.length 1 (L.take k) := by
  obtain ⟨q, x, hqk, hx, hne⟩ := hc
  have hpn : ma.prevLogIndex.toNat = p := by rw [hprev]; simp
  have hPl : P.length ≤ p + q := by
    apply Nat.le_of_not_lt; intro hlt
    have h1 := hag q (entAbs C C.length (p + 1 + q) x) (by rw [hents, logAbs_getElem?, hx]; rfl)
      (by rw [hpn]; exact hlt)
    rw [hpn, prefix_getElem?_of_lt hP hlt, logAbs_getElem?] at h1
    cases hy : L[p + q]? with
    | none => rw [hy] at h1; cases h1
    | some y =>
      rw [hy] at h1 hne
      simp only [Option.map_some, Option.some.injEq] at h1 hne
      have ht := congrArg Etcdraft.Entry.term h1
      rw [entAbs_term C C.length _ y (fun hb => hbL (p + q) y (by omega) hy),
        entAbs_term C C.length _ x (fun hb => hbe q x (by omega) hx)] at ht
      exact hne (congrArg some (uint_Z_inj.mp ht))
  rw [← logAbs_take, List.prefix_iff_eq_take.mp hP]
  exact take_prefix_le _ _ _ (by
    have := hP.length_le; rw [logAbs_length] at this; omega)

/-- **The new log keeps every prefix the request agrees with** (`maybeAppend`'s new log `es'`: the log
itself, or its first `p + d` entries, before the first conflict `d`, followed by the batch from `d`). -/
theorem prefix_newLog (C : List w64) (P : List Etcdraft.Entry) (L ents es' : List EntryM) (p : Nat)
    (lt lastnewi : w64) (ma : Etcdraft.Msg) (hprev : ma.prevLogIndex = p)
    (hents : ma.entries = logAbs C C.length (p + 1) ents)
    (hbL : BootTerms C.length 1 L) (hbe : BootTerms C.length (p + 1) ents)
    (hwf : ∀ (k : Nat) (e : EntryM), ents[k]? = some e → uint.Z e.Index' = (p : Int) + k + 1)
    (hp : p < 2 ^ 64) (hnw : (p : Int) + ents.length + 1 < 2 ^ 64)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) L (entryID.mk lt (W64 p)) ents = some (lastnewi, es'))
    (hP : P <+: logAbs C C.length 1 L) (hag : AppAgrees P ma) :
    P <+: logAbs C C.length 1 es' := by
  obtain ⟨hpl, -, hcase⟩ := maybeAppend_spec L ents es' p lt lastnewi hwf hp hnw happ
  rcases hcase with ⟨rfl, -, -⟩ | ⟨d, hd, hpd, rfl, -, -, hbef, hconf⟩
  · exact hP
  have hPd : P <+: logAbs C C.length 1 (L.take (p + d)) := by
    rcases Nat.lt_or_ge (p + d) L.length with hlt | hge
    · apply prefix_take_of_conflict C P L ents p (p + d) ma hprev hents hbL hbe hP hag
      obtain ⟨x, hx⟩ : ∃ x, ents[d]? = some x := ⟨ents[d], List.getElem?_eq_getElem hd⟩
      refine ⟨d, x, Nat.le_refl _, hx, fun hmt => hconf (p + d + 1) (by omega) (by omega) ?_⟩
      intro k e' hk hlk
      rw [List.getElem?_take_of_lt hlk]
      rcases Nat.lt_or_ge k d with hkd | hkd
      · have := hbef k e' hk (by omega)
        rwa [List.getElem?_take_of_lt (by omega)] at this
      · have : k = d := by omega
        subst this; rw [hx] at hk; cases hk; exact hmt
    · rw [List.take_of_length_le (by omega)]; exact hP
  refine hPd.trans ?_
  have : (L.take (p + d) ++ ents.drop d).take (p + d) = L.take (p + d) := by
    rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_self]
  have h2 := List.take_prefix (p + d) (logAbs C C.length 1 (L.take (p + d) ++ ents.drop d))
  rw [logAbs_take, this] at h2
  exact h2

/-- **The new log's entries**: each of the old log's, at its position, or the request's. -/
theorem newLog_entries (C : List w64) (L ents es' : List EntryM) (p : Nat) (lt lastnewi : w64)
    (ma : Etcdraft.Msg) (hprev : ma.prevLogIndex = p) (hents : ma.entries = logAbs C C.length (p + 1) ents)
    (hwf : ∀ (k : Nat) (e : EntryM), ents[k]? = some e → uint.Z e.Index' = (p : Int) + k + 1)
    (hp : p < 2 ^ 64) (hnw : (p : Int) + ents.length + 1 < 2 ^ 64)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) L (entryID.mk lt (W64 p)) ents = some (lastnewi, es')) :
    ∀ (k : Nat) (e : Etcdraft.Entry), (logAbs C C.length 1 es')[k]? = some e →
      (logAbs C C.length 1 L)[k]? = some e ∨ ∃ j, ma.entries[j]? = some e ∧ k = ma.prevLogIndex.toNat + j := by
  obtain ⟨hpl, -, hcase⟩ := maybeAppend_spec L ents es' p lt lastnewi hwf hp hnw happ
  intro k e he
  rcases hcase with ⟨rfl, -, -⟩ | ⟨d, hd, hpd, rfl, -, -, -, -⟩
  · exact .inl he
  rw [logAbs_getElem?, List.getElem?_append] at he
  simp only [List.length_take, Nat.min_eq_left hpd] at he
  split at he
  · rename_i hk
    left; rw [logAbs_getElem?, ← List.getElem?_take_of_lt hk]; exact he
  · rename_i hk
    right
    refine ⟨k - p, ?_, by rw [hprev]; simp; omega⟩
    rw [List.getElem?_drop, show d + (k - (p + d)) = k - p by omega] at he
    rw [hents, logAbs_getElem?, show p + 1 + (k - p) = 1 + k by omega]; exact he

/-- **A truncated log's entries** are the old log's. -/
theorem takeLog_entries (C : List w64) (L : List EntryM) (n : Nat) :
    ∀ (k : Nat) (e : Etcdraft.Entry), (logAbs C C.length 1 (L.take n))[k]? = some e →
      (logAbs C C.length 1 L)[k]? = some e := by
  intro k e he
  rw [← logAbs_take, List.getElem?_take] at he
  split at he
  · exact he
  · cases he

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- One entry's record out of `logRecs` (`Enter.lean`'s private `logRecs_elem'`). -/
private theorem logRecs_elemA (γ : RaftNames) (b : entryID) (es : List EntryM)
    (k : Nat) (x : EntryM) :
    es[k]? = some x → uint.Z b.index' + (k : Int) + 1 < 2 ^ 64 →
    logRecs (GF := GF) γ b es ⊢ ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR γ x pt := by
  intro Hk Hr
  unfold logRecs
  refine (BigSepL.bigSepL_lookup (Φ := fun k e =>
    if uint.Z b.index' + (k : Int) + 1 < 2 ^ 64
    then iprop(∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR (GF := GF) γ e pt)
    else iprop(True)) Hk).trans ?_
  simp only [Hr, ↓reduceIte]
  exact .rfl

/-- `logRecs` from each in-range entry's record (`Enter.lean`'s private `logRecs_intro'`). -/
private theorem logRecs_introA (γ : RaftNames) (b : entryID) (es : List EntryM) :
    ⊢ □ (∀ (k : Nat) (x : EntryM),
          ⌜es[k]? = some x ∧ uint.Z b.index' + (k : Int) + 1 < 2 ^ 64⌝ →
          ∃ pt, ⌜plogTermAt b es (pidx b k) = some pt⌝ ∗ isEntryR (GF := GF) γ x pt) -∗
      logRecs γ b es := by
  iintro #H
  unfold logRecs
  iapply BigSepL.bigSepL_forall_elim
  iintro %k %x Hk
  ipure Hk
  split
  · rename_i Hr
    iapply H $$ %k %x
    ipureintro; exact ⟨Hk, Hr⟩
  · itrivial

/-- The commit index after an accepted append request (`HandleAppResult`'s second exit):
`committed` raised to `min(m.Commit, lastnewi)`. -/
def accCommit (c mc lastnewi : w64) : w64 :=
  plogCommitTo c (if uint.Z mc < uint.Z lastnewi then mc else lastnewi)

/-- **Raft's facts of an accepted append request's new log** (`ownRaftGhost_step_app_accept`'s, without
the step), at a node of the request's term with an uncompacted log whose commit index is at most the
request's previous index: the old log's records, certificate and committed prefix; the new log's
records (the kept prefix's, the leader's above the cut), its commit certificate at the raised commit
index (`commitIn_move`, from the request's or the old log's) and its committed prefix; both logs'
shapes. The ghost state is unchanged. -/
theorem ownRaftGhost_appAccFacts (γ : RaftNames) (id : w64) (s : PState) (m : Msg) {md : Bool}
    (lastnewi : w64) (es' : List EntryM)
    (Hty : m.ty = .app) (Hterm : m.term = s.term) (Hbase : s.base = base0)
    (Hcidx : uint.Z s.commit ≤ uint.Z m.index)
    (Happ : plogMaybeAppend base0 s.log (entryID.mk m.logterm m.index) m.entries = some (lastnewi, es')) :
    ⊢ isMessage (GF := GF) γ m -∗ ownRaftGhost γ id s md -∗
      ownRaftGhost γ id s md ∗
      (logRecs γ base0 s.log ∗ commitIn γ s.log s.commit s.term ∗
        isCommitted γ (s.log.take (uint.Z s.commit).toNat) ∗ logRecs γ base0 es' ∗
        commitIn γ es' (accCommit s.commit m.commit lastnewi) s.term ∗
        isCommitted γ (es'.take (uint.Z (accCommit s.commit m.commit lastnewi)).toNat)) ∗
      ⌜PlogWfR base0 s.log ∧ PlogWfR base0 es' ∧ uint.Z s.commit ≤ s.log.length ∧
        uint.Z lastnewi = uint.Z m.index + (m.entries.length : Int)⌝ := by
  iintro #Hm Hg
  ihave %Hok := ownRaftGhost_logOk γ id s $$ Hg
  icases persistent_entails_right (wand_entails (ownRaftGhost_lastRec (GF := GF) (md := md) γ id s)) $$ Hg
    with ⟨⟨-, %HB64⟩, Hg⟩
  rw [Hbase] at HB64
  icases ownRaftGhost_logFacts γ id s Hbase $$ Hg with ⟨Hg, ⟨#Hrecs, #Hcm0, #Hc⟩, %Hwf⟩
  iframe Hg
  obtain ⟨-, -, Hcl⟩ := Hok
  rw [Hbase] at Hcl
  have HlenB : plogLastIndexZ base0 s.log = s.log.length := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  rw [HlenB] at Hcl
  icases isMessage_app_inv γ m Hty $$ Hm with
    ⟨%Hpay, -, ⟨%bL, %l', %fpL, #Hp', %Hpl, #Hpf', #Hmc, #Hmcm, -⟩, -⟩
  obtain ⟨Hprev', Hpre'⟩ := Hpl
  rw [Hterm]
  ihave #HLf := leadFull_intro $$ Hp' Hpf'
  icases leadFull_wf γ s.term (fpL ++ l') $$ HLf with ⟨%HwLf, #HrLf⟩
  icases lpfull_fp $$ Hpf' with ⟨-, %HfL⟩
  obtain ⟨Hwfb, Hnw⟩ := Hpay
  obtain ⟨Hmatch, Hli, Hcase⟩ := plogMaybeAppend_inv _ _ _ _ _ _ Hwfb Hnw Happ
  have Hmatch' : plogTermAt base0 s.log m.index = some m.logterm := Hmatch
  obtain ⟨Hwf', Hlast'⟩ := plogMaybeAppend_wfR _ _ _ _ _ _ Hwf Hwfb Hnw Happ
  have Hbatch := plogMaybeAppend_batch _ _ _ _ _ _ Hwfb Hnw Happ
  have Hlb := plog_prefix_batch bL l' (entryID.mk m.logterm m.index) m.entries Hnw Hprev' Hpre'
  simp only at Hli Hbatch Hlb Hnw
  have Hpl := (plogTermAt_some_range _ _ _ _ Hmatch').2
  have HbL := (plogTermAt_some_range _ _ _ _ Hprev').1
  have Hagree : ∀ j : w64, uint.Z m.index ≤ uint.Z j →
      uint.Z j ≤ uint.Z m.index + (m.entries.length : Int) →
      plogTermAt base0 es' j = plogTermAt bL l' j ∧ (plogTermAt bL l' j).isSome := by
    intro j Hj1 Hj2
    rw [Hbatch j Hj1 Hj2, Hlb j Hj1 Hj2]
    refine ⟨rfl, plogTermAt_in_range _ _ _ ⟨Hj1, ?_⟩⟩
    unfold plogLastIndexZ; exact Hj2
  have HbZ : uint.Z (base0 : entryID).index' = 0 := base0_index
  have HmZ := uint_Z_lt m.index
  have Hm0 := uint_Z_nonneg m.index
  have HbL0 := uint_Z_nonneg bL.index'
  -- the new log's records
  ihave #Hrecs' : logRecs γ base0 es' $$ []
  · rcases Hcase with ⟨rfl, -⟩ | ⟨d, e, Hd, Hnm, Hbefore, Hei, Hend, Hes'⟩
    · iexact Hrecs
    dsimp only at Hei
    icases leadPrefix_wf γ m.src s.term bL l' $$ Hp' with ⟨%Hwfl, #Hrl⟩
    have Hdlen : d < m.entries.length := (List.getElem?_eq_some_iff.mp Hd).1
    subst Hes'
    iapply logRecs_introA
    imodintro
    iintro %k %x Hk
    ipure Hk
    obtain ⟨Hk, Hr⟩ := Hk
    · have Hn : (uint.Z e.Index' - uint.Z (base0 : entryID).index' - 1).toNat ≤ s.log.length := by
        unfold plogLastIndexZ at Hend; omega
      by_cases Hkn : k < (uint.Z e.Index' - uint.Z (base0 : entryID).index' - 1).toNat
      · rw [List.getElem?_append_left (by rw [List.length_take]; omega), List.getElem?_take] at Hk
        simp only [Hkn, ↓reduceIte] at Hk
        icases logRecs_elemA γ base0 s.log k x Hk (by omega) $$ Hrecs with ⟨%pt, %Hpt, #Hx⟩
        iexists pt
        iframe Hx
        ipureintro
        rw [← Hpt]
        apply plog_cut_keep _ _ _ _ _ ⟨by omega, by omega⟩
        unfold pidx
        rw [uint_Z_W64 _ (by omega) (by omega)]
        omega
      · have Hk' := Hk
        rw [List.getElem?_append_right (by rw [List.length_take]; omega), List.length_take,
          Nat.min_eq_left Hn, List.getElem?_drop] at Hk'
        have Hkk := (List.getElem?_eq_some_iff.mp Hk').1
        have Hx' := prefix_lookup_Some Hk' Hpre'
        unfold plogFrom at Hx'
        rw [List.getElem?_drop] at Hx'
        have Hadd : uint.Z (m.index + W64 1) = uint.Z m.index + 1 := by word
        rw [Hadd] at Hx'
        icases logRecs_elemA γ bL l' _ x Hx' (by omega) $$ Hrl with ⟨%pt, %Hpt, #Hx⟩
        iexists pt
        iframe Hx
        ipureintro
        have Hpj : pidx base0 k = W64 (uint.Z m.index +
            ((d + (k - (uint.Z e.Index' - uint.Z (base0 : entryID).index' - 1).toNat) : Nat) : Int)) := by
          unfold pidx; congr 1; omega
        have Hpj' : pidx bL ((uint.Z m.index + 1 - uint.Z bL.index' - 1).toNat +
            (d + (k - (uint.Z e.Index' - uint.Z (base0 : entryID).index' - 1).toNat))) =
            W64 (uint.Z m.index +
              ((d + (k - (uint.Z e.Index' - uint.Z (base0 : entryID).index' - 1).toNat) : Nat) : Int)) := by
          unfold pidx; congr 1; omega
        rw [Hpj'] at Hpt
        rw [Hpj, ← Hpt]
        refine (Hagree _ ?_ ?_).1
        · rw [uint_Z_W64 _ (by omega) (by omega)]; omega
        · rw [uint_Z_W64 _ (by omega) (by omega)]; omega
  -- the new log's last index
  have Hlast'' : plogLastIndexZ base0 es' < 2 ^ 64 := by
    rcases Hcase with ⟨rfl, -⟩ | ⟨d, e, Hd, Hnm, Hbefore, Hei, Hend, Hes'⟩
    · exact PlogWf_range _ _ (PlogWfR_wf _ _ Hwf (by omega))
    · dsimp only at Hei
      have Hdlen : d < m.entries.length := (List.getElem?_eq_some_iff.mp Hd).1
      rw [Hes', plog_cut_last _ _ _ _ ⟨by omega, Hend⟩, List.length_drop]
      omega
  have Hwl' : PlogWf base0 es' := PlogWfR_wf _ _ Hwf' Hlast''
  have Hw : PlogWf base0 s.log := PlogWfR_wf _ _ Hwf (by omega)
  -- the new log agrees with the old one up to the previous entry, with the leader's after it
  have Hlow : ∀ j : w64, uint.Z j ≤ uint.Z m.index → plogTermAt base0 es' j = plogTermAt base0 s.log j := by
    intro j Hj
    by_cases Hjm : uint.Z j = uint.Z m.index
    · have : j = m.index := uint_Z_inj.mp Hjm
      rw [this, (Hagree m.index (Int.le_refl _) (by omega)).1, Hprev', Hmatch']
    · rcases Hcase with ⟨rfl, -⟩ | ⟨d, e, Hd, Hnm, Hbefore, Hei, Hend, Hes'⟩
      · rfl
      · dsimp only at Hei
        rw [Hes', plog_cut_keep _ _ _ _ _ ⟨by omega, Hend⟩ (by omega)]
  have Hmid : ∀ j : w64, uint.Z m.index ≤ uint.Z j → uint.Z j ≤ uint.Z lastnewi →
      plogTermAt base0 es' j = plogTermAt base0 (fpL ++ l') j ∧
      (plogTermAt base0 (fpL ++ l') j).isSome := by
    intro j Hj1 Hj2
    obtain ⟨Heq, Hs⟩ := Hagree j Hj1 (by omega)
    rw [full_term_at bL fpL l' j HfL.1 (by omega)]
    exact ⟨Heq, Hs⟩
  obtain ⟨Hli', Hsli⟩ := Hmid lastnewi (by omega) (Int.le_refl _)
  ihave %HmL := full_match γ (fpL ++ l') es' lastnewi HwLf.1 Hwl' Hsli Hli'.symm $$ HrLf Hrecs'
  have HXle : uint.Z (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) ≤ uint.Z lastnewi := by
    split <;> omega
  have HXm : uint.Z (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) ≤ uint.Z m.commit := by
    split <;> omega
  have HcS : (plogTermAt base0 s.log s.commit).isSome :=
    plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by rw [HlenB]; exact Hcl⟩
  iframe Hrecs Hc Hcm0 Hrecs'
  isplitr
  · isplitr
    · unfold accCommit plogCommitTo
      generalize (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) = X at HXle HXm ⊢
      split
      · iapply commitIn_move γ (fpL ++ l') es' X s.term s.term (Int.le_refl _)
          HwLf.1 Hwl' (full_term_at_some _ _ lastnewi Hsli HXle) (HmL X HXle).symm $$ HrLf Hrecs'
        iapply commitIn_le γ (fpL ++ l') m.commit X s.term HwLf.1 HXm $$ HrLf Hmc
      · iapply commitIn_move γ s.log es' s.commit s.term s.term (Int.le_refl _)
          Hw Hwl' HcS (Hlow s.commit Hcidx) $$ Hrecs Hrecs' Hc
    · unfold accCommit plogCommitTo
      generalize (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) = X at HXle HXm ⊢
      split
      · ihave %Htk := full_take_eq γ (fpL ++ l') es' X HwLf.1 Hwl'
          (full_term_at_some _ _ lastnewi Hsli HXle) (HmL X HXle) $$ HrLf Hrecs'
        rw [← Htk]
        iapply isCommitted_mono γ _ _ (take_prefix_le _ _ _ (by omega)) $$ Hmcm
      · ihave %Htk := full_take_eq γ s.log es' s.commit Hw Hwl' HcS (Hlow s.commit Hcidx).symm $$ Hrecs Hrecs'
        rw [← Htk]; iexact Hcm0
  · ipureintro
    exact ⟨Hwf, Hwf', Hcl, Hli⟩

end ghost

end EtcdGrove
end Perennial
