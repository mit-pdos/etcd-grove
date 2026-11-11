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


section fx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A receiver's new log keeps `QuorumLogF`** (amendment A5's `quorumLogF_conflict`, for any new log
of the receiver `r` at the request's term that keeps its committed prefix and every prefix the request
agrees with, `hkeep`: a truncation to a length past the first conflict, `maybeAppend`'s new log): each
committed prefix, kept from a term `t ≤` the request's with its certificate, agrees with the request
(`commitCert_app`, with the receiver's raft facts of the request and the vote table), so `r` still holds
it; no other server changes. -/
theorem quorumLogF_appLog (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (r : Etcdraft.ID)
    (m : Etcdraft.Msg) (hterm : m.term = (σ.s r).currentTerm) (hsrv : σ'.server = σ.server)
    (hs : ∀ k, k ≠ r → σ'.s k = σ.s k) (hT : (σ'.s r).currentTerm = (σ.s r).currentTerm)
    (hcm : committedL σ' r = committedL σ r)
    (hkeep : ∀ P, P <+: (σ.s r).log → AppAgrees P m → P <+: (σ'.s r).log)
    (src T : w64) (bL : entryID) (l fp ents : List EntryM) (idx lt : w64)
    (hTm : m.term = uint.Z T) (hin : plogTermAt bL l idx = some lt)
    (hsl : ents <+: plogFrom bL l (idx + W64 1)) (hidx1 : uint.Z idx + 1 < 2 ^ 64)
    (hidx : m.prevLogIndex = uint.Z idx) (hents : m.entries = logAbs C C.length (uint.nat idx + 1) ents) :
    votesTbl (GF := GF) γ ∗ QuorumLogF γ C σ ∗ leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp ⊢
      votesTbl γ ∗ QuorumLogF γ C σ' := by
  have hcmA : ∀ k, committedL σ' k = committedL σ k := by
    intro k; by_cases hk : k = r
    · subst hk; exact hcm
    · unfold committedL; rw [hs k hk]
  iintro ⟨Htbl, #Hq, #Hp, #Hf⟩
  iunfold QuorumLogF at Hq
  ihave #HA : □ ∀ i, ⌜i ∈ σ.server⌝ → ((∃ t, ⌜KeptFrom σ (committedL σ i) t⌝ ∗
      CommitCert γ C (committedL σ i) t) ∗ leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp) $$ []
  · imodintro
    iintro %i %hi
    iframe Hp Hf
    iapply Hq $$ %i %hi
  icases votesTbl_forall_list γ
      (fun i => iprop((∃ t, ⌜KeptFrom σ (committedL σ i) t⌝ ∗ CommitCert γ C (committedL σ i) t) ∗
        leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp))
      (fun i => iprop(∃ t, ⌜KeptFrom σ (committedL σ i) t ∧ (t ≤ m.term → AppAgrees (committedL σ i) m)⌝ ∗
        CommitCert γ C (committedL σ i) t))
      (fun i => by
        iintro ⟨Htbl, ⟨%t, %hK, #Hc⟩, #Hp, #Hf⟩
        by_cases ht : t ≤ m.term
        · icases keep_pure (commitCert_app γ C (committedL σ i) t src T bL l fp ents idx lt m
              (by rw [← hTm]; exact ht) hin hsl hidx1 hidx hents) $$ [$Htbl $Hc $Hp $Hf]
            with ⟨⟨Htbl, -⟩, %hag⟩
          iframe Htbl
          iexists t
          iframe Hc
          ipureintro
          exact ⟨hK, fun _ => hag⟩
        · iframe Htbl
          iexists t
          iframe Hc
          ipureintro
          exact ⟨hK, fun h => absurd h ht⟩)
      σ.server $$ [$Htbl $HA] with ⟨Htbl, #Hb⟩
  iframe Htbl
  iunfold QuorumLogF
  imodintro
  iintro %i %hi
  rw [hsrv] at hi
  ihave Hi := Hb $$ %i %hi
  icases Hi with ⟨%t, %hK, #Hc⟩
  iexists t
  rw [hcmA i]
  iframe Hc
  ipureintro
  refine keptFrom_of hsrv ?_ hK.1
  intro k _ hpk htk
  by_cases hkr : k = r
  · subst hkr
    refine ⟨hkeep _ hpk (hK.2 (by rw [hterm]; exact htk)), by rw [hT]; exact htk⟩
  · rw [hs k hkr]; exact ⟨hpk, htk⟩

/-- **The facts at an accepted append request's intermediate state** (`appMid`): the receiver `i`, a
follower of the request's term, with raft's log `L`, its log replaced by `L'` (and the leader
adopted), the bags unchanged. `L'` keeps the committed prefix (`htk`), its entries are the old log's or
the request's (`hent`, for `SpecInv`), and it keeps every prefix the request agrees with (`hkeep`, for
`QuorumLogF`, with the receiver's raft facts of the request); its records are raft's (`logRecs`). -/
theorem simFx_appLog (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (i : w64) (ma : Etcdraft.Msg)
    (L L' : List EntryM) (j : Etcdraft.ID)
    (hsrv : σ.server = confAbs C) (hiC : i ∈ C) (hdst : ma.dest = idAbs i)
    (hf : (σ.s (idAbs i)).state = Etcdraft.follower)
    (hterm : ma.term = (σ.s (idAbs i)).currentTerm) (hmem : ma ∈ σ.messages.domain)
    (hlog : (σ.s (idAbs i)).log = logAbs C C.length 1 L) (hbL : BootTerms C.length 1 L) (hwL : PlogWf base0 L)
    (hbL' : BootTerms C.length 1 L') (hwr' : PlogWfR base0 L') (hln' : L'.length < 2 ^ 63)
    (hcl' : (σ.s (idAbs i)).commitIndex ≤ L'.length)
    (htk : L'.take (σ.s (idAbs i)).commitIndex.toNat = L.take (σ.s (idAbs i)).commitIndex.toNat)
    (hent : ∀ k e, (logAbs C C.length 1 L')[k]? = some e → (logAbs C C.length 1 L)[k]? = some e ∨
        ∃ q, ma.entries[q]? = some e ∧ k = ma.prevLogIndex.toNat + q)
    (hkeep : ∀ P, P <+: logAbs C C.length 1 L → AppAgrees P ma → P <+: logAbs C C.length 1 L')
    (src T : w64) (bL : entryID) (l fp ents : List EntryM) (idx lt : w64)
    (hTm : ma.term = uint.Z T) (hin : plogTermAt bL l idx = some lt)
    (hsl : ents <+: plogFrom bL l (idx + W64 1)) (hidx1 : uint.Z idx + 1 < 2 ^ 64)
    (hidx : ma.prevLogIndex = uint.Z idx) (hents : ma.entries = logAbs C C.length (uint.nat idx + 1) ents) :
    votesTbl (GF := GF) γ ∗ simFx γ C σ ∗ logRecs γ base0 L ∗ logRecs γ base0 L' ∗
        leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp ⊢
      votesTbl γ ∗ simFx γ C (withNode σ (idAbs i)
        { σ.s (idAbs i) with log := logAbs C C.length 1 L', lead := j } _root_.id _root_.id) := by
  obtain ⟨W, hW⟩ : ∃ W, W = withNode σ (idAbs i)
      { σ.s (idAbs i) with log := logAbs C C.length 1 L', lead := j } _root_.id _root_.id := ⟨_, rfl⟩
  rw [← hW]
  have hWs : ∀ k, W.s k = if k = idAbs i then
      { σ.s (idAbs i) with log := logAbs C C.length 1 L', lead := j } else σ.s k := by
    intro k; rw [hW]; rfl
  have hWo : ∀ k, k ≠ idAbs i → W.s k = σ.s k := by
    intro k hk; rw [hWs, ite_eq_right_of_eq_false _ _ (eq_false hk)]
  have hWi : W.s (idAbs i) = { σ.s (idAbs i) with log := logAbs C C.length 1 L', lead := j } := by
    rw [hWs, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  have hWsrv : W.server = σ.server := by rw [hW]; rfl
  have hWm : W.messages = σ.messages := by rw [hW]; rfl
  have hWp : W.pendingMessages = σ.pendingMessages := by rw [hW]; rfl
  have hiS : idAbs i ∈ σ.server := by rw [hsrv, mem_confAbs]; exact hiC
  iintro ⟨Htbl, Hfx, #HL, #HL', #Hp, #Hf⟩
  iunfold simFx at Hfx
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hpure⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hpure
  -- the receiver's facts
  ihave #Hal1 : allFacts γ C W $$ []
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %k %hk
    by_cases hki : idAbs k = idAbs i
    · ihave #Hk := Hal $$ %k %hk
      rw [hki, hWi]
      iunfold srvFacts at Hk
      icases Hk with ⟨%es, %pend, %Hpk, #Hrec, #Hcm, -, #Hci⟩
      obtain ⟨hlg, hbt, hwr, hln, hc0, hcl, ht0, ht1, hpn, hpt⟩ := Hpk
      have hpend : pend = [] := hpn (by rw [hf]; exact TraceSpecInv.follower_ne_leader)
      subst hpend
      simp only [List.append_nil] at hlg hbt hwr hln
      have hwe : PlogWf base0 es := PlogWfR_wf _ _ hwr (by unfold plogLastIndexZ; rw [base0_index]; omega)
      icases log_eq_of_abs γ C es L hbt hbL (hlg.symm.trans hlog) hwe hwL hln $$ [$Hrec $HL] with %HeL
      subst HeL
      have hwL' : PlogWf base0 L' := PlogWfR_wf _ _ hwr' (by unfold plogLastIndexZ; rw [base0_index]; omega)
      have hcW : uint.Z (W64 (σ.s (idAbs i)).commitIndex) = (σ.s (idAbs i)).commitIndex := by word
      have hS : (plogTermAt base0 es (W64 (σ.s (idAbs i)).commitIndex)).isSome :=
        plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by
          unfold plogLastIndexZ; rw [base0_index, hcW]; simp; omega⟩
      have hE : plogTermAt base0 L' (W64 (σ.s (idAbs i)).commitIndex) =
          plogTermAt base0 es (W64 (σ.s (idAbs i)).commitIndex) := by
        rw [← plogTermAt_take_full L' (σ.s (idAbs i)).commitIndex.toNat _ (by rw [hcW]; omega), htk,
          plogTermAt_take_full es _ _ (by rw [hcW]; omega)]
      iunfold srvFacts
      iexists L', []
      simp only [List.append_nil]
      have hst : ({ σ.s (idAbs i) with log := logAbs C C.length 1 L', lead := j } : Etcdraft.Server).state ≠
          Etcdraft.leader := by
        simp only [hf]; exact TraceSpecInv.follower_ne_leader
      simp only [hst, ↓reduceIte]
      iframe HL'
      isplitr
      · ipureintro
        exact ⟨trivial, hbL', hwr', by omega, hc0, hcl', ht0, ht1, fun _ => trivial, fun e he => by simp at he⟩
      isplitr
      · rw [htk]; iexact Hcm
      isplitr
      · itrivial
      · iapply commitIn_move γ es L' _ _ _ (Int.le_refl _) hwe hwL' hS hE $$ Hrec HL' Hci
    · rw [hWo _ hki]
      iapply Hal $$ %k %hk
  -- `SpecInv`: a follower's new log of entries of the old log or of the request
  have hupd : W = σ.upd (idAbs i) (fun v => { v with log := logAbs C C.length 1 L', lead := j }) := by
    rw [hW, upd_eq_withNode]
  have hmm : ma ∈ TraceSpecInv.msgs σ := List.mem_append_left _ hmem
  have hsi' : TraceSpecInv.SpecInv W := by
    rw [hupd]
    apply TraceSpecInv.specInv_upd_followerLog hsi hf rfl rfl rfl rfl rfl rfl rfl
    · intro k e he l hl hll ht
      rcases hent k e he with he | ⟨q, hq, rfl⟩
      · rw [← hlog] at he
        exact (hsi.1 l hl hll).1 (idAbs i) hiS k e he ht
      · exact (hsi.1 l hl hll).2 ma hmm q e hq ht
    · intro e he
      obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp he
      rcases hent k e (by rw [List.getElem?_eq_getElem hk, hke]) with he' | ⟨q, hq, -⟩
      · rw [← hlog] at he'
        exact hsi.logTermsLe.1 (idAbs i) hiS e (List.mem_of_getElem? he')
      · rw [← hterm]; exact hsi.logTermsLe.2 ma hmm e (List.mem_of_getElem? hq)
  -- `QuorumLogF`
  have hcmL : committedL W (idAbs i) = committedL σ (idAbs i) := by
    unfold committedL; rw [hWi]; simp only
    rw [hlog, logAbs_take, logAbs_take, htk]
  icases quorumLogF_appLog γ C σ W (idAbs i) ma hterm hWsrv hWo
      (by rw [hWi]) hcmL
      (fun P hP hag => by rw [hWi]; simp only; rw [hlog] at hP; exact hkeep P hP hag)
      src T bL l fp ents idx lt hTm hin hsl hidx1 hidx hents $$ [$Htbl $Hq $Hp $Hf] with ⟨Htbl, #Hq'⟩
  iframe Htbl
  iunfold simFx
  iframe Hal1 Hq'
  isplitl
  · imodintro
    iintro %x %hx
    rw [hWm, hWp] at hx
    iapply Hmf; ipureintro; exact hx
  ipureintro
  refine ⟨hsi', ?_, ?_, ?_⟩
  · intro ln m1 m2 h1 h2 r1 r2
    rw [hWm, hWp] at h1 h2
    exact hu ln m1 m2 h1 h2 r1 r2
  · intro x hx; rw [hWm, hWp] at hx; exact hsh x hx
  · intro m hm hty' k hk hlk htk' hs k' e he
    rw [hWm, hWp] at hm
    rw [hWsrv] at hk
    have hkr : k ≠ idAbs i := by
      rintro rfl; rw [hWi] at hlk; simp only [hf] at hlk; exact TraceSpecInv.follower_ne_leader hlk
    rw [hWo k hkr] at hlk htk' ⊢
    exact has m hm hty' k hk hlk htk' hs k' e he


/-- **The facts after `AppendEntriesAlreadyDone` of an accepted append request** (the line's last
round, from the state with the new log `L`): the commit index raised to `cc = min(m.commitIndex, p + k)`
at most, the leader adopted, the success response pending. The raised commit index's certificate and
committed prefix are raft's (`ownRaftGhost_appAccFacts`), `QuorumLogF` by the sender's committed prefix
(`committedL_raise_prefix`, as the heartbeat's `simFx_hb`). -/
theorem simFx_appDone (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (ma : Etcdraft.Msg) (L ents : List EntryM)
    (i : w64) (p : Nat) (hsrv : σ.server = confAbs C) (hiC : i ∈ C) (hdst : ma.dest = idAbs i)
    (hf : (σ.s ma.dest).state = Etcdraft.follower) (hty : ma.type = .appendEntriesRequest)
    (hterm : ma.term = (σ.s ma.dest).currentTerm) (hsub : ma.subtype = "app")
    (hmem : ma ∈ σ.messages.domain)
    (hlog : (σ.s ma.dest).log = logAbs C C.length 1 L) (hbL : BootTerms C.length 1 L) (hwL : PlogWf base0 L)
    (hents : ma.entries = logAbs C C.length (p + 1) ents) (hprev : ma.prevLogIndex = p)
    (hq : p + ents.length ≤ L.length) (hc : (σ.s ma.dest).commitIndex < (p : Int) + 1)
    (hbe : BootTerms C.length (p + 1) ents)
    (hnc : ∀ k e, ents[k]? = some e → p + k < L.length → (L[p + k]?).map EntryM.Term' = some e.Term')
    (cc : Int) (hcc : cc = max (σ.s ma.dest).commitIndex (min ma.commitIndex ((p : Int) + ents.length)))
    (hccl : cc ≤ L.length) :
    simFx (GF := GF) γ C σ ∗ logRecs γ base0 L ∗
      commitIn γ L (W64 cc) (W64 (σ.s ma.dest).currentTerm) ∗ isCommitted γ (L.take cc.toNat) ⊢
      simFx γ C (withNode σ ma.dest (doneSrv (σ.s ma.dest) (σ.s ma.dest).log ma.source
          (min ma.commitIndex ((p : Int) + ents.length)))
        (fun b => b.without ma) (fun b => b.with (doneResp (σ.s ma.dest) ma p ents.length))) := by
  obtain ⟨W, hW⟩ : ∃ W, W = withNode σ ma.dest (doneSrv (σ.s ma.dest) (σ.s ma.dest).log ma.source
      (min ma.commitIndex ((p : Int) + ents.length)))
      (fun b => b.without ma) (fun b => b.with (doneResp (σ.s ma.dest) ma p ents.length)) := ⟨_, rfl⟩
  rw [← hW]
  have hWs : ∀ k, W.s k = if k = ma.dest then doneSrv (σ.s ma.dest) (σ.s ma.dest).log ma.source
      (min ma.commitIndex ((p : Int) + ents.length)) else σ.s k := by
    intro k; rw [hW]; rfl
  have hF : ∀ k, (W.s k).log = (σ.s k).log ∧ (W.s k).currentTerm = (σ.s k).currentTerm ∧
      (W.s k).state = (σ.s k).state ∧ (W.s k).config = (σ.s k).config ∧
      (W.s k).commitIndex = (if k = ma.dest then max (σ.s k).commitIndex
        (min ma.commitIndex ((p : Int) + ents.length)) else (σ.s k).commitIndex) := by
    intro k; rw [hWs]
    split
    · rename_i hk; subst hk; simp [doneSrv]
    · simp_all
  have hsub' : ∀ x ∈ W.messages.domain ++ W.pendingMessages.domain,
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain ∨ x = doneResp (σ.s ma.dest) ma p ents.length := by
    intro x hx
    have hx' : x ∈ ((σ.discard ma).send (doneResp (σ.s ma.dest) ma p ents.length)).messages.domain ++
        ((σ.discard ma).send (doneResp (σ.s ma.dest) ma p ents.length)).pendingMessages.domain := by
      rw [hW] at hx; exact hx
    rcases TraceSpecInv.mem_msgs_send _ _ x hx' with hx | rfl
    · left
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
      · exact List.mem_append_right _ hx
    · right; rfl
  have hWsrv : W.server = σ.server := by rw [hW]; rfl
  iintro ⟨Hfx, #HL, #Hci', #Hcm'⟩
  iunfold simFx at Hfx
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
  -- the receiver's facts
  ihave #Hal1 : allFacts γ C W $$ []
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %k %hk
    by_cases hki : idAbs k = ma.dest
    · ihave #Hk := Hal $$ %k %hk
      rw [hki]
      simp only [hWs, ↓reduceIte]
      iunfold srvFacts at Hk
      icases Hk with ⟨%es, %pend, %Hpk, #Hrec, -, -, -⟩
      obtain ⟨hlg, hbt, hwr, hln, hc0, hcl, ht0, ht1, hpn, hpt⟩ := Hpk
      have hpend : pend = [] := hpn (by rw [hf]; exact TraceSpecInv.follower_ne_leader)
      subst hpend
      simp only [List.append_nil] at hlg hbt hwr hln
      have hwe : PlogWf base0 es := PlogWfR_wf _ _ hwr (by unfold plogLastIndexZ; rw [base0_index]; omega)
      icases log_eq_of_abs γ C es L hbt hbL (hlg.symm.trans hlog) hwe hwL hln $$ [$Hrec $HL] with %HeL
      subst HeL
      iunfold srvFacts
      iexists es, []
      simp only [List.append_nil]
      have hst : (doneSrv (σ.s ma.dest) (σ.s ma.dest).log ma.source
          (min ma.commitIndex ((p : Int) + ents.length))).state ≠ Etcdraft.leader := by
        simp only [doneSrv, hf]; exact TraceSpecInv.follower_ne_leader
      simp only [hst, ↓reduceIte]
      have hmx : (doneSrv (σ.s ma.dest) (σ.s ma.dest).log ma.source
          (min ma.commitIndex ((p : Int) + ents.length))).commitIndex = cc := by
        simp only [doneSrv]; rw [hcc]
      have hlx : (doneSrv (σ.s ma.dest) (σ.s ma.dest).log ma.source
          (min ma.commitIndex ((p : Int) + ents.length))).log = logAbs C C.length 1 es := by
        simp only [doneSrv]; exact hlg
      have htx : (doneSrv (σ.s ma.dest) (σ.s ma.dest).log ma.source
          (min ma.commitIndex ((p : Int) + ents.length))).currentTerm = (σ.s ma.dest).currentTerm := by
        simp only [doneSrv]
      rw [hmx, htx, hlx]
      iframe HL Hci' Hcm'
      ipureintro
      exact ⟨rfl, hbt, hwr, hln, by rw [hcc]; omega, hccl, ht0, ht1, fun _ => trivial, fun e he => by simp at he⟩
    · rw [hWs, ite_eq_right_of_eq_false _ _ (eq_false hki)]
      iapply Hal $$ %k %hk
  -- the pure facts
  have hmmem : ma ∈ σ.messages.domain ++ σ.pendingMessages.domain := List.mem_append_left _ hmem
  obtain ⟨hsrcS, hcS⟩ := hsi.reqCommitC ma hmmem hty
  have hiS : ma.dest ∈ σ.server := by rw [hdst, hsrv, mem_confAbs]; exact hiC
  have hstep := alreadyDone_any σ ma.dest ma.source ma C C.length p L ents hlog hents hprev hq hc
    (by rw [hsub]; decide) hbL hbe hnc
  have hsiX := TraceSpecInv.specInv_appendEntriesAlreadyDone hsi hiS hmem rfl hty hterm hf
    (by rw [hprev]) hstep
  have hsi' : TraceSpecInv.SpecInv W := by
    have h2 := TraceSpecInv.specInv_upd_frame (i := ma.dest) (f := fun w => { w with lead := ma.source }) hsiX
      rfl rfl rfl rfl rfl rfl rfl rfl
    have h3 : TraceSpecInv.SpecInv (withLead ((σ.commitTo ma.dest (min ma.commitIndex ((p : Int) + ents.length))).reply
        { type := .appendEntriesResponse, subtype := ma.subtype, term := (σ.s ma.dest).currentTerm,
          success := true, matchIndex := (p : Int) + ents.length, source := ma.dest, dest := ma.source } ma)
        ma.dest ma.source) := h2
    unfold Etcdraft.State.commitTo at h3
    rw [withLead_reply_upd] at h3
    rw [hW]
    exact h3
  icases allFacts_logInv γ C W (by rw [hWsrv, hsrv]) $$ Hal1 with %HlogInv
  icases allFacts_commitOk γ C σ hsrv $$ Hal with %Hco
  have hcmp := HlogInv ma.dest (by rw [hWsrv]; exact hiS) ma.source (by rw [hWsrv]; exact hsrcS)
  have hPW : ∀ k ∈ σ.server, ∃ k' ∈ σ.server, committedL W k <+: committedL σ k' := by
    intro k hk
    by_cases hkd : k = ma.dest
    · subst hkd
      rcases committedL_raise_prefix (σ := σ) (W := W) (src := ma.source)
          (c := min ma.commitIndex ((p : Int) + ents.length))
          (hF _).1 (by rw [(hF _).2.2.2.2, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
          (fun k hk => by unfold committedL; rw [(hF k).1, (hF k).2.2.2.2, ite_eq_right_of_eq_false _ _ (eq_false hk)])
          (Int.le_trans (Int.min_le_left _ _) hcS) (Hco ma.source hsrcS).2 hcmp with h | h
      · exact ⟨_, hk, h⟩
      · exact ⟨ma.source, hsrcS, h⟩
    · exact ⟨k, hk, by unfold committedL; rw [(hF k).1, (hF k).2.2.2.2, ite_eq_right_of_eq_false _ _ (eq_false hkd)]; exact List.prefix_refl _⟩
  -- uniqueness and shape: after the discard, the response sent
  have hxq : (doneResp (σ.s ma.dest) ma p ents.length).type ≠ .appendEntriesRequest := by simp [doneResp]
  have hx0 : canonMsg (doneResp (σ.s ma.dest) ma p ents.length) = doneResp (σ.s ma.dest) ma p ents.length := by
    unfold doneResp canonMsg; simp [hsub]
  have hud : MsgsUniq (σ.discard ma) := msgsUniq_mono (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx) hu
  have hshd : MsgsShape (σ.discard ma) := fun x hx => hsh x (by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx)
  obtain ⟨hu', hsh'⟩ := msgsUniq_send_canon (σ.discard ma) _ hud hshd hx0
    (fun y _ => ContentLogged.pinned (fun h => absurd h hxq) y)
  iunfold simFx
  iframe Hal1
  isplitl
  · imodintro
    iintro %x %hx
    rcases hsub' x hx with hx | rfl
    · iapply Hmf; ipureintro; exact hx
    · iapply msgFacts_plain γ C _ hxq rfl
  isplitl
  · iapply quorumLogF_mono γ C σ W hWsrv hPW ?_ $$ Hq
    intro P t h
    exact keptFrom_congr hWsrv (fun k => (hF k).1) (fun k => by rw [(hF k).2.1]; exact Int.le_refl _) h
  ipureintro
  refine ⟨hsi', by rw [hW]; exact hu', by rw [hW]; exact hsh', ?_⟩
  intro m hm hty' k hk hlk htk hs k' e he
  have hk' : k ∈ σ.server := by rw [hWsrv] at hk; exact hk
  rcases hsub' m hm with hm | rfl
  · rw [(hF k).1]
    rw [(hF k).2.2.1] at hlk; rw [(hF k).2.1] at htk
    exact has m hm hty' k hk' hlk htk hs k' e he
  · exact absurd hty' hxq


/-- **A log with records has a record at its last index** (`lastRec`: `0`, or its last entry's). -/
theorem logRecs_lastRec (γ : RaftNames) (F : List EntryM) (hw : PlogWf base0 F) (hl : F.length < 2 ^ 63) :
    logRecs (GF := GF) γ base0 F ⊢ lastRec γ (F.length : Int) := by
  iintro #H
  unfold lastRec
  rcases Nat.eq_zero_or_pos F.length with h0 | hpos
  · ileft; ipureintro; rw [h0]; rfl
  iright
  obtain ⟨e, he⟩ : ∃ e, F[F.length - 1]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hi := hw _ e he
  rw [base0_index] at hi
  icases logRecs_isEntry γ base0 F _ e he (by rw [base0_index]; omega) $$ H with ⟨%pt, #He⟩
  iexists e
  isplitr
  · iunfold isEntry; iexists pt; iexact He
  · ipureintro; rw [hi]; push_cast; omega

/-- **Raft's commit index covers the bootstrap log** (`ownLogGhost_boot`); the ghost state unchanged. -/
theorem ownRaftGhost_bootLe (γ : RaftNames) (id : w64) (s : PState) {md : Bool} :
    ownRaftGhost (GF := GF) γ id s md ⊢ ownRaftGhost γ id s md ∗ ⌜(γ.reBoot.length : Int) ≤ uint.Z s.commit⌝ := by
  iintro Hg
  iunfold ownRaftGhost at Hg
  icases Hg with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  icases persistent_entails_right (wand_entails (ownLogGhost_boot (GF := GF) γ id s kl (virt V πc))) $$ Hlg
    with ⟨⟨%Hbt, -⟩, Hlg⟩
  isplitl
  · iunfold ownRaftGhost
    iexists γs, V, πc, kl
    iframe Hslot Hvirt Hpend Hout Htally Hlead Hlg Hlcm Hrd
    ipureintro; exact ⟨Hsname, Hfresh, Hidnz, Hhist, Hlead_ok, Hfollower_votes, Hrole_ok, Hmode⟩
  · ipureintro; exact Hbt.1

/-- **The new log's length is within the trace's number bound** (its last index's time receipt,
`lastRec_receipt`, below the receipts' bound past the bootstrap log). -/
theorem logRecs_traceBound (γ : RaftNames) (F : List EntryM) (hw : PlogWf base0 F) (hl : F.length < 2 ^ 63)
    (Hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    logRecs (GF := GF) γ base0 F ⊢ |==> ⌜(F.length : Int) < traceNumBound⌝ := by
  iintro #H
  ihave #Hlr := logRecs_lastRec γ F hw hl $$ H
  imod lastRec_receipt γ _ $$ Hlr with #Hrc
  ihave %Hlt := preceipt_lt _ $$ Hrc
  imodintro
  ipureintro
  have hb : traceNumBound = 2 ^ 61 := rfl
  omega

/-- The new log's facts the line's states need (`maybeAppend`'s new log `es'` from the log `L` at the
batch `ents` after `p`, the commit index `c` at most `p`): its bootstrap terms, its committed prefix
the old one's, the batch in it, its length past `lastnewi`. -/
theorem newLog_pure (C : List w64) (L ents es' : List EntryM) (p : Nat) (lt lastnewi : w64) (c : Nat)
    (hbL : BootTerms C.length 1 L) (hbe : BootTerms C.length (p + 1) ents)
    (hwf : ∀ (k : Nat) (e : EntryM), ents[k]? = some e → uint.Z e.Index' = (p : Int) + k + 1)
    (hp : p < 2 ^ 64) (hnw : (p : Int) + ents.length + 1 < 2 ^ 64) (hcp : c ≤ p)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) L (entryID.mk lt (W64 p)) ents = some (lastnewi, es')) :
    BootTerms C.length 1 es' ∧ es'.take c = L.take c ∧ p + ents.length ≤ es'.length ∧
      (∀ k e, ents[k]? = some e → p + k < es'.length → (es'[p + k]?).map EntryM.Term' = some e.Term') ∧
      uint.Z lastnewi = (p : Int) + ents.length := by
  obtain ⟨hpl, hli, hcase⟩ := maybeAppend_spec L ents es' p lt lastnewi hwf hp hnw happ
  rcases hcase with ⟨rfl, hq, hnc⟩ | ⟨d, hd, hpd, rfl, -, -, hbef, -⟩
  · exact ⟨hbL, rfl, hq, hnc, hli⟩
  refine ⟨bootTerms_truncAppend C.length p d L ents hpd hbL hbe, ?_, ?_, truncAppend_has L ents p d hpd hbef, hli⟩
  · rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left (by omega)]
  · simp; omega

/-- **The facts at every intermediate state of an accepted append request's line** (`appMid`, up to
the receiver's server: the log truncated to `k` entries past the first conflict, or the new log), the
receiver `i` a follower of the request's term with raft's log `L`; from `simFx_appLog` with the kept
prefixes (`prefix_take_of_conflict`, `prefix_newLog`). -/
theorem simFx_appAccMid (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (i : w64) (ma : Etcdraft.Msg)
    (L ents es' : List EntryM) (p : Nat) (lt lastnewi : w64) (j : Etcdraft.ID)
    (hsrv : σ.server = confAbs C) (hiC : i ∈ C) (hdst : ma.dest = idAbs i)
    (hf : (σ.s (idAbs i)).state = Etcdraft.follower)
    (hterm : ma.term = (σ.s (idAbs i)).currentTerm) (hmem : ma ∈ σ.messages.domain)
    (hlog : (σ.s (idAbs i)).log = logAbs C C.length 1 L) (hbL : BootTerms C.length 1 L)
    (hwr : PlogWfR base0 L) (hln : L.length < 2 ^ 63)
    (hcp : (σ.s (idAbs i)).commitIndex ≤ p) (hc0 : 0 ≤ (σ.s (idAbs i)).commitIndex)
    (hprev : ma.prevLogIndex = p) (hents : ma.entries = logAbs C C.length (p + 1) ents)
    (hbe : BootTerms C.length (p + 1) ents)
    (hwf : ∀ (k : Nat) (e : EntryM), ents[k]? = some e → uint.Z e.Index' = (p : Int) + k + 1)
    (hp : p < 2 ^ 64) (hnw : (p : Int) + ents.length + 1 < 2 ^ 64)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) L (entryID.mk lt (W64 p)) ents = some (lastnewi, es'))
    (hwr' : PlogWfR base0 es') (hln' : es'.length < 2 ^ 63)
    (src T : w64) (bL : entryID) (l fp ents0 : List EntryM) (idx lt0 : w64)
    (hTm : ma.term = uint.Z T) (hin : plogTermAt bL l idx = some lt0)
    (hsl : ents0 <+: plogFrom bL l (idx + W64 1)) (hidx1 : uint.Z idx + 1 < 2 ^ 64)
    (hidx : ma.prevLogIndex = uint.Z idx) (hents0 : ma.entries = logAbs C C.length (uint.nat idx + 1) ents0)
    (L' : List EntryM)
    (hL' : (∃ k, p ≤ k ∧ k < L.length ∧ ConflictBy ents L p k ∧ L' = L.take k) ∨ L' = es') :
    votesTbl (GF := GF) γ ∗ simFx γ C σ ∗ logRecs γ base0 L ∗ logRecs γ base0 es' ∗
        leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp ⊢
      votesTbl γ ∗ simFx γ C (withNode σ (idAbs i)
        { σ.s (idAbs i) with log := logAbs C C.length 1 L', lead := j } _root_.id _root_.id) := by
  have hwL : PlogWf base0 L := PlogWfR_wf _ _ hwr (by unfold plogLastIndexZ; rw [base0_index]; omega)
  have hcn : (σ.s (idAbs i)).commitIndex.toNat ≤ p := by omega
  obtain ⟨hbN, htkN, hqN, -, -⟩ := newLog_pure C L ents es' p lt lastnewi _ hbL hbe hwf hp hnw hcn happ
  iintro ⟨Htbl, Hfx, #HL, #HN, #Hp, #Hf⟩
  rcases hL' with ⟨k, hpk, hkl, hcf, rfl⟩ | rfl
  · ihave #HLk := logRecs_take γ L k $$ HL
    iapply simFx_appLog γ C σ i ma L (L.take k) j hsrv hiC hdst hf hterm hmem hlog hbL hwL (hbL.take k)
      (PlogWf_wfR _ _ (PlogWf_take _ _ _ hwL)) (by simp; omega) (by simp; omega)
      (by rw [List.take_take, Nat.min_eq_left (by omega)])
      (fun k' e he => .inl (takeLog_entries C L k k' e he))
      (fun P hP hag => prefix_take_of_conflict C P L ents p k ma hprev hents hbL hbe hP hag hcf)
      src T bL l fp ents0 idx lt0 hTm hin hsl hidx1 hidx hents0
    iframe Htbl Hfx HL HLk Hp Hf
  · iapply simFx_appLog γ C σ i ma L L' j hsrv hiC hdst hf hterm hmem hlog hbL hwL hbN hwr' hln'
      (by omega) htkN (newLog_entries C L ents L' p lt lastnewi ma hprev hents hwf hp hnw happ)
      (fun P hP hag => prefix_newLog C P L ents L' p lt lastnewi ma hprev hents hbL hbe hwf hp hnw happ hP hag)
      src T bL l fp ents0 idx lt0 hTm hin hsl hidx1 hidx hents0
    iframe Htbl Hfx HL HN Hp Hf

/-- **The facts at the end of an accepted append request's line** (`doneSt` over the new log, as a
node update of the line's first state): `simFx_appLog` to the new log, then `simFx_appDone`. -/
theorem simFx_appAccEnd (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (i : w64) (ma : Etcdraft.Msg)
    (L ents es' : List EntryM) (p : Nat) (lt lastnewi : w64)
    (hsrv : σ.server = confAbs C) (hiC : i ∈ C) (hdst : ma.dest = idAbs i)
    (hf : (σ.s (idAbs i)).state = Etcdraft.follower) (hty : ma.type = .appendEntriesRequest)
    (hterm : ma.term = (σ.s (idAbs i)).currentTerm) (hsub : ma.subtype = "app") (hmem : ma ∈ σ.messages.domain)
    (hlog : (σ.s (idAbs i)).log = logAbs C C.length 1 L) (hbL : BootTerms C.length 1 L)
    (hwr : PlogWfR base0 L) (hln : L.length < 2 ^ 63)
    (hcp : (σ.s (idAbs i)).commitIndex ≤ p) (hc0 : 0 ≤ (σ.s (idAbs i)).commitIndex)
    (hprev : ma.prevLogIndex = p) (hents : ma.entries = logAbs C C.length (p + 1) ents)
    (hbe : BootTerms C.length (p + 1) ents)
    (hwf : ∀ (k : Nat) (e : EntryM), ents[k]? = some e → uint.Z e.Index' = (p : Int) + k + 1)
    (hp : p < 2 ^ 64) (hnw : (p : Int) + ents.length + 1 < 2 ^ 64)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) L (entryID.mk lt (W64 p)) ents = some (lastnewi, es'))
    (hwr' : PlogWfR base0 es') (hln' : es'.length < 2 ^ 63)
    (src T : w64) (bL : entryID) (l fp ents0 : List EntryM) (idx lt0 : w64)
    (hTm : ma.term = uint.Z T) (hin : plogTermAt bL l idx = some lt0)
    (hsl : ents0 <+: plogFrom bL l (idx + W64 1)) (hidx1 : uint.Z idx + 1 < 2 ^ 64)
    (hidx : ma.prevLogIndex = uint.Z idx) (hents0 : ma.entries = logAbs C C.length (uint.nat idx + 1) ents0)
    (cc : Int) (hcc : cc = max (σ.s (idAbs i)).commitIndex (min ma.commitIndex ((p : Int) + ents.length)))
    (hccl : cc ≤ es'.length) :
    votesTbl (GF := GF) γ ∗ simFx γ C σ ∗ logRecs γ base0 L ∗ logRecs γ base0 es' ∗
        leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp ∗
        commitIn γ es' (W64 cc) (W64 (σ.s (idAbs i)).currentTerm) ∗ isCommitted γ (es'.take cc.toNat) ⊢
      votesTbl γ ∗ simFx γ C (withNode σ (idAbs i)
        (doneSrv (σ.s (idAbs i)) (logAbs C C.length 1 es') ma.source (min ma.commitIndex ((p : Int) + ents.length)))
        (fun b => b.without ma) (fun b => b.with (doneResp (σ.s (idAbs i)) ma p ents.length))) := by
  have hwN : PlogWf base0 es' := PlogWfR_wf _ _ hwr' (by unfold plogLastIndexZ; rw [base0_index]; omega)
  have hcn : (σ.s (idAbs i)).commitIndex.toNat ≤ p := by omega
  obtain ⟨hbN, -, hqN, hncN, -⟩ := newLog_pure C L ents es' p lt lastnewi _ hbL hbe hwf hp hnw hcn happ
  iintro ⟨Htbl, Hfx, #HL, #HN, #Hp, #Hf, #Hci, #Hcm⟩
  icases simFx_appAccMid γ C σ i ma L ents es' p lt lastnewi ma.source hsrv hiC hdst hf hterm hmem hlog hbL hwr hln
      hcp hc0 hprev hents hbe hwf hp hnw happ hwr' hln' src T bL l fp ents0 idx lt0 hTm hin hsl hidx1 hidx hents0
      es' (.inr rfl) $$ [$Htbl $Hfx $HL $HN $Hp $Hf] with ⟨Htbl, #HA⟩
  iframe Htbl
  obtain ⟨v0, hv0⟩ : ∃ v0, v0 = ({ σ.s (idAbs i) with log := logAbs C C.length 1 es', lead := ma.source } :
      Etcdraft.Server) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = withNode σ (idAbs i) v0 _root_.id _root_.id := ⟨_, rfl⟩
  rw [← hv0, ← hA]
  have hAs : A.s ma.dest = v0 := by rw [hA, hdst]; exact withNode_s_self _ _ _ _ _
  have heq : withNode A ma.dest (doneSrv (A.s ma.dest) (A.s ma.dest).log ma.source
      (min ma.commitIndex ((p : Int) + ents.length))) (fun b => b.without ma)
      (fun b => b.with (doneResp (A.s ma.dest) ma p ents.length)) =
      withNode σ (idAbs i)
        (doneSrv (σ.s (idAbs i)) (logAbs C C.length 1 es') ma.source (min ma.commitIndex ((p : Int) + ents.length)))
        (fun b => b.without ma) (fun b => b.with (doneResp (σ.s (idAbs i)) ma p ents.length)) := by
    rw [hAs, hA, hdst, withNode_withNode, hv0]; rfl
  ihave #HD := simFx_appDone γ C A ma es' ents i p (by rw [hA]; exact hsrv) hiC hdst
    (by rw [hAs, hv0]; exact hf) hty (by rw [hAs, hv0]; exact hterm) hsub (by rw [hA]; exact hmem)
    (by rw [hAs, hv0]) hbN hwN hents hprev hqN
    (by rw [hAs, hv0]; simp only; omega) hbe hncN cc (by rw [hAs, hv0]; exact hcc) hccl $$ [$HA $HN]
  · rw [hAs, hv0]; iframe Hci Hcm
  rw [← heq]
  iexact HD
end fx
end EtcdGrove
end Perennial
