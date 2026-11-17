/-
Lean-first (no Rocq counterpart). **The leader case of the `confc` arm, excluded: the pure facts**
(2026-11-12, trace-check implementation step 2, `notes/trace-check-design.md` §3.4 items 2 and 4;
`notes/decisions.md`, "Implementation step 2 (path facts)").

- **Lemma (i), the bootstrap log prefix** (`bootPrefix_unapplied`, `hupCampaigns_applied_boot`): at a
  log whose first entries are the bootstrap log's configuration entries, committed past them, `hup`
  refuses to campaign (`hasUnappliedConfChanges`) while `applied` is short of them: a campaign happens
  only at `applied ≥ |boot|`.
- **G3 (a), no conf entry past the bootstrap log** (2026-11-12, `notes/trace-check-design.md`, "G3 (a)";
  `notes/decisions.md`, "G3 (a): no conf entry past the bootstrap log"; `isEntryR_trNoConf`,
  `logRecs_trNoConf`, `ownStepGhost_trNoConf`): at a traced cluster every conf entry of a log with
  records sits within the bootstrap log, since a leader's records carry `TrNoConf` (`ev2Rec`).
-/
module

public import Proof.go_etcd_io.raft.v3.SpecResults
public import Proof.go_etcd_io.raft.v3.StepGhostMode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris go_etcd_io.raft.v3

section lemmaI
variable [GooseExts]

/-- **Lemma (i)** (design §3.4 item 2): a log starting at index `1` (`prev` at index `0`) whose first
entries are configuration entries (`boot`), committed at least through them, has an unapplied
configuration entry while `applied` is short of them: the entry at index `applied + 1`. -/
theorem bootPrefix_unapplied (ls : LogState) (boot : List EntryM)
    (hprev : uint.Z ls.prev.index' = 0) (hpre : boot <+: ls.sents ++ ls.uents)
    (hconf : ∀ e ∈ boot, IsConfEnt e)
    (hcm : (boot.length : Int) ≤ uint.Z ls.committed) (hcmb : uint.Z ls.committed + 1 < 2 ^ 64)
    (hap : uint.Z ls.applied < boot.length) :
    ∃ e ∈ unappliedEnts ls, IsConfEnt e := by
  obtain ⟨t, ht⟩ := hpre
  have ha0 := uint_Z_nonneg ls.applied
  have hc1 : uint.Z (ls.committed + W64 1) = uint.Z ls.committed + 1 := by word
  have ha1 : uint.Z (ls.applied + W64 1) = uint.Z ls.applied + 1 := by word
  have hk : (uint.Z ls.applied).toNat < boot.length := by omega
  refine ⟨boot[(uint.Z ls.applied).toNat], ?_, hconf _ (List.getElem_mem hk)⟩
  unfold unappliedEnts scanRange plogFrom
  rw [hc1, ha1, hprev, ← ht]
  have hd : (uint.Z ls.applied + 1 - 0 - 1).toNat = (uint.Z ls.applied).toNat := by omega
  rw [hd]
  have hn : (uint.Z ls.committed + 1 - (uint.Z ls.applied + 1)).toNat =
      ((uint.Z ls.committed + 1 - (uint.Z ls.applied + 1)).toNat - 1) + 1 := by omega
  rw [hn, List.drop_append_of_le_length (by omega), List.drop_eq_getElem_cons hk, List.cons_append,
    List.take_succ_cons]
  exact List.mem_cons_self

/-- **Lemma (i) at `hup`'s guard** (design §3.4 item 2): a campaign (`HupCampaigns`) at such a log
happens only at `applied ≥ |boot|`, so clause 1(c) (`role ≠ follower → applied ≥ |γ.reBoot|`) holds from
the campaign on. -/
theorem hupCampaigns_applied_boot [GoGlobalContext] [GoSemanticsFunctions] {c : CfgM} {id : w64}
    {s : NState} (boot : List EntryM) (h : HupCampaigns c id s)
    (hprev : uint.Z s.logst.prev.index' = 0) (hpre : boot <+: s.logst.sents ++ s.logst.uents)
    (hconf : ∀ e ∈ boot, IsConfEnt e)
    (hcm : (boot.length : Int) ≤ uint.Z s.logst.committed) (hcmb : uint.Z s.logst.committed + 1 < 2 ^ 64) :
    (boot.length : Int) ≤ uint.Z s.logst.applied := by
  apply Int.not_lt.1
  intro hlt
  exact h.2.2.2 (bootPrefix_unapplied s.logst boot hprev hpre hconf hcm hcmb hlt)

end lemmaI

section g3
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF] [StorageModel GF]

open Iris.BI Iris.ProofMode

/-- **G3 (a), one record**: at a traced cluster an entry with a record is a conf entry only within
the bootstrap log: a leader's record carries `TrNoConf` (`ev2Rec`), a boot record is at an index
`≤ |γ.reBoot|` (`BootRec`). -/
theorem isEntryR_trNoConf (γ : RaftNames) (e : EntryM) (pt : w64) (htr : γ.reTrace ≠ none) :
    isEntryR (GF := GF) γ e pt ⊢ ⌜IsConfEnt e → uint.Z e.Index' ≤ γ.reBoot.length⌝ := by
  unfold isEntryR
  iintro (⟨%_, %_, %_, %_, %_, -, -, -, -, -, -, -, #Hev2⟩ | ⟨%Hb, -⟩)
  · unfold ev2Rec
    icases Hev2 with ⟨%Ht, -⟩
    ipureintro
    intro hc
    exact absurd hc (Ht htr)
  · ipureintro
    intro _
    have h1 := (List.getElem?_eq_some_iff.mp Hb.2.1).1
    have h2 := Hb.1
    omega

/-- **G3 (a), a log with records** (base `b`): at a traced cluster its `k`-th entry is a conf entry
only at an index `b.index + k + 1 ≤ |γ.reBoot|`. -/
theorem logRecs_trNoConf (γ : RaftNames) (b : entryID) (es : List EntryM)
    (htr : γ.reTrace ≠ none) (Hwf : PlogWf b es) :
    logRecs (GF := GF) γ b es ⊢ ⌜∀ (k : Nat) (e : EntryM), es[k]? = some e → IsConfEnt e →
      uint.Z b.index' + k + 1 ≤ γ.reBoot.length⌝ := by
  refine (BI.forall_intro fun k => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun e => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun Hk => ?_).trans BI.pure_forall.2
  have Hi := Hwf k e Hk
  have Hr := uint_Z_lt e.Index'
  unfold logRecs
  refine (BigSepL.bigSepL_lookup Hk).trans ?_
  have Hr' : uint.Z b.index' + (k : Int) + 1 < 2 ^ 64 := by push_cast at Hi; omega
  simp only [Hr', ↓reduceIte]
  iintro ⟨%pt, -, #He⟩
  ihave %H := isEntryR_trNoConf γ e pt htr $$ He
  ipureintro
  intro hc
  have := H hc
  push_cast at Hi
  omega

/-- **G3 (a) at a node** (what the leader exclusion reads, design §3.4 items 4(b) and 5): at a traced
cluster the `k`-th entry of the node's log (`sents ++ uents`, after `prev`) is a conf entry only at
an index `prev.index + k + 1 ≤ |γ.reBoot|` (at `prev = 0`: position `k < |γ.reBoot|`, lemma (i)'s
shape). -/
theorem ownStepGhost_trNoConf (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (htr : γ.reTrace ≠ none) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      ⌜∀ (k : Nat) (e : EntryM), (s.logst.sents ++ s.logst.uents)[k]? = some e → IsConfEnt e →
        uint.Z s.logst.prev.index' + k + 1 ≤ γ.reBoot.length⌝ ∗ ownStepGhost γ md c id s := by
  iintro Hgh
  iunfold ownStepGhost at Hgh
  icases Hgh with ⟨Hg, Hr⟩
  ihave ⟨%Hwf, #Hrecs⟩ := ownRaftGhost_logRecs γ id (toPState s) md.isDyn $$ Hg
  ihave %H := logRecs_trNoConf γ (toPState s).base (toPState s).log htr Hwf $$ Hrecs
  isplitr
  · ipureintro; exact H
  iunfold ownStepGhost
  iframe Hg Hr

end g3

end EtcdGrove
end Perennial
