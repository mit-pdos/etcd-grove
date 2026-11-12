/-
Lean-first (no Rocq counterpart). **The leader case of the `confc` arm, excluded: the pure facts**
(2026-11-12, trace-check implementation step 2, `notes/trace-check-design.md` §3.4 items 2 and 4;
`notes/decisions.md`, "Implementation step 2 (path facts)").

- **Lemma (i), the bootstrap log prefix** (`bootPrefix_unapplied`, `hupCampaigns_applied_boot`): at a
  log whose first entries are the bootstrap log's configuration entries, committed past them, `hup`
  refuses to campaign (`hasUnappliedConfChanges`) while `applied` is short of them: a campaign happens
  only at `applied ≥ |boot|`.
-/
module

public import Proof.go_etcd_io.raft.v3.SpecResults

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

end EtcdGrove
end Perennial
