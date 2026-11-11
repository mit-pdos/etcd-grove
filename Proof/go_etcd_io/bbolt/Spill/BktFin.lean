/-
`Bucket.spill`'s initial trees (U9i, `notes/bbolt-proof-plan.md`), part 1: **a finished subtree
from the base tree** (`fTree_base`). An entry of an unspilled branch whose child is not
materialized is a subtree of the committed tree (`treeOK`): an `sTree` from its first key (its
keys narrowed to it, `treeKeys_first`), over any page map that agrees on its pages.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.STreeBase
public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Spill.STreeAgree

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section fin
variable [GooseExts]

theorem pageKey_leaf {pg : List w8} (h : pageFlags pg = leafPageFlag) (i : Nat) :
    pageKey pg i = leafKey pg i := by
  unfold pageKey; rw [if_pos (by rw [h]; rfl)]

theorem pageKey_branch {pg : List w8} (h : pageFlags pg = branchPageFlag) (i : Nat) :
    pageKey pg i = branchKey pg i := by
  unfold pageKey; rw [if_neg (by rw [h]; decide)]

/-- **A tree's keys start at its first key**: the lower bound narrowed to it. -/
theorem treeKeys_first (P : Pages) (hwm : Nat) {id : Nat} {lo hi : Option (List w8)}
    (hk : treeKeys P id lo hi) :
    treeWF P hwm id → ∀ pg, P !! id = some pg → 0 < pageCount pg →
      treeKeys P id (some (pageKey pg 0)) hi := by
  induction hk with
  | leaf root pg lo hi hpg hl hk hb =>
    intro hw pg' hpg' _
    rw [hpg] at hpg'; cases hpg'
    have hwf : leafWF pg pg.length := by
      cases hw with
      | page _ pg2 _ _ hpg2 _ _ hpt =>
        rw [hpg] at hpg2; cases hpg2
        cases hpt with
        | leaf _ _ _ hwf _ => exact hwf
        | branch _ _ hb' _ _ => rw [hl] at hb'; cases hb'
    refine treeKeys.leaf root pg _ hi hpg hl (fun i hi' => ⟨?_, (hk i hi').2⟩) hb
    intro l hl'
    cases hl'
    rw [pageKey_leaf hl]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact go.goStringLt_irrefl _
    · exact go.goStringLt_asymm (hwf.2.2.2 0 i hpos hi')
  | branch root pg lo hi kind hpg hb h2 hk hc hs ih =>
    intro hw pg' hpg' _
    rw [hpg] at hpg'; cases hpg'
    obtain ⟨hwf, hch⟩ : branchWF pg pg.length hwm ∧
        ∀ i < pageCount pg, treeWF P hwm (branchPgid pg i) := by
      cases hw with
      | page _ pg2 _ _ hpg2 _ _ hpt =>
        rw [hpg] at hpg2; cases hpg2
        cases hpt with
        | leaf _ _ hl' _ _ => rw [hb] at hl'; cases hl'
        | branch _ _ _ hwf hch => exact ⟨hwf, hch⟩
    rw [pageKey_branch hb]
    refine treeKeys.branch root pg _ hi kind hpg hb h2
      (fun i hi' => ⟨?_, (hk i hi').2⟩) hc (fun i hi' => ?_)
    · intro l hl'
      cases hl'
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact go.goStringLt_irrefl _
      · exact go.goStringLt_asymm (hwf.2.2.2.2 0 i hpos hi')
    · by_cases i0 : i = 0
      · subst i0
        obtain ⟨cpg, hcpg, hcnt, -, hck⟩ := hc 0 hi'
        have := ih 0 hi' (hch 0 hi') cpg hcpg hcnt
        rw [hck] at this
        have e : childLo (some (branchKey pg 0)) (branchKey pg) 0 = some (branchKey pg 0) := by
          unfold childLo; rw [if_pos rfl]
        rw [e]; exact this
      · have e : childLo (some (branchKey pg 0)) (branchKey pg) i = childLo lo (branchKey pg) i := by
          unfold childLo; rw [if_neg i0, if_neg i0]
        rw [e]; exact hs i hi'

/-- **A finished subtree from the base tree**: page `id` of the committed tree `C` (`treeOK`), its
first key `k`, its keys within `[lo, hi)`, is an `fTree` from `k` over any page map `P` agreeing
with `C`'s on its pages, at any mark above `C`'s, of the height its page has (`pageHts`). -/
theorem fTree_base (C : CommitSt) (hok : treeOK C) {id : Nat} {pg : List w8}
    (hpg : C.pages !! id = some pg) (hcnt : 0 < pageCount pg) {k : List w8}
    (hkey : pageKey pg 0 = k) {lo hi : Option (List w8)} (hk : treeKeys C.pages id lo hi)
    (pht : Nat → Nat) (hpht : pageHts C.pages pht) (P : Pages) (hwm : Nat) (hh : C.hwm ≤ hwm)
    (hag : ∀ x ∈ subPages C.pages id, P !! x = C.pages !! x) :
    fTree P hwm id k hi (pht id) (subPages C.pages id) (treeEls P id) := by
  have ht : treeHas C.pages C.root id := by
    have e : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
    rw [treePages_lookup] at e
    split at e
    · assumption
    · cases e
  have hwf : treeWF C.pages C.hwm id := (sTree_base C hok ht hk pht hpht).wf
  have hk' := treeKeys_first C.pages C.hwm hk hwf pg hpg hcnt
  rw [hkey] at hk'
  have hs := sTree_base C hok ht hk' pht hpht
  refine ⟨sTree_agree hag hh hs, ⟨pg, ?_, hcnt, hkey⟩, rfl⟩
  rw [hag id (mem_subPages.2 (treeHas.root id pg hpg))]; exact hpg

end fin

end Spill

end bbolt
end EtcdGrove
end Perennial
