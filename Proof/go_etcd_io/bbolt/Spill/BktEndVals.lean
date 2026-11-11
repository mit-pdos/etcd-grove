/-
`Bucket.spill`'s root loop's end (U9x9, `notes/bbolt-proof-plan.md`): **the root's entries'
values at the end** (for `BktEndTree.end_rootTree`'s nested values `Sb` and owned slots). A leaf
entry of a bucket is a root entry (`rootEnts_of_allEnts`), an opened bucket's entry at the start
is (`entryIn_rootEnts`), and a skipped child's value is its entry's (`nil_val`: the root's keys
are distinct at the start).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndAsm

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section vals
variable [GooseExts]

/-- A bucket entry of the root's leaves is a root entry. -/
theorem rootEnts_of_allEnts {X : WX} {w : WEntry} (hw : w ∈ X.allEnts X.rl)
    (hb : isBktFlag w.flags) : (w.key, w.value) ∈ rootEnts X := by
  unfold WX.allEnts at hw
  obtain ⟨ws, hws, hw⟩ := List.mem_flatten.1 hw
  unfold rootEnts
  exact List.mem_flatMap.2 ⟨ws, hws, List.mem_filterMap.2 ⟨w, hw, by simp [hb]⟩⟩

/-- **An opened bucket's entry is a root entry** (`wOKR`). -/
theorem entryIn_rootEnts {X : WX} (hok : wOKR X) (hreach : liveReach X) {B : BRec}
    (hB : X.t.bs !! X.rl = some B) (h0 : B.ib.root' ≠ W64 0) (hrt : rtOK X X.rl)
    (h64 : ∀ p pg, X.v.pages !! p = some pg → p < 2 ^ 64) {k v : List w8}
    (h : entryIn X.v B k v) :
    ∃ we ∈ X.allEnts X.rl, we.key = k ∧ we.value = v ∧ (k, v) ∈ rootEnts X := by
  rcases h with ⟨l, r, w, hr, hl, hw, hkey, hbk, hval⟩ |
    ⟨c0, p, pg, i, hpr, hown, hpg, hfl, hi, hkey, hbf, hval⟩
  · have hwA := mem_allEnts_node hok hreach hrt hB h0 hr hl hw
    refine ⟨w, hwA, hkey, hval, ?_⟩
    rw [← hkey, ← hval]; exact rootEnts_of_allEnts hwA hbk
  · have hpA := mem_allEnts_page hok hreach hrt hB h64 hpr hown hpg hfl hi
    have hk : (pageW pg i).key = k := by simp [pageW, hfl, hkey]
    have hv : (pageW pg i).value = v := by simp [pageW, hfl, hval]
    refine ⟨_, hpA, hk, hv, ?_⟩
    have hbk : isBktFlag (pageW pg i).flags := by
      rw [pageW_leaf_eq hfl i]
      apply (isBkt_iff _).2
      have hl := leafFlags_lt pg i
      have e : (W32 (leafFlags pg i : Int)).toNat = leafFlags pg i := by
        simp only [BitVec.toNat_ofInt]; omega
      rw [e]; unfold bucketLeafFlag at hbf; omega
    rw [← hk, ← hv]; exact rootEnts_of_allEnts hpA hbk

/-- **A skipped child's value is its root entry's** (`bvalS_cachedNil`, the root's keys being
distinct at the start). -/
theorem nil_val {X : WX} {C : CommitSt} (hok : wOKR X) (hreach : liveReach X)
    (hcok : treeOK C) (hcp : X.v.pages = C.pages) {hwm : Nat} (hch : C.hwm ≤ hwm) {P : Pages}
    (hag : ∀ x pg, X.v.pages !! x = some pg → P !! x = some pg) {B : BRec}
    (hB : X.t.bs !! X.rl = some B) (h0 : B.ib.root' ≠ W64 0) (hrt : rtOK X X.rl)
    (h64 : ∀ p pg, X.v.pages !! p = some pg → p < 2 ^ 64)
    {k : GoString} {c : Loc} (hk : B.bm !! k = some c) {Cc : BRec} (hc : X.t.bs !! c = some Cc)
    (hrn : Cc.bv.rootNode' = null) {v0 : List w8} (hm0 : (k, v0) ∈ rootEnts X) :
    Cc.ib = ibOf v0 ∧ ∃ S, bvalS P hwm v0 S ∧
      ∀ s, s ∈ pgSlots P S ↔ bucketCovers X.v.pages v0 s := by
  have hcl : bktClean X.v X.t.mv.pgid'.toNat X.rl B := (hok.1.2.2.2.2.2 X.rl B hB).1
  obtain ⟨we, hwe, -, hwk, hwv, -⟩ := rootEnt_src hB hcl h0 hm0
  obtain ⟨v', S, hent, hib, hS, hsl⟩ := bvalS_cachedNil hok hcok hcp hch hag hB hk hc hrn
  obtain ⟨we', hwe', hk', hv', -⟩ := entryIn_rootEnts hok hreach hB h0 hrt h64 hent
  have := allEnts_key_injR X hok X.rl B hB we we' hwe hwe' (hwk.trans hk'.symm)
  have hvv : v' = v0 := by rw [← hv', ← this, hwv]
  subst hvv
  exact ⟨hib, S, hS, hsl⟩

end vals

end Spill

end bbolt
end EtcdGrove
end Perennial
