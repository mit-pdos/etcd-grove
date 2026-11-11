/-
`Bucket.spill`'s root loop (U9x, `notes/bbolt-proof-plan.md`): **an unspilled tree of a kept
bucket is kept** (`uTree_kept`): `UTreeFrame.uTree_frame` for a bucket whose nodes are all kept
modulo sources and live (a sibling child of the spilled one, whose records the child's spill only
reaches through `spFrame`'s clause for the other buckets).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureKeepOK

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section keeptree
variable [GooseExts]

/-- Bucket `bl`'s nodes kept modulo sources, the live ones live. -/
def nodesKept (X X' : WX) (bl : Loc) : Prop :=
  X'.v.pages = X.v.pages ∧ ∀ l r, X.node bl l = some r →
    ∃ r', X'.node bl l = some r' ∧ nodeSim r r' ∧ (l ∈ X.live → l ∈ X'.live)

theorem uNode_kept {X X' : WX} {bl : Loc} (hk : nodesKept X X' bl) {n : Loc}
    {r r' : NRec} {lo hi : Option (List w8)} (hu : uNode X bl n r lo hi) (hs : nodeSim r r')
    (hl : n ∈ X.live → n ∈ X'.live) : uNode X' bl n r' lo hi := by
  obtain ⟨hlive, hb, hsp, hcap, hlen, hsort, hent, hown⟩ := hu
  refine ⟨hl hlive, by rw [nodeSim_bucket hs]; exact hb, by rw [nodeSim_spilled hs]; exact hsp,
    by rw [hs.2.2.2.2.2.2]; exact hcap, by rw [hs.2.2.2.1, length_of_dat hs.2.2.1]; exact hlen,
    wsSorted_of_dat hs.2.2.1 hsort, fun w' hw' => ?_, ?_⟩
  · obtain ⟨w, hw, he⟩ := mem_of_dat hs.2.2.1 hw'
    rw [wDat_key he, wDat_value he]; exact hent w hw
  · unfold ownPg at hown ⊢; rw [nodeSim_pgid hs, hk.1]; exact hown

theorem spilledN_kept {X X' : WX} {bl : Loc} (hk : nodesKept X X' bl) {c : Loc}
    (hc : spilledN X bl c) : spilledN X' bl c := by
  obtain ⟨hl, rc, hrc, hb, hsp, hcs, hne⟩ := hc
  obtain ⟨rc', hrc', hs, hl'⟩ := hk.2 c rc hrc
  exact ⟨hl' hl, rc', hrc', by rw [nodeSim_bucket hs]; exact hb,
    by rw [nodeSim_spilled hs]; exact hsp, by rw [hs.2.2.2.2.1]; exact hcs,
    by rw [length_of_dat hs.2.2.1]; exact hne⟩

/-- **An unspilled tree of a kept bucket is kept** (see the module doc). -/
theorem uTree_kept {X X' : WX} {bl : Loc} {P P' : Pages} {hwm hwm' : Nat}
    (hk : nodesKept X X' bl) (hh : hwm ≤ hwm') {n : Loc} {lo hi : Option (List w8)} {h : Nat}
    {F D : List Nat} {N : List Loc} {E : List El} (hu : uTree X bl P hwm n lo hi h F D N E) :
    (∀ x ∈ D, P' !! x = P !! x) → uTree X' bl P' hwm' n lo hi h F D N E :=
  uTree.rec (X := X) (bl := bl) (P := P) (hwm := hwm)
    (motive_1 := fun n lo hi h F D N E _ => (∀ x ∈ D, P' !! x = P !! x) →
      uTree X' bl P' hwm' n lo hi h F D N E)
    (motive_2 := fun n lo hi ws cs h i w e _ => ∀ (ws' : List WEntry) (w' : WEntry),
      ws'.map wDat = ws.map wDat → wDat w' = wDat w →
      (∀ x ∈ e.D, P' !! x = P !! x) → uEnt X' bl P' hwm' n lo hi ws' cs h i w' e)
    (fun n r lo hi Sb hr hun hleaf hcs hbv hb0 hP => by
      obtain ⟨r', hr', hs, hl⟩ := hk.2 n r hr
      have hD : ∀ i, i < r.ws.length → ∀ x ∈ Sb i, P' !! x = P !! x := by
        intro i hi x hx
        refine hP x (List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩))
        exact mem_pgSlots_self hx
      have H := uTree.leaf (X := X') (bl := bl) (P := P') (hwm := hwm') n r' lo hi Sb hr'
        (uNode_kept hk hun hs hl) (by rw [nodeSim_isLeaf hs]; exact hleaf)
        (by rw [hs.2.2.2.2.1]; exact hcs)
        (fun i w' hw' hf => by
          obtain ⟨w, hw, he⟩ := get_of_dat hs.2.2.1 hw'
          rw [wDat_value he]
          have hi : i < r.ws.length := (List.getElem?_eq_some_iff.1 hw).1
          exact bvalS_agree (hD i hi) hh (hbv i w hw (by rw [← wDat_flags he]; exact hf)))
        (fun i w' hw' hf => by
          obtain ⟨w, hw, he⟩ := get_of_dat hs.2.2.1 hw'
          exact hb0 i w hw (by rw [← wDat_flags he]; exact hf))
      rw [nodeSim_pgid hs, ownSl_congr hk.1, length_of_dat hs.2.2.1,
        wEl_of_dat hs.2.2.1] at H
      have e : ((List.range r.ws.length).flatMap fun i => pgSlots P' (Sb i)) =
          (List.range r.ws.length).flatMap fun i => pgSlots P (Sb i) := by
        apply flatMap_congr'
        intro i hi
        exact pgSlots_congr (hD i (List.mem_range.1 hi))
      rw [e] at H
      exact H)
    (fun n r lo hi h es hr hun hleaf h2 hlen hent hchnd hcs hcsnd hNnd hpg0 ih hP => by
      obtain ⟨r', hr', hs, hl⟩ := hk.2 n r hr
      have hlen' := length_of_dat hs.2.2.1
      have H := uTree.branch (X := X') (bl := bl) (P := P') (hwm := hwm') n r' lo hi h es hr'
        (uNode_kept hk hun hs hl) (by rw [nodeSim_isLeaf hs]; exact hleaf)
        (by rw [hlen']; exact h2) (by rw [hlen']; exact hlen)
        (fun i w' e hw' he => by
          obtain ⟨w, hw, hwe⟩ := get_of_dat hs.2.2.1 hw'
          rw [hs.2.2.2.2.1]
          have hm : e ∈ es := List.mem_of_getElem? he
          exact ih i w e hw he r'.ws w' hs.2.2.1 hwe (fun x hx => hP x
            (List.mem_append_right _ (List.mem_flatMap.2 ⟨e, hm, hx⟩))))
        hchnd
        (fun c hc => by
          rw [hs.2.2.2.2.1] at hc
          rcases hcs c hc with h' | h'
          · exact Or.inl h'
          · exact Or.inr (spilledN_kept hk h'))
        (by rw [hs.2.2.2.2.1]; exact hcsnd) hNnd
        (fun h0 => hpg0 (by rw [← nodeSim_pgid hs]; exact h0))
      rw [nodeSim_pgid hs, ownSl_congr hk.1] at H
      exact H)
    (fun n lo hi ws cs h i w c rc F D N E hc hrc hpar hpg hkey hk' hne hut ih ws' w' hws hw hP => by
      obtain ⟨rc', hrc', hs, -⟩ := hk.2 c rc hrc
      have H := ih hP
      rw [← wKey_of_dat hws, ← length_of_dat hws] at H
      exact uEnt.child n lo hi ws' cs h i w' c rc' F D N E hc hrc'
        (by rw [nodeSim_parent hs]; exact hpar) (by rw [nodeSim_pgid hs, wDat_pgid hw]; exact hpg)
        (by rw [hs.2.2.2.2.2.1, wDat_key hw]; exact hkey)
        (fun h0 => hk' (hs.2.1.1 h0))
        ⟨by rw [length_of_dat hs.2.2.1]; exact hne.1, by rw [hs.2.2.2.2.1]; exact hne.2⟩ H)
    (fun n lo hi ws cs h i w S E hf ws' w' hws hw hP => by
      obtain ⟨hf', he⟩ := fTree_agree hP hh hf
      have H := uEnt.fin (X := X') (bl := bl) (P := P') (hwm := hwm') n lo hi ws' cs h i w' S E
        (by rw [wDat_pgid hw, wDat_key hw, wKey_of_dat hws, length_of_dat hws]; exact hf')
      rw [he] at H
      exact H)
    hu

/-- **A kept, live bucket's nodes are kept** (`live_kept`). -/
theorem nodesKept_of_kept {X X' : WX} {bl : Loc} (hkept : bktKept X X' bl)
    (hv : X'.v.pages = X.v.pages) (hreach : liveReach X) (hp' : derefPre X')
    (hbl : bl ∈ X'.liveB) : nodesKept X X' bl := by
  refine ⟨hv, fun l r hr => ?_⟩
  unfold WX.node at hr
  cases hB : X.t.bs !! bl with
  | none => rw [hB] at hr; cases hr
  | some B =>
    rw [hB] at hr
    simp only [Option.bind_some] at hr
    obtain ⟨B', hB', hs, hns⟩ := hkept B hB
    obtain ⟨r', hr', e⟩ := fwd_kept hns hr
    exact ⟨r', by unfold WX.node; rw [hB']; exact hr', e,
      fun hl => live_kept hB hB' hs hns hreach hp' hbl hr hl⟩

end keeptree

end Spill

end bbolt
end EtcdGrove
end Perennial
