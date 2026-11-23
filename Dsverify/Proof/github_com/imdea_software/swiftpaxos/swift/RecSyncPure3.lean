/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecSyncPure3.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`recoveredSync`'s last phase (the `MSync`'s maps along the order), pure part: the kept commands
are puts or gets (D10, through the reports: `RepsOk.pg`), the order's commands along its
prefixes.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSyncPure2

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace swift.rec

/-- Every kept command is a reported one's, so a put or a get. -/
theorem putget_of {N : Nat} {reps : List (Nat × sp.Report)} (hok : swift.RepsOk N reps)
    {Am : List (Nat × sp.Report)} (hA : ∀ a ∈ Am, a ∈ reps) {k : sp.Kept} (hc : sp.CmdFrom Am k) :
    ∀ y e, k.get y = some e → e.cmd.isPut ∨ e.cmd.isGet := by
  intro y e hy
  obtain ⟨a, ha, re, hre, -, h2⟩ := hc y e hy
  rw [← h2]; exact hok.pg a (hA a ha) re hre

/-- The order's prefix, one more command. -/
theorem fm_take_succ {α β : Type} (O : List α) (f : α → Option β) (j : Nat) (c : α)
    (h : O[j]? = some c) : (O.take (j + 1)).filterMap f = (O.take j).filterMap f ++ (f c).toList := by
  rw [List.take_add_one, h]
  simp only [Option.toList_some, List.filterMap_append]
  cases hf : f c <;> simp [List.filterMap, hf]

/-- In a list without duplicates, the `j`-th element is not before it. -/
theorem notin_take {α : Type} {O : List α} (hnd : O.Nodup) {j : Nat} {c : α}
    (hc : O[j]? = some c) : c ∉ O.take j := by
  intro hm
  have hj : j < O.length := by
    rcases Nat.lt_or_ge j O.length with h | h
    · exact h
    · rw [List.getElem?_eq_none_iff.mpr h] at hc; cases hc
  have hcj : O[j] = c := by rw [List.getElem?_eq_getElem hj] at hc; exact Option.some.inj hc
  rw [← List.take_append_drop j O, List.drop_eq_getElem_cons hj, hcj] at hnd
  exact (List.nodup_append.mp hnd).2.2 c hm c List.mem_cons_self rfl

/-- The ids of an order's commands (each with its own id) are among the order's. -/
theorem fm_fst {α β γ : Type} {l : List α} {g : α → Option β} {h : β → γ} {x : α}
    (hx : x ∈ (l.filterMap (fun c => (g c).map (fun e => (c, h e)))).map Prod.fst) : x ∈ l := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨c, hc, hpc⟩ := List.mem_filterMap.mp hp
  cases hg : g c with
  | none => rw [hg] at hpc; cases hpc
  | some e => rw [hg] at hpc; cases hpc; exact hc

/-- When every element has an entry, the ids are the list. -/
theorem fm_fst_all {α β γ : Type} {g : α → Option β} {h : β → γ} :
    ∀ {l : List α}, (∀ c ∈ l, (g c).isSome) →
      (l.filterMap (fun c => (g c).map (fun e => (c, h e)))).map Prod.fst = l
  | [], _ => rfl
  | c :: l, hall => by
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (hall c List.mem_cons_self)
    rw [List.filterMap_cons, he]
    simp only [Option.map_some, List.map_cons]
    rw [fm_fst_all (fun x hx => hall x (List.mem_cons_of_mem c hx))]

end swift.rec

end Perennial.github_com.imdea_software.swiftpaxos
