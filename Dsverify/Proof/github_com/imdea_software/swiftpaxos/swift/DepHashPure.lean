/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DepHashPure.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`getDepAndHashes`' pure core (notes/prove-swift.md §12, §13): the keys' `lightKeyInfo`s along a
sequence (`lkOf`) give the model's dependencies (`lkDeps`), and a hash log's `Append` of a fresh
command keeps `hlogOk`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Local

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open swift.lki in
/-- `lkOf` along one more command. -/
theorem swift.lkOf_append1 (s : sp.Seq) (p : sp.CmdId × sp.Cmd) (k : w64) :
    swift.lkOf (s ++ [p]) k =
      if p.2.key = k then addTo p.2.op (ofCmdId p.1) (swift.lkOf s k).1 (swift.lkOf s k).2
      else swift.lkOf s k := by
  unfold swift.lkOf; rw [List.foldl_append]; rfl

/-- No command of key `k`: no `lightKeyInfo` contents. -/
theorem swift.lkOf_absent (s : sp.Seq) (k : w64) (h : ∀ p ∈ s, p.2.key ≠ k) :
    swift.lkOf s k = ([], []) := by
  induction s using sp.revInd with
  | h0 => rfl
  | hs s p ih =>
    rw [swift.lkOf_append1, if_neg (h p (by simp))]
    exact ih (fun q hq => h q (by simp [hq]))

/-- `C` grows by at most one per command. -/
theorem swift.lkOf_len (s : sp.Seq) (k : w64) : (swift.lkOf s k).2.length ≤ s.length := by
  induction s using sp.revInd with
  | h0 => simp [swift.lkOf]
  | hs s p ih =>
    rw [swift.lkOf_append1]
    split
    · unfold swift.lki.addTo; split <;> simp <;> omega
    · simp; omega

/-- **The `lightKeyInfo` is the model's dependencies**: `W` those of a non-put of key `k`
(the last put), `C` those of a put (the last put and the commands since). -/
theorem swift.lkOf_deps (s : sp.Seq) (c : sp.Cmd) :
    (if c.isPut then (swift.lkOf s c.key).2 else (swift.lkOf s c.key).1) =
      (sp.lkDeps s c).map ofCmdId := by
  induction s using sp.revInd with
  | h0 => simp [swift.lkOf, sp.lkDeps]
  | hs s p ih =>
    rw [swift.lkOf_append1, sp.lkDeps_snoc]
    by_cases hk : p.2.key = c.key
    · rw [if_pos hk, if_pos hk]
      unfold swift.lki.addTo
      by_cases hp : p.2.isPut = true
      · have hop : p.2.op = W8 1 := by
          unfold sp.Cmd.isPut sp.opPUT at hp; simpa using hp
        rw [if_pos hop, if_pos hp]
        split <;> rfl
      · have hop : ¬ p.2.op = W8 1 := by
          intro h; apply hp; unfold sp.Cmd.isPut sp.opPUT; simp [h]
        rw [if_neg hop, if_neg hp]
        by_cases hc : c.isPut = true
        · rw [if_pos hc, if_pos hc]; rw [if_pos hc] at ih; simp [ih]
        · rw [if_neg hc, if_neg hc]; rw [if_neg hc] at ih; exact ih
    · rw [if_neg hk, if_neg hk]; exact ih

/-- `getConflictCmds`' choice (`W` for a get, else `C`) for a put or a get. -/
theorem swift.lkOf_conflict (s : sp.Seq) (c : sp.Cmd) (hc : c.isPut ∨ c.isGet) :
    (if c.op = W8 2 then (swift.lkOf s c.key).1 else (swift.lkOf s c.key).2) =
      (sp.lkDeps s c).map ofCmdId := by
  rw [← swift.lkOf_deps]
  rcases hc with h | h
  · have hop : c.op = W8 1 := by unfold sp.Cmd.isPut sp.opPUT at h; simpa using h
    rw [if_pos h, if_neg (by rw [hop]; decide)]
  · have hop : c.op = W8 2 := by unfold sp.Cmd.isGet sp.opGET at h; simpa using h
    have hp : c.isPut = false := by unfold sp.Cmd.isPut sp.opPUT; simp [hop]
    rw [if_pos hop, hp]; rfl

/-- `idsOfKey` along one more command. -/
theorem swift.idsOfKey_append1 (hd : sp.Seq) (x : sp.CmdId) (c : sp.Cmd) (k : w64) :
    swift.idsOfKey (hd ++ [(x, c)]) k =
      if c.key = k then swift.idsOfKey hd k ++ [x] else swift.idsOfKey hd k := by
  unfold swift.idsOfKey
  by_cases h : c.key = k <;> simp [List.filter_append, h]

theorem swift.idsOfKey_absent (hd : sp.Seq) (k : w64) (h : ∀ p ∈ hd, p.2.key ≠ k) :
    swift.idsOfKey hd k = [] := by
  unfold swift.idsOfKey
  simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
  exact h

theorem swift.idsOfKey_sub (hd : sp.Seq) (k : w64) (z : sp.CmdId)
    (h : z ∈ swift.idsOfKey hd k) : z ∈ hd.map Prod.fst := by
  unfold swift.idsOfKey at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact List.mem_map_of_mem (List.mem_filter.mp hp).1

namespace swift.hlog

/-- A fresh log of a key no handled command has is `hlogOk`. -/
theorem hlogOk_init (ld : Bool) (hd : sp.Seq) (K : sp.CmdId → Prop)
    (Λ : w64 → w64 → List sp.CmdId → Prop) (k : w64) (h : ∀ p ∈ hd, p.2.key ≠ k) :
    swift.hlogOk ld hd K Λ k HL.init := by
  have he := swift.idsOfKey_absent hd k h
  refine ⟨fun z hz => by simp [HL.init] at hz, fun z hz => by rw [he] at hz; simp at hz,
    fun x hx => by simp [HL.init] at hx, fun _ => ⟨rfl, by rw [he]; rfl, fun _ => rfl⟩,
    Or.inl ⟨by simp [HL.init], rfl⟩⟩

/-- `hlogOk_init` from `idsOfKey hd k = []`. -/
theorem hlogOk_init' (ld : Bool) (hd : sp.Seq) (K : sp.CmdId → Prop)
    (Λ : w64 → w64 → List sp.CmdId → Prop) (k : w64) (h : swift.idsOfKey hd k = []) :
    swift.hlogOk ld hd K Λ k HL.init := by
  refine ⟨fun z hz => by simp [HL.init] at hz, fun z hz => by rw [h] at hz; simp at hz,
    fun x hx => by simp [HL.init] at hx, fun _ => ⟨rfl, by rw [h]; rfl, fun _ => rfl⟩,
    Or.inl ⟨by simp [HL.init], rfl⟩⟩

/-- `hlogOk` is monotone in `K` and `Λ`. -/
theorem hlogOk_mono {ld : Bool} {hd : sp.Seq} {K K' : sp.CmdId → Prop}
    {Λ Λ' : w64 → w64 → List sp.CmdId → Prop} {k : w64} {σ : HL}
    (hK : ∀ y, K y → K' y) (hΛ : ∀ k s P, Λ k s P → Λ' k s P) (h : swift.hlogOk ld hd K Λ k σ) :
    swift.hlogOk ld hd K' Λ' k σ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, fun y hy => (h3 y hy).imp_right (hK y), h4, h5.imp_right (hΛ _ _ _)⟩

/-- A key other than the command's: the log is still `hlogOk` after the command. -/
theorem hlogOk_other (ld : Bool) (hd : sp.Seq) (K : sp.CmdId → Prop)
    (Λ : w64 → w64 → List sp.CmdId → Prop) (k : w64) (σ : HL) (x : sp.CmdId) (c : sp.Cmd)
    (hk : c.key ≠ k) (h : swift.hlogOk ld hd K Λ k σ) :
    swift.hlogOk ld (hd ++ [(x, c)]) K Λ k σ := by
  have he := swift.idsOfKey_append1 hd x c k
  rw [if_neg hk] at he
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by rw [he]; exact h1, by rw [he]; exact h2, fun y hy => ?_, by rw [he]; exact h4, h5⟩
  rcases h3 y hy with h | h
  · left; simp [h]
  · right; exact h

/-- **`Append` of a fresh command** of the log's key (not in `K`): `hlogOk` along it, and the
path of the hash it returns ends in it, is the leader's whole key history, and has every handled
command of the key. -/
theorem hlogOk_append (ld : Bool) (hd : sp.Seq) (K : sp.CmdId → Prop)
    (Λ : w64 → w64 → List sp.CmdId → Prop) (σ : HL) (x : sp.CmdId) (c : sp.Cmd)
    (h : swift.hlogOk ld hd K Λ c.key σ) (hx : x ∉ hd.map Prod.fst) (hxK : ¬ K x) :
    x ∉ σ.pending ∧ swift.hlogOk ld (hd ++ [(x, c)]) K Λ c.key (σ.append x).1 ∧
      (σ.append x).2.getLast? = some x ∧
      (ld = true → (σ.append x).2 = swift.idsOfKey hd c.key ++ [x]) ∧
      (∀ z ∈ swift.idsOfKey hd c.key, z ∈ (σ.append x).2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hu : σ.upd x = none := by
    cases hq : σ.upd x with
    | none => rfl
    | some e =>
      rcases h3 x (by rw [hq]; rfl) with h | h
      · exact absurd h hx
      · exact absurd h hxK
  have he := swift.idsOfKey_append1 hd x c c.key
  rw [if_pos rfl] at he
  have hnp : x ∉ σ.pending := fun hp => hx (swift.idsOfKey_sub hd c.key x (h1 x hp))
  unfold HL.append
  rw [hu]
  refine ⟨hnp, ⟨?_, ?_, ?_, ?_, h5⟩, ?_, ?_, ?_⟩
  · intro z hz
    rw [he]
    rcases List.mem_append.mp hz with hz | hz
    · exact List.mem_append_left _ (h1 z hz)
    · exact List.mem_append_right _ hz
  · intro z hz
    rw [he] at hz
    rcases List.mem_append.mp hz with hz | hz
    · rcases h2 z hz with h' | h'
      · left; exact List.mem_append_left _ h'
      · right; exact h'
    · left; exact List.mem_append_right _ hz
  · intro y hy
    rcases h3 y hy with h | h
    · left; simp [h]
    · right; exact h
  · intro hl
    obtain ⟨hb, hp, hn⟩ := h4 hl
    exact ⟨hb, by rw [he, hp], hn⟩
  · simp
  · intro hl
    obtain ⟨hb, hp, -⟩ := h4 hl
    simp [hb, hp]
  · intro z hz
    rcases h2 z hz with h' | h'
    · simp [h']
    · simp [h']

end swift.hlog

end Perennial.github_com.imdea_software.swiftpaxos
