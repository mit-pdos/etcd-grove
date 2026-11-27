/- Lean-first (no Rocq counterpart).

# `mvccfull`: the run's file names

A run's files by name (`runNames ops`, for `ops` operations; until 2026-11-26 `mvccfullNames`,
`Main`'s 12000) and their facts: pairwise distinct, each a valid name, of at most 255 bytes for
fewer than `2 ^ 38` operations, and `FilePaths` at the prefix `r/mvccfull` is them under `r`
(`filePaths_at`); and `MainConfig`'s configuration in `Run`'s scope (`mainConfig_okAt`). `MainAt`'s
proof, which checks the names itself, takes them (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.LogModel
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.FilePaths
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.MainConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.itoa
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.buildPath
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.memberPath
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.normalize
public import GooseLang.Ext.Fs.TreeLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull

/-- **A run's files, by name**, for `ops` operations (`FilePaths` of a configuration with the prefix
`mvccfull`): the members' `mvccfull-0.db`, `mvccfull-1.db` and the builders' `mvccfull-b<n>.db`,
`n` from 1 to `ops`. -/
def runNames [GooseExts] (ops : w64) : List GoString :=
  [memberPathM go!"mvccfull" 0, memberPathM go!"mvccfull" 1] ++
    (List.range' 1 (sint.nat ops)).map (buildPathM go!"mvccfull")

end mvccfull

/-! ## The program's files -/

namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull

-- (moved here from `itoa.lean`, P3, 2026-11-24)
theorem decDigits_zero : decDigits 0 = [] := by
  rw [decDigits]; simp

theorem decDigits_pos (n : Nat) (h : n ≠ 0) :
    decDigits n = decDigits (n / 10) ++ [W8 (48 + n % 10 : Nat)] := by
  rw [decDigits]; simp [h]

theorem decDigits_ne_nil (n : Nat) (h : n ≠ 0) : decDigits n ≠ [] := by
  rw [decDigits_pos n h]; simp

/-- `n`'s decimal digits determine `n` (for `n ≠ 0`). -/
theorem decDigits_inj : ∀ (a b : Nat), a ≠ 0 → b ≠ 0 → decDigits a = decDigits b → a = b := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b ha hb he
    rw [decDigits_pos a ha, decDigits_pos b hb] at he
    obtain ⟨h1, h2⟩ := List.append_inj' he rfl
    simp only [List.cons.injEq, and_true] at h2
    have hd : a % 10 = b % 10 := by
      have := congrArg (fun w : w8 => uint.Z w) h2
      have ha10 := Nat.mod_lt a (by decide : 10 > 0)
      have hb10 := Nat.mod_lt b (by decide : 10 > 0)
      word
    by_cases ha' : a / 10 = 0
    · by_cases hb' : b / 10 = 0
      · omega
      · exfalso; rw [ha', decDigits_zero] at h1
        exact decDigits_ne_nil _ hb' h1.symm
    · by_cases hb' : b / 10 = 0
      · exfalso; rw [hb', decDigits_zero] at h1
        exact decDigits_ne_nil _ ha' h1
      · have := ih (a / 10) (by omega) (b / 10) ha' hb' h1
        omega

theorem decDigits_one (n : Nat) (h : n ≠ 0) (x : w8) (he : decDigits n = [x]) :
    n < 10 ∧ x = W8 (48 + n % 10 : Nat) := by
  rw [decDigits_pos n h] at he
  by_cases h' : n / 10 = 0
  · rw [h', decDigits_zero] at he
    simp only [List.nil_append, List.cons.injEq, and_true] at he
    exact ⟨by omega, he.symm⟩
  · exfalso
    have hl := congrArg List.length he
    have hne : (decDigits (n / 10)).length ≠ 0 := by
      have := decDigits_ne_nil _ h'; simpa using this
    simp only [List.length_append, List.length_singleton] at hl
    omega

/-- `itoa` is injective. -/
theorem itoaM_inj (a b : Nat) (he : itoaM a = itoaM b) : a = b := by
  unfold itoaM at he
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · omega
  · simp only [ha, hb, ↓reduceIte] at he
    obtain ⟨h1, h2⟩ := decDigits_one b hb _ he.symm
    have := congrArg (fun w : w8 => uint.Z w) h2
    simp at this; word
  · simp only [ha, hb, ↓reduceIte] at he
    obtain ⟨h1, h2⟩ := decDigits_one a ha _ he
    have := congrArg (fun w : w8 => uint.Z w) h2
    simp at this; word
  · simp only [ha, hb, ↓reduceIte] at he
    exact decDigits_inj a b ha hb he

theorem buildPathM_inj (a b : Nat) (h : buildPathM go!"mvccfull" a = buildPathM go!"mvccfull" b) :
    a = b := by
  unfold buildPathM at h
  simp only [List.append_assoc, List.append_cancel_left_eq, List.append_cancel_right_eq] at h
  exact itoaM_inj a b h

theorem buildPathM_ne0 (n : Nat) : buildPathM go!"mvccfull" n ≠ memberPathM go!"mvccfull" 0 := by
  unfold buildPathM memberPathM
  simp [itoaM]

theorem buildPathM_ne1 (n : Nat) : buildPathM go!"mvccfull" n ≠ memberPathM go!"mvccfull" 1 := by
  unfold buildPathM memberPathM
  simp [itoaM, decDigits_pos 1 (by decide), decDigits_zero]

/-- **A run's files are distinct**: the members' `mvccfull-0.db`, `mvccfull-1.db` and the builders'
`mvccfull-b<n>.db`. -/
theorem runNames_nodup [GooseExts] (ops : w64) : (runNames ops).Nodup := by
  unfold runNames
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · simp [memberPathM, itoaM, decDigits_pos 1 (by decide), decDigits_zero]
  · exact List.pairwise_map.2 ((List.nodup_range' (s := 1) (n := sint.nat ops)).imp fun h e => h (buildPathM_inj _ _ e))
  · intro x hx y hy hxy
    subst hxy
    simp only [List.mem_map] at hy
    obtain ⟨n, -, rfl⟩ := hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h
    · exact buildPathM_ne0 n h
    · exact buildPathM_ne1 n h

end mvccfull

/-! ## The program's files at a root (S3e) -/

namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull

/-- A decimal digit's byte. -/
theorem decDigits_mem : ∀ (n : Nat) (c : w8), c ∈ decDigits n → 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro c hc
    by_cases h0 : n = 0
    · subst h0; rw [decDigits_zero] at hc; exact absurd hc List.not_mem_nil
    · rw [decDigits_pos n h0] at hc
      rcases List.mem_append.1 hc with h | h
      · exact ih (n / 10) (by omega) c h
      · simp only [List.mem_singleton] at h
        subst h
        have h10 := Nat.mod_lt n (by decide : 10 > 0)
        refine ⟨?_, ?_⟩ <;> word

theorem itoaM_mem (n : Nat) (c : w8) (hc : c ∈ itoaM n) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  unfold itoaM at hc
  split at hc
  · simp only [List.mem_singleton] at hc; subst hc; decide
  · exact decDigits_mem n c hc

/-- A name of at least three bytes, none a slash or a NUL, is a name (`NameOk`). -/
theorem nameOk_of (b : GoString) (hl : 3 ≤ b.length) (hc : ∀ c ∈ b, c.toNat ≠ 47 ∧ c.toNat ≠ 0) :
    NameOk b := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; subst h; simp at hl
  · intro h; subst h; simp at hl
  · intro h; subst h; simp at hl
  · intro h; exact (hc _ h).1 rfl
  · intro h; exact (hc _ h).2 rfl

theorem memberPathM_child (r p : GoString) (k : Nat) :
    memberPathM (Fs.child r p) k = Fs.child r (memberPathM p k) := by
  simp [memberPathM, Fs.child, List.append_assoc]

theorem buildPathM_child (r p : GoString) (k : Nat) :
    buildPathM (Fs.child r p) k = Fs.child r (buildPathM p k) := by
  simp [buildPathM, Fs.child, List.append_assoc]

/-- The files of a run at the prefix `r/mvccfull` are the names in the directory `r`. -/
theorem filePaths_at [GooseExts] (r : GoString) (cfg : Config)
    (hp : cfg.Prefix' = Fs.child r go!"mvccfull") :
    filePathsM cfg = (runNames cfg.Ops').map (Fs.child r) := by
  unfold runNames filePathsM
  rw [hp]
  simp only [memberPathM_child, List.map_append, List.map_cons, List.map_nil, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [buildPathM_child]

/-- Each of a run's files is a name. -/
theorem runNames_ok [GooseExts] (ops : w64) : ∀ b ∈ runNames ops, NameOk b := by
  intro b hb
  unfold runNames at hb
  rcases List.mem_append.1 hb with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> apply nameOk_of <;>
      first
      | (simp [memberPathM]; done)
      | (intro c hc
         simp only [memberPathM, List.mem_append] at hc
         rcases hc with (hc | hc) | hc
         · revert c; decide
         · have := itoaM_mem _ c hc; omega
         · revert c; decide)
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h
    apply nameOk_of
    · simp [buildPathM]
    · intro c hc
      simp only [buildPathM, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · revert c; decide
      · have := itoaM_mem k c hc; omega
      · revert c; decide

/-- A number below `10 ^ k` has at most `k` decimal digits (as `runner__newVal.lean`'s, private there). -/
theorem decDigits_length_le' : ∀ (k n : Nat), n < 10 ^ k → (decDigits n).length ≤ k
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; rw [decDigits]; simp
  | k + 1, n, h => by
    rw [decDigits]
    split
    · simp
    · simp only [List.length_append, List.length_singleton]
      have := decDigits_length_le' k (n / 10) (by rw [Nat.pow_succ] at h; omega)
      omega

/-- Each of a run's files is a name of at most 255 bytes, for fewer than `2 ^ 38` operations
(wal-fsfix, 2026-11-20: with `Fs.DirFits r`, its path fits, `PathFits`). -/
theorem runNames_len [GooseExts] (ops : w64) (hops : sint.Z ops < 2 ^ 38) :
    ∀ b ∈ runNames ops, b.length ≤ 255 := by
  intro b hb
  have hi : ∀ n, n < 10 ^ 20 → (itoaM n).length ≤ 20 := fun n hn => by
    unfold itoaM; split
    · decide
    · exact decDigits_length_le' 20 n hn
  unfold runNames at hb
  rcases List.mem_append.1 hb with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp [memberPathM, itoaM] <;>
      first | decide | (have := decDigits_length_le' 1 1 (by decide); omega)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
    have hk' : k < 10 ^ 20 := by
      rw [List.mem_range'_1] at hk
      have : sint.nat ops < 2 ^ 38 := by word
      omega
    have := hi k hk'
    simp only [buildPathM, List.length_append] at this ⊢
    have h8 : (go!"mvccfull" : GoString).length = 8 := by decide
    have h2 : (go!"-b" : GoString).length = 2 := by decide
    have h3 : (go!".db" : GoString).length = 3 := by decide
    omega

/-- **`MainConfig`'s configuration is in `Run`'s scope** (its read weights the code's), at any
prefix (`Main.lean`'s `mainConfig_ok`, at `"mvccfull"`). -/
theorem mainConfig_okAt [GooseExts] [GoGlobalContext] (pfx : GoString) (mx : Mix) :
    runCfgOk (mainConfigM pfx mx) [W64 1, W64 1, W64 2, W64 1, W64 1, W64 0] := by
  have hk : (keysOf 4).length = 120 := by decide
  have hlim : limOf (mainConfigM pfx mx) = W64 3 := by
    unfold limOf; exact if_pos (show (0 : Int) < sint.Z (W64 3) by decide)
  have hcbl : cblOf (mainConfigM pfx mx) = W64 2 := by
    unfold cblOf; exact if_pos (show (0 : Int) < sint.Z (W64 2) by decide)
  have hdep : (normalizeM (mainConfigM pfx mx)).Depth' = W64 4 := by
    unfold normalizeM mainConfigM; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold readMixOk; refine ⟨by decide, ⟨0, by decide, by decide⟩, by decide⟩
  · show (0 : Int) ≤ sint.Z (W64 12000); decide
  · show sint.Z (W64 12000) < 2 ^ 38; decide
  · show 2 * max 0 (sint.Z (W64 2)) + 4 * max 0 (sint.Z (W64 2)) + 3 ≤ 2 ^ 28; decide
  · rw [hlim]; decide
  · rw [hcbl]; unfold mvcc.batchLimitOk; decide
  · rw [hdep, show sint.nat (W64 4) = 4 by decide, hk]; decide
  · show sint.Z (mainConfigM pfx mx).MaxVal' ≤ 2 ^ 20
    rw [show (mainConfigM pfx mx).MaxVal' = W64 5000 from rfl]; decide
  · rw [hdep]; decide

end mvccfull

end EtcdGrove
end Perennial

end
