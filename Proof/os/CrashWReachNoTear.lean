/- Lean-first (no Rocq counterpart). A retried write under the no-tear premise (`NoTearCut`,
`GooseLang/Ext/Fs/NoTear.lean`): an attempt that returns an errno lands nothing, so the loop's count
`nn` is exactly the prefix of the data written (`WReach.exact`, for any such cut); each attempt of
a page-aligned write starts on a page boundary (`WReach.noTear_cut`); and, the sectors of the range
being unknown at first, the file's versions stay known through every attempt (`WReach.noTear_vk`):
each attempt meets only sectors no earlier attempt met.
-/
module

public import Proof.os.CrashWReach
public import GooseLang.Ext.Fs.NoTear

@[expose] public section

noncomputable section

namespace Perennial

open Fs

/-- **A retried write whose cut lands nothing with an errno** has written exactly the first `nn`
bytes of the data (the size is as one attempt of `nn` bytes leaves it). -/
theorem WReach.exact {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8}
    {C : Nat → Nat → Nat → w64 → Prop} (hC : ∀ o l k e, C o l k e → e ≠ 0 → k = 0)
    {nn : Nat} {m' : OsMeta} {bs' : List (w8 × Bool)}
    (h : WReach C m bs off data nn m' bs')
    (hl : bs.length = m.size) (hoff : off ≤ m.size) (h64 : data.length < 2 ^ 64) :
    nn ≤ data.length ∧ m'.size = pwSize m.size off nn ∧
      ∀ i, off ≤ i → i < off + data.length → i < pwSize m.size off nn →
      bs'[i]? = if i < off + nn then some (data.getD (i - off) 0, false) else bs[i]? := by
  induction h with
  | refl =>
    exact ⟨Nat.zero_le _, by simp [pwSize], fun i _ _ _ => by rw [if_neg (by omega)]⟩
  | @step nn m1 bs1 k nn' e hR hnn hk hck hnn' ih =>
    obtain ⟨-, hsz, hK⟩ := ih
    have hdl : (data.drop nn).length = data.length - nn := List.length_drop
    have hC' := hck (by rw [hdl]; omega)
    have hE : nn' = nn + k := by
      rcases hnn' with h | ⟨he, h⟩
      · exact h
      · have := hC _ _ _ _ hC' he; omega
    subst hE
    have hN := hR.narrow hl hoff
    have hS : off + nn ≤ m1.size := by
      rw [hsz]; unfold pwSize; split
      · omega
      · omega
    refine ⟨by omega, ?_, fun i h1 h2 h3 => ?_⟩
    · show pwSize m1.size (off + nn) k = _
      rw [hsz, pwSize_from' _ _ _ _ _ (Nat.le_refl nn), Nat.max_eq_right (by omega)]
    rw [← Nat.max_eq_right (Nat.le_add_right nn k), ← pwSize_from' _ _ _ _ _ (Nat.le_refl nn),
      ← hsz] at h3
    by_cases a : i < off + nn
    · rw [finBytes_pre hN.len i (by unfold cfLo; omega)]
      have h3' : i < pwSize m.size off nn := by rw [← hsz]; omega
      rw [hK i h1 h2 h3', if_pos a, if_pos (by omega)]
    · rw [finBytes_mid (m := m1) (bs := bs1) (off := off + nn) (data := data.drop nn) hN.len
        (by rw [hdl]; exact hk) i (by omega) (by rw [hdl]; omega) h3]
      by_cases b : i < off + nn + k
      · rw [if_pos b, if_pos (by omega), getD_drop', show nn + (i - (off + nn)) = i - off by omega]
      · rw [if_neg b, if_neg (by omega)]
        have h3' : i < pwSize m.size off nn := by
          rw [← hsz]; unfold pwSize at h3; split at h3 <;> omega
        rw [hK i h1 h2 h3', if_neg a]

theorem noTearCut_errno : ∀ o l k e, NoTearCut o l k e → e ≠ 0 → k = 0 :=
  fun _ _ _ _ h he => h.2 he

/-- **Each attempt of a page-aligned write starts on a page boundary** (or the write is done):
an attempt lands a page cut, and nothing with an errno. -/
theorem WReach.noTear_cut {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8}
    {nn : Nat} {m' : OsMeta} {bs' : List (w8 × Bool)}
    (h : WReach NoTearCut m bs off data nn m' bs') (ha : off % 4096 = 0)
    (h64 : data.length < 2 ^ 64) :
    nn = data.length ∨ (off + nn) % 4096 = 0 := by
  induction h with
  | refl => exact .inr (by omega)
  | @step nn m1 bs1 k nn' e hR hnn hk hck hnn' ih =>
    have hdl : (data.drop nn).length = data.length - nn := List.length_drop
    obtain ⟨⟨-, hpc⟩, he⟩ := hck (by rw [hdl]; omega)
    have hE : nn' = nn + k := by
      rcases hnn' with h | ⟨he', h⟩
      · exact h
      · have := he he'; omega
    subst hE
    rw [hdl] at hpc
    rcases hpc with h0 | h0 | h0
    · subst h0; exact ih
    · left; omega
    · right; omega

theorem secHits_mono {lo lo' hi hi' n : Nat} (h1 : lo' ≤ lo) (h2 : hi ≤ hi')
    (h : secHits lo hi n = true) : secHits lo' hi' n = true := by
  unfold secHits at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at *
  omega

/-- **The versions stay known through a page-aligned write's attempts**, if the sectors of its
range were not known with two versions at first: each attempt meets sectors no earlier one met. -/
theorem WReach.noTear_vk {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8}
    {nn : Nat} {m' : OsMeta} {bs' : List (w8 × Bool)}
    (h : WReach NoTearCut m bs off data nn m' bs')
    (hl : bs.length = m.size) (hoff : off ≤ m.size) (ha : off % 4096 = 0)
    (h64 : data.length < 2 ^ 64) {ns : List Nat} (hvk : m.vk = some ns)
    (hns : ∀ n, secHits off (off + data.length) n = true → n ∉ ns) :
    ∃ ns', m'.vk = some ns' ∧
      (nn < data.length → ∀ n, secHits (off + nn) (off + data.length) n = true → n ∉ ns') := by
  induction h with
  | refl => exact ⟨ns, hvk, fun _ n hn => hns n (by simpa using hn)⟩
  | @step nn m1 bs1 k nn' e hR hnn hk hck hnn' ih =>
    have hR' := WReach.step k nn' e hR hnn hk hck hnn'
    have hcut := hR'.noTear_cut ha h64
    obtain ⟨ns1, hv1, hn1⟩ := ih
    have hn1 := hn1 hnn
    have hdl : (data.drop nn).length = data.length - nn := List.length_drop
    obtain ⟨⟨-, -⟩, he⟩ := hck (by rw [hdl]; omega)
    have hE : nn' = nn + k := by
      rcases hnn' with h | ⟨he', h⟩
      · exact h
      · have := he he'; omega
    subst hE
    obtain ⟨-, hsz, -⟩ := hR.exact noTearCut_errno hl hoff h64
    have hS : off + nn ≤ m1.size := by
      rw [hsz]; unfold pwSize; split
      · omega
      · omega
    have hall : (hitSecs (off + nn) (off + nn + k)).all (fun n => decide (n ∉ ns1)) = true := by
      rw [List.all_eq_true]
      intro n hn
      rw [mem_hitSecs] at hn
      exact decide_eq_true (hn1 n (secHits_mono (Nat.le_refl _) (by omega) hn))
    refine ⟨ns1 ++ hitSecs (off + nn) (off + nn + k), ?_, fun hlt n hn => ?_⟩
    · show vkHit m1.vk (min (off + nn) m1.size) (off + nn + k) = _
      rw [hv1, Nat.min_eq_left hS]
      simp only [vkHit, if_pos hall]
    · rw [List.mem_append, not_or]
      refine ⟨hn1 n (secHits_mono (by omega) (Nat.le_refl _) hn), fun hm => ?_⟩
      rw [mem_hitSecs] at hm
      have ha' : (off + (nn + k)) % 4096 = 0 := hcut.resolve_left (by omega)
      unfold secHits at hm hn
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm hn
      omega

/-- A retried write keeps what the `OsMeta` knows of the durable bytes, `ok`, the mappings and the
lower size bound. -/
theorem WReach.meta_keep {C : Nat → Nat → Nat → w64 → Prop} {m : OsMeta} {bs : List (w8 × Bool)}
    {off : Nat} {data : List w8} {nn : Nat} {m' : OsMeta} {bs' : List (w8 × Bool)}
    (h : WReach C m bs off data nn m' bs') :
    m'.dur = m.dur ∧ m'.dz = m.dz ∧ m'.ok = m.ok ∧ m'.maps = m.maps ∧ m'.lo = m.lo := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | step k nn' e _ _ _ _ _ ih => simpa [finMeta, pwPost, pwMeta] using ih

/-- **A page-aligned write of whole pages keeps the fresh sectors known**: each attempt ends on a
page boundary, or inside the file. -/
theorem WReach.fr_keep {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {data : List w8}
    {nn : Nat} {m' : OsMeta} {bs' : List (w8 × Bool)}
    (h : WReach NoTearCut m bs off data nn m' bs')
    (ha : off % 4096 = 0) (hd : data.length % 4096 = 0) (h64 : data.length < 2 ^ 64) :
    m'.fr = m.fr := by
  induction h with
  | refl => rfl
  | @step nn m1 bs1 k nn' e hR hnn hk hck hnn' ih =>
    have hdl : (data.drop nn).length = data.length - nn := List.length_drop
    obtain ⟨⟨-, hpc⟩, -⟩ := hck (by rw [hdl]; omega)
    show (pwPost m1 (off + nn) (data.drop nn).length k).fr = m.fr
    rw [← ih]
    simp only [pwPost, pwFr]
    split
    · rfl
    · rename_i hk0
      unfold frChange
      cases hf : m1.fr with
      | none => rfl
      | some p =>
        simp only [Option.map_some, Option.some.injEq]
        rw [if_pos]
        rw [hdl] at hpc
        by_cases hL : off + nn + k ≤ m1.size
        · left; omega
        · right
          refine ⟨.inr (by omega), ?_⟩
          have hal : (off + nn + k) % 4096 = 0 := by
            rcases hpc with h0 | h0 | h0
            · omega
            · rw [h0]; omega
            · omega
          unfold pageUp; omega

end Perennial
