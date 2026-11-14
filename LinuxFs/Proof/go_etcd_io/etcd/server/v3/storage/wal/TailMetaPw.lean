/- Lean-first (no Rocq counterpart).

# The handle's tail facts across the writes of a `WriteAt` past the size (W6; W6 log, twenty-fifth session)

The writer past the preallocated size writes in attempts (`pwrite`s of chunks, short writes, `EINTR`
retries), all ending at or below the `WriteAt`'s end `E`; each leaves the tail as `pwPostK true` (the
candidates announced past the size kept). `TailZ` (the zeros known past the size, the page cache zero to
the end of their page) does not hold between them: a short write past the zeros known moves them to its
data's end without raising `cz`. It holds again after the last attempt, which writes all of its data up to
`E` (`Fs.pwCz`). Between them, `TailZE m E`: `TailZ` but for the page fact, which may wait for a write up to
`E`. `TailMetaL` is `TailMetaW` with `TailZE`.

* `TailZE`, `TailZ.tailZE`, `TailZE.pc_isSome`, `TailZE.pwK` (with `TailZ` after a complete write to `E`);
* `PastZ.pwK`, `LoWr.pwK`;
* `TailMetaL`, `TailMetaW.tailMetaL`, `TailMetaL.fin`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailStepW

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

theorem pwSize_ge_off {sz off k : Nat} (h : off ≤ sz) :
    sz ≤ pwSize sz off k ∧ off + k ≤ pwSize sz off k := by
  unfold pwSize; split <;> omega

theorem pwSize_le_max' {sz off k n : Nat} (hk : k ≤ n) : pwSize sz off k ≤ max sz (off + n) := by
  unfold pwSize; split <;> omega

/-- **`TailZ` during the writes of a `WriteAt` ending at `E`**: the zeros known from `z` on, at least the
size, the candidates of the bytes between known, and the page cache zero to the end of `z`'s page or
`z` at most `E` (the last attempt, writing all of its data up to `E`, raises `cz` there). -/
def TailZE (m : OsMeta) (E : Nat) : Prop :=
  ∃ z, m.zf = some z ∧ m.size ≤ z ∧ (pageEnd z ≤ max m.size m.cz ∨ z ≤ E) ∧
    ∀ b, m.size ≤ b → b < z → ∃ c, m.tc !! b = some c

theorem TailZ.tailZE {m : OsMeta} (h : TailZ m) (E : Nat) : TailZE m E := by
  obtain ⟨z, h1, h2, h3, h4⟩ := h
  exact ⟨z, h1, h2, .inl h3, h4⟩

theorem TailZE.ge {m : OsMeta} {E : Nat} (h : TailZE m E) : ∀ z, m.zf = some z → m.size ≤ z := by
  obtain ⟨z0, h0, h1, -⟩ := h
  intro z hz; rw [h0, Option.some.injEq] at hz; subst hz; exact h1

/-- **`TailZE` knows every byte past the size.** -/
theorem TailZE.pc_isSome {m : OsMeta} {E : Nat} (h : TailZE m E) {b : Nat} (hb : m.size ≤ b) :
    (m.pc b).isSome := by
  obtain ⟨z, hz, -, -, htc⟩ := h
  unfold OsMeta.pc
  by_cases hbz : b < z
  · obtain ⟨c, hc⟩ := htc b hb hbz
    rw [hc]; rfl
  · cases m.tc !! b with
    | some c => rfl
    | none => rw [hz]; simp only; rw [if_pos (by omega)]; rfl

theorem pwPostK_zf (m : OsMeta) (off : Nat) (data : List w8) (k n : Nat) :
    (pwPostK true m off data k n).zf =
      m.zf.map (fun z => if min off m.size < off + data.length then max z (off + data.length) else z) := rfl

theorem pwPostK_cz (m : OsMeta) (off : Nat) (data : List w8) (k n : Nat) :
    (pwPostK true m off data k n).cz = pwCz m off data.length k := rfl

theorem pwPostK_tc (m : OsMeta) (off : Nat) (data : List w8) (k n : Nat) :
    (pwPostK true m off data k n).tc = pwTail m off data n := rfl

theorem pwPostK_maps (m : OsMeta) (off : Nat) (data : List w8) (k n : Nat) :
    (pwPostK true m off data k n).maps = m.maps := by
  simp [pwPostK, pwPost]

/-- **A write from inside the file, ending at or below `E`, keeps `TailZE`**; one writing all of its data
up to `E` gives `TailZ`. -/
theorem TailZE.pwK {m : OsMeta} {off : Nat} {data : List w8} {k n E : Nat} (h : TailZE m E)
    (hoff : off ≤ m.size) (hd : 0 < data.length) (hE : off + data.length ≤ E) (hk : k ≤ data.length) :
    TailZE (pwPostK true m off data k n) E ∧
      (k = data.length → off + data.length = E → TailZ (pwPostK true m off data k n)) := by
  have hpc := fun b (hb : m.size ≤ b) => h.pc_isSome hb
  obtain ⟨z, hz, h1, h2, h3⟩ := h
  have hmin : min off m.size = off := Nat.min_eq_left hoff
  have hzf : (pwPostK true m off data k n).zf = some (max z (off + data.length)) := by
    rw [pwPostK_zf, hz, hmin]; simp only [Option.map_some, Option.some.injEq]
    rw [if_pos (by omega)]
  have hsz : (pwPostK true m off data k n).size = pwSize m.size off k := pwPostK_size _ _ _ _ _
  have hps1 := pwSize_ge_off (k := k) hoff
  have hps2 := pwSize_le_max' (sz := m.size) (off := off) hk
  have hcz : m.cz ≤ (pwPostK true m off data k n).cz := by rw [pwPostK_cz]; exact le_pwCz _ _ _ _
  have htc : ∀ b, pwSize m.size off k ≤ b → b < max z (off + data.length) →
      ∃ c, (pwPostK true m off data k n).tc !! b = some c := by
    intro b hb1 hb2
    rw [pwPostK_tc, pwTail_lookup]
    by_cases hr : inRange off (off + data.length) b = true
    · rw [if_pos hr, if_pos (by omega)]
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (hpc b (by omega))
      rw [hc]; exact ⟨_, rfl⟩
    · rw [if_neg hr]
      simp only [inRange, Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_lt] at hr
      exact h3 b (by omega) (by have := hr (by omega); omega)
  refine ⟨⟨max z (off + data.length), hzf, by rw [hsz]; omega, ?_, by rw [hsz]; exact htc⟩, ?_⟩
  · rcases h2 with h2 | h2
    · by_cases hzo : off + data.length ≤ z
      · left; rw [hsz, show max z (off + data.length) = z by omega]; omega
      · right; omega
    · right; omega
  · intro hkd hEe
    refine ⟨max z (off + data.length), hzf, by rw [hsz]; omega, ?_, by rw [hsz]; exact htc⟩
    by_cases hzo : z ≤ off + data.length
    · have hr : pageEnd (off + data.length) ≤ pwCz m off data.length k := by
        rw [hkd]; exact pwCz_raise hz hd hzo
      rw [pwPostK_cz, show max z (off + data.length) = off + data.length by omega]; omega
    · rcases h2 with h2 | h2
      · rw [hsz, show max z (off + data.length) = z by omega]; omega
      · omega

/-- **A write keeps `PastZ`**, the candidates past the size kept (`pwPostK true`: it raises `hi` over the
bytes it announces). -/
theorem PastZ.pwK {m : OsMeta} (h : PastZ m) (off : Nat) (data : List w8) (k n : Nat) :
    PastZ (pwPostK true m off data k n) := by
  refine h.of_pc (by rw [pwPostK_hi]; omega) (by rw [pwPostK_rz]; exact fun _ h => h)
    fun b c hb hc => ?_
  rw [pwPostK_hi] at hb
  cases ht : (pwPostK true m off data k n).tc !! b with
  | none => exact .inr (pc_zf_cases ht hc)
  | some c1 =>
    have ht' : (pwPostK true m off data k n).tc !! b = m.tc !! b := by
      rw [pwPostK_tc, pwTail_lookup, if_neg (by simp only [inRange, Bool.and_eq_true,
        decide_eq_true_eq, not_and, Nat.not_lt]; omega)]
    left
    unfold OsMeta.pc at hc ⊢
    rw [ht] at hc; rw [← ht', ht]; exact hc

/-- **A write ending at or below `E` keeps `LoWr … E`**: no window opened (inside the size of an exact
tail), or the least crash size at most the size, below the write's end. -/
theorem LoWr.pwK {m : OsMeta} {off : Nat} {data : List w8} {k n E : Nat} (h : LoWr m E)
    (hoff : off ≤ m.size) (hE : off + data.length ≤ E) (hk : k ≤ data.length) :
    LoWr (pwPostK true m off data k n) E := by
  have hlo := pwPostK_lo m off data k n
  have hhi := pwPostK_hi m off data k n
  have hsz : (pwPostK true m off data k n).size = pwSize m.size off k := pwPostK_size _ _ _ _ _
  have hps1 := pwSize_ge_off (k := k) hoff
  have hps2 := pwSize_le_max' (sz := m.size) (off := off) hk
  rcases h with ⟨h1, h2⟩ | h
  · by_cases hin : off + data.length ≤ m.size
    · left; rw [hlo, hhi, hsz]; omega
    · right; rw [hlo]; omega
  · right; rw [hlo]; omega

/-- **What the program knows of the tail between the attempts of a `WriteAt` ending at `E`**: `TailMetaW`
with `TailZE`. -/
def TailMetaL (m : OsMeta) (bs : List ByteG) (E : Nat) : Prop :=
  bs.length = m.size ∧ m.maps = ∅ ∧ TailZE m E ∧ m.lo ≤ m.size ∧ m.size ≤ m.hi ∧ PastZ m

theorem TailMetaW.tailMetaL {m : OsMeta} {bs : List ByteG} (h : TailMetaW m bs) (E : Nat) :
    TailMetaL m bs E :=
  ⟨h.1, h.2.1, h.2.2.1.tailZE E, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- **An attempt's finish keeps `TailMetaL`**; the last, writing all of its data up to `E`, gives
`TailMetaW`. -/
theorem TailMetaL.fin {m : OsMeta} {bs : List ByteG} {off : Nat} {data : List w8} {k n E : Nat}
    {zs : List Cands} (h : TailMetaL m bs E) (hoff : off ≤ m.size) (hd : 0 < data.length)
    (hE : off + data.length ≤ E) (hk : k ≤ data.length) :
    TailMetaL (pwPostK true m off data k n) (finBytes m bs off data k n zs) E ∧
      (k = data.length → off + data.length = E →
        TailMetaW (pwPostK true m off data k n) (finBytes m bs off data k n zs)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hz := h3.pwK (n := n) hoff hd hE hk
  have hl : (finBytes m bs off data k n zs).length = (pwPostK true m off data k n).size := by
    rw [pwPostK_size]; exact finBytes_length h1 hoff hk
  have hps1 := pwSize_ge_off (k := k) hoff
  have hps2 := pwSize_le_max' (sz := m.size) (off := off) hk
  have hlo : (pwPostK true m off data k n).lo ≤ (pwPostK true m off data k n).size := by
    rw [pwPostK_lo, pwPostK_size]; omega
  have hhi : (pwPostK true m off data k n).size ≤ (pwPostK true m off data k n).hi := by
    rw [pwPostK_hi, pwPostK_size]; omega
  have hmp : (pwPostK true m off data k n).maps = ∅ := by rw [pwPostK_maps]; exact h2
  exact ⟨⟨hl, hmp, hz.1, hlo, hhi, h6.pwK _ _ _ _⟩,
    fun hk1 hk2 => ⟨hl, hmp, hz.2 hk1 hk2, hlo, hhi, h6.pwK _ _ _ _⟩⟩

end pure

end WalFs
end EtcdGrove
end Perennial

end
