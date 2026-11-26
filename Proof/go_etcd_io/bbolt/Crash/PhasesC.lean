/- Lean-first (no Rocq counterpart).

# bbolt's crash invariant: a write of any length (chunked)

`bDur_write_idle` and `wreach_inside` (`Crash/Phases.lean`) for the states a `WriteAt` past `maxRW`
(1 GiB) reaches, each attempt of the next chunk (`WReachC`, `wchunk`: `Spec/os/CrashStILLong.lean`),
for `os.File.WriteAt.specCrashILLong`.
-/
module

public import Proof.go_etcd_io.bbolt.Crash.Phases
public import Spec.os.CrashStILLong

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open go_etcd_io.bbolt.internal.common

section phasesC
variable [GooseExts]

/-- The states a chunked write inside the file reaches keep its size, bounds and crash sizes, and
the bytes out of its range (`wreach_inside` for `WReachC`). -/
theorem wreachC_inside {m : OsMeta} {bs : List ByteG} {off : Nat} {data : List w8} {nn : Nat}
    {m' : OsMeta} {bs' : List ByteG} (hR : WReachC m bs off data nn m' bs')
    (hin : off + data.length ≤ m.size) (hl : bs.length = m.size) (hlo : m.lo ≤ m.size)
    (hhi : m.size ≤ m.hi) :
    m'.size = m.size ∧ m'.lo = m.lo ∧ m'.hi = m.hi ∧ bs'.length = m.size ∧ nn ≤ data.length ∧
      (∀ b, (b < off ∨ off + data.length ≤ b) → bs'[b]? = bs[b]?) ∧ m'.xs = m.xs := by
  induction hR with
  | refl => exact ⟨rfl, rfl, rfl, hl, Nat.zero_le _, fun _ _ => rfl, rfl⟩
  | @step nn0 m0 bs0 k nn' n zs _ hnn hk hnn' _ _ _ ih =>
    obtain ⟨hs, hlo0, hhi0, hl0, -, hout, hxs0⟩ := ih
    have hd : (wchunk data nn0).length = min (data.length - nn0) 0x40000000 := wchunk_length data nn0
    have hpw : pwSize m0.size (off + nn0) k = m0.size := by unfold pwSize; split <;> omega
    refine ⟨by rw [pwPostK_size, hpw, hs], ?_, ?_, ?_, by omega, fun b hb => ?_,
      by rw [pwPostK_xs, if_pos (by rw [hd]; omega), hxs0]⟩
    · rw [pwPostK_lo, hd, hlo0, hs]; omega
    · rw [pwPostK_hi, hd, hhi0, hs]; omega
    · rw [finBytes_length (by omega) (by omega) (by omega), hpw, hs]
    · by_cases hbs : b < m.size
      · rw [finBytes_out (by omega) (by omega) (by omega) b (by omega) (by omega)]
        exact hout b hb
      · have hfl : (finBytes m0 bs0 (off + nn0) (wchunk data nn0) k n zs).length = m0.size := by
          rw [finBytes_length (by omega) (by omega) (by omega), hpw]
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **A write of unprotected bytes inside the file keeps the idle facts** (`Tx.write`'s dirty pages,
`commitFreelist`'s page: pages free for the committed state, not a meta slot), the crash sizes the
size alone (`XsOne`: `DB.grow` syncs its truncate first), in every state of `WReachC` (a write of
any length, in chunks of at most `maxRW`, `os.File.WriteAt.specCrashILLong`), idle and with the next
attempt's chunk in flight (`bDur_write_idle` for `WReachC`). -/
theorem bDur_write_idleC (a : BAbs) (ha : a.phase = .idle) (m : OsMeta) (bs : List ByteG)
    (fa fb off : Nat) (data : List w8) (h : BDur a ⟨m, bs, fa, fb, .idle⟩)
    (hin : off + data.length ≤ m.size)
    (hun : ∀ b, off ≤ b → b < off + data.length → 8192 ≤ b ∧ ¬ protData a.xcur a.cur b)
    (hone : XsOne m)
    (nn : Nat) (m' : OsMeta) (bs' : List ByteG) (hR : WReachC m bs off data nn m' bs') :
    BDur a ⟨m', bs', fa, fb, .idle⟩ ∧ (nn < data.length → ∀ t n,
      PwFresh m' bs' (off + nn) (wchunk data nn) n →
      BDur a ⟨m', bs', fa, fb, .write t (off + nn) (wchunk data nn) n⟩) := by
  simp only [bDur_idle_iff ha] at h ⊢
  obtain ⟨hW, hI⟩ := h
  have hl : bs.length = m.size := hW.1
  have hlo : m.lo ≤ m.size := hW.2.2.1
  have hhi : m.size ≤ m.hi := hW.2.2.2
  obtain ⟨hs, hlo', hhi', hl', hnn, hout, hxs'⟩ := wreachC_inside hR hin hl hlo hhi
  have hal : m.size % 4096 = 0 := hI.2.2.2.2.1
  obtain ⟨l, hxl, hla, -, -⟩ : XsAl ⟨m, bs, fa, fb, .idle⟩ := hI.2.2.2.2.2.2
  have hxl0 : m.xs = some l := hxl
  have hxa : ∀ busy : CBusy, (∀ t sz n, busy ≠ .trunc t sz n) →
      XsAl ⟨m', bs', fa, fb, busy⟩ := fun busy hnt =>
    ⟨l, by show m'.xs = _; rw [hxs']; exact hxl, hla, fun t sz n h => absurd h (hnt t sz n),
      fun _ _ _ _ _ x hx => by show x = m'.size; rw [hs]; exact hone l hxl0 x hx⟩
  have hprot : ∀ b, (b < 8192 ∨ protData a.xcur a.cur b) → b < off ∨ off + data.length ≤ b := by
    intro b hb
    apply Classical.byContradiction; intro hc
    have := hun b (by omega) (by omega)
    rcases hb with hb | hb
    · omega
    · exact this.2 hb
  have hbs : ∀ b v, (b < 8192 ∨ protData a.xcur a.cur b) → bs[b]? = some (durB v) →
      bs'[b]? = some (durB v) := fun b v hb h => by
    have h' : bs[b]? = some (durB v) := h
    rw [hout b (hprot b hb)]; exact h'
  have hd : (wchunk data nn).length = min (data.length - nn) 0x40000000 := wchunk_length data nn
  refine ⟨⟨⟨by show bs'.length = m'.size; rw [hs]; exact hl', trivial, by show m'.lo ≤ m'.size; omega,
      by show m'.size ≤ m'.hi; omega⟩,
    idleOk_mono hI (fun b v hb h => hbs b v hb h) (fun _ _ _ _ _ _ h => by cases h)
      (by show m.lo ≤ m'.lo; omega)
      (by show m'.size % 4096 = 0; rw [hs]; exact hal) (fun _ _ _ _ h => by cases h)
      (hxa _ (fun _ _ _ h => by cases h))⟩,
    fun hlt t n _ => ⟨⟨by show bs'.length = m'.size; rw [hs]; exact hl', by show off + nn ≤ m'.size; omega,
      by show m'.lo ≤ m'.size; omega, by show m'.size ≤ m'.hi; omega⟩,
    idleOk_mono hI (fun b v hb h => hbs b v hb h) (fun b hb t' off' data' n' he => by
        cases he; have := hprot b hb; rw [hd]; omega)
      (by show m.lo ≤ m'.lo; omega) (by show m'.size % 4096 = 0; rw [hs]; exact hal)
      (fun t' off' data' n' he => by
        cases he; show off + nn + (wchunk data nn).length ≤ m'.size; rw [hd]; omega)
      (hxa _ (fun _ _ _ h => by cases h))⟩⟩

end phasesC

end bbolt
end EtcdGrove
end Perennial
