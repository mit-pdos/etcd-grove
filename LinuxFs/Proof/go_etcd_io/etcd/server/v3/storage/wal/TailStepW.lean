/- Lean-first (no Rocq counterpart).

# A `pwrite` step on the tail in a resize window or past the size (W6, pure; W6 log, twenty-third session)

The writer past the preallocated size (a `Save` crossing `SegmentSizeBytes`) and the writes in a resize
window (`cut`'s flush after its truncate, the writes after a write past the size) change the last
segment's ghost as `TailStepPure.lean`'s steps do, but the tail is not exact before or after: the
layout's `OsMeta` of a write in flight is `wrMeta` (the candidates announced past the size, `pwTail`),
its finish `pwPostK true`. Their crash condition is `crashOkW_tailW` (`TailCrashW.lean`) from the two
layouts' static relations; here the pieces of those.

* `wrMeta_pc_ge`: what `wrMeta` knows past the size.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrashW

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- **What a write's layout `OsMeta` knows past the size** (`wrMeta`; W6 log, twenty-third session, for the
writer past the size): in the written range, what `m` knew with the data's byte stamped `n` appended
(`pwTail`); past it, what `m` knew (the zeros known moved to the write's end only over the range). -/
theorem wrMeta_pc_ge {m : OsMeta} {off : Nat} {data : List w8} {n b : Nat} (hoff : off ≤ m.size)
    (hb : m.size ≤ b) :
    (wrMeta m off data n).pc b = if off ≤ b ∧ b < off + data.length then
      (m.pc b).map (· ++ [(data.getD (b - off) 0, n)]) else m.pc b := by
  have htc : (wrMeta m off data n).tc !! b = if inRange off (off + data.length) b then
      (m.pc b).map (· ++ [(data.getD (b - off) 0, n)]) else m.tc !! b := by
    show pwTail m off data n !! b = _
    rw [pwTail_lookup]
    by_cases hr : inRange off (off + data.length) b = true
    · rw [if_pos hr, if_pos hr, if_pos hb]
    · rw [if_neg hr, if_neg hr]
  have hzf : (wrMeta m off data n).zf = m.zf.map
      (fun z => if min off m.size < off + data.length then max z (off + data.length) else z) := by
    rw [wrMeta_zf]; unfold cfMeta; rw [announce_zf]
  have hmin : min off m.size = off := Nat.min_eq_left hoff
  rw [hmin] at hzf
  by_cases hin : off ≤ b ∧ b < off + data.length
  · rw [if_pos hin]
    have hr : inRange off (off + data.length) b = true := by simp [inRange, hin.1, hin.2]
    rw [hr, if_pos rfl] at htc
    cases hp : m.pc b with
    | some c =>
      rw [hp] at htc
      unfold OsMeta.pc; rw [htc]; rfl
    | none =>
      rw [hp] at htc
      unfold OsMeta.pc; rw [htc, hzf]
      simp only [Option.map_none]
      cases hz : m.zf with
      | none => rfl
      | some z =>
        simp only [Option.map_some]
        rw [if_pos (show off < off + data.length by omega),
          if_neg (show ¬ max z (off + data.length) ≤ b by omega)]
  · rw [if_neg hin]
    have hr : inRange off (off + data.length) b = false := by
      simp only [inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    rw [hr] at htc
    simp only [Bool.false_eq_true, ite_false] at htc
    unfold OsMeta.pc; rw [htc, hzf]
    cases m.tc !! b with
    | some c => rfl
    | none =>
      cases hz : m.zf with
      | none => rfl
      | some z =>
        simp only [Option.map_some]
        have hb' : off + data.length ≤ b := by omega
        split
        · by_cases hzb : z ≤ b
          · rw [if_pos (by omega), if_pos hzb]
          · rw [if_neg (by omega), if_neg hzb]
        · rfl

end pure

end WalFs
end EtcdGrove
end Perennial

end
