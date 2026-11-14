/- Lean-first (no Rocq counterpart).

# The cleanup's broken name (W4 of `notes/wal-fsext-plan.md`, twenty-sixth session)

`cleanupWAL` renames the WAL directory `r/nm` to `fmt.Sprintf("%s.broken.%v", r/nm, s)`, `s` the
timestamp (`time.Time.Format.specBroken`: digits, `.` and `-`; `fmt.SprintfBroken.spec`): the name
`nm.broken.<s>` in the area directory `r`, a valid name (`NameOk`) whatever its length.
-/
module

public import LinuxFs.Spec.time.Time__FormatBroken
public import GooseLang.Ext.Fs.TreeLemmas

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs

/-- The broken name of the WAL name `nm` at the timestamp `s`. -/
def brokenName (nm s : GoString) : GoString := nm ++ go!".broken." ++ s

/-- The cleanup's target path is the broken name in the area. -/
theorem child_brokenName (r nm s : GoString) :
    child r nm ++ go!".broken." ++ s = child r (brokenName nm s) := by
  simp [child, brokenName, List.append_assoc]

/-- A broken name is valid: `nm`'s bytes, `.broken.` and the timestamp's hold no `/` nor NUL, and it
is longer than `..`. -/
theorem brokenName_nameOk {nm s : GoString} (hnm : NameOk nm) (hs : ∀ c ∈ s, c ∈ timeStampChars) :
    NameOk (brokenName nm s) := by
  obtain ⟨hne, -, -, hsl, hnul⟩ := hnm
  have hlen : 2 < (brokenName nm s).length := by
    have : 0 < nm.length := List.length_pos_iff.2 hne
    simp [brokenName]; omega
  refine ⟨fun h => by rw [h] at hlen; simp at hlen, fun h => by rw [h] at hlen; simp at hlen,
    fun h => by rw [h] at hlen; simp at hlen, ?_, ?_⟩
  · intro h
    simp only [brokenName, List.mem_append] at h
    rcases h with (h | h) | h
    · exact hsl h
    · revert h; decide
    · have := hs _ h; revert this; decide
  · intro h
    simp only [brokenName, List.mem_append] at h
    rcases h with (h | h) | h
    · exact hnul h
    · revert h; decide
    · have := hs _ h; revert this; decide

end WalFs
end EtcdGrove
end Perennial

end
