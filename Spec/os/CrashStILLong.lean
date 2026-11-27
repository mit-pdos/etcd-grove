/-
The vocabulary of the long `WriteAt` (`wchunk`, `WReachC`: past `maxRW` (1 GiB) the model
(`TrustedCode/os.lean`'s `File.WriteAt.impl`, as Go's `poll.FD.Pwrite`) writes in chunks of at most
`maxRW` bytes, each attempt from where the last stopped) for `os.File.WriteAt.specCrashILLongR`
(`Spec/os/CrashStILR.lean`). (W3, 2026-11-26: the specs over `csInvI` that this file held were retired,
unused.) Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.CrashStIL
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial

open Fs

/-- The chunk an attempt of a `WriteAt` of `data` from `nn` writes: at most `maxRW` (1 GiB) bytes of
the rest. -/
def wchunk (data : List w8) (nn : Nat) : List w8 := (data.drop nn).take 0x40000000

theorem wchunk_length (data : List w8) (nn : Nat) :
    (wchunk data nn).length = min (data.length - nn) 0x40000000 := by
  simp only [wchunk, List.length_take, List.length_drop]; omega

/-- A write of at most `maxRW` bytes has one chunk, all of the rest. -/
theorem wchunk_short {data : List w8} (nn : Nat) (h : data.length ≤ 0x40000000) :
    wchunk data nn = data.drop nn :=
  List.take_of_length_le (by simp only [List.length_drop]; omega)

/-- The states a `WriteAt` of `data` at `off` reaches from `m`, `bs`, `nn` of the data's bytes
written, in chunks (`WReach` with each attempt of `wchunk data nn`). -/
inductive WReachC (m : OsMeta) (bs : List ByteG) (off : Nat) (data : List w8) :
    Nat → OsMeta → List ByteG → Prop
  | refl : WReachC m bs off data 0 m bs
  | step {nn : Nat} {m' : OsMeta} {bs' : List ByteG} (k nn' n : Nat) (zs : List Cands) :
      WReachC m bs off data nn m' bs' → nn < data.length → k ≤ (wchunk data nn).length →
      (nn' = nn + k ∨ nn' = nn) → zs.length = pwSize m'.size (off + nn) k - m'.size → ZsOk m' zs →
      PwFresh m' bs' (off + nn) (wchunk data nn) n →
      WReachC m bs off data nn'
        (pwPostK true m' (off + nn) (wchunk data nn) k n) (finBytes m' bs' (off + nn) (wchunk data nn) k n zs)

/-- A state the loop reached has the start's cut (no attempt syncs). -/
theorem WReachC.cut {m : OsMeta} {bs : List ByteG} {off : Nat} {data : List w8} {nn : Nat}
    {m' : OsMeta} {bs' : List ByteG} (h : WReachC m bs off data nn m' bs') : m'.cut = m.cut := by
  induction h with
  | refl => rfl
  | step _ _ _ _ _ _ _ _ _ _ _ ih => simp [pwPostK, pwPost, OsMeta.announce, ih]

/-- **A write inside the file keeps its size and mappings**, in every state the loop reaches: the
bytes stay all of the file's, and at most all of the data is written. -/
theorem WReachC.inside {m : OsMeta} {bs : List ByteG} {off : Nat} {data : List w8} {nn : Nat}
    {m' : OsMeta} {bs' : List ByteG} (h : WReachC m bs off data nn m' bs')
    (hl : bs.length = m.size) (hin : off + data.length ≤ m.size) :
    m'.size = m.size ∧ m'.maps = m.maps ∧ bs'.length = m'.size ∧ nn ≤ data.length := by
  induction h with
  | refl => exact ⟨rfl, rfl, hl, Nat.zero_le _⟩
  | @step nn0 m0 bs0 k nn' n zs _ hnn hk hn' _ _ _ ih =>
    obtain ⟨hs, hm, hb, -⟩ := ih
    have hkl : k ≤ data.length - nn0 := by rw [wchunk_length] at hk; omega
    have hps : pwSize m0.size (off + nn0) k = m0.size := by unfold pwSize; split <;> omega
    refine ⟨?_, ?_, ?_, by omega⟩
    · show pwSize m0.size (off + nn0) k = m.size
      rw [hps, hs]
    · simp only [pwPostK, pwPost, announce_maps, hm]
    · rw [finBytes_length hb (by omega) hk]; rfl

namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

end spec

end EtcdGrove
end Perennial
