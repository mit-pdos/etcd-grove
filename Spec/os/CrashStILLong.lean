/-
Two cases `Spec/os/CrashStIL.lean`'s specs leave out. `os.File.WriteAt.specCrashILLong`:
`os.File.WriteAt.specCrashIL` for a write of any length inside the file:
past `maxRW` (1 GiB) the model (`TrustedCode/os.lean`'s `File.WriteAt.impl`, as Go's `poll.FD.Pwrite`)
writes in chunks of at most `maxRW` bytes, each attempt (`pwrite(2)`, the extension's
`PWriteStart`/`PWriteFinish`) from where the last stopped, of the next chunk (`wchunk`). The states the
loop reaches are `WReachC`'s: `WReach`'s, each attempt of the chunk from `nn` instead of all the rest
of the data (the same when the data is at most `maxRW`, `wchunk_short`).
`os.File.Truncate.specCrashILBig`: a growing `Truncate` to a target past `maxBytes`, which fails with
the file as its first attempt announced it. Proved in `Proof/os/CrashStILLong.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.os.CrashStIL

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

variable [os.Assumptions] in
/-- **`os.File.WriteAt.specCrashIL` for data of any length**: the model's loop writes in chunks of at
most `maxRW` (1 GiB, `wchunk`), each attempt from where the last stopped (`WReachC`); the caller
shows `Ok` of every state the loop may pass through, idle and with an attempt's chunk in flight. -/
abbrev os.File.WriteAt.specCrashILLong : Prop :=
  ∀ {A : Type} [Pos.Countable A] (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (data : List w8) (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) (m : OsMeta) (bs xs : List ByteG),
  d.ino = i → d.writable = true → 0 ≤ off.toInt → off.toNat + data.length ≤ m.size →
  off.toNat + data.length ≤ maxBytes → off.toNat + data.length < 2 ^ 63 → 0 < data.length →
  xs.length = data.length → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ nn m' bs', WReachC m bs off.toNat data nn m' bs' →
    Ok a ⟨m', bs', 0, 0, .idle⟩ ∧ (nn < data.length → ∀ t n,
      PwFresh m' bs' (off.toNat + nn) (wchunk data nn) n →
      Ok a ⟨m', bs', 0, 0, .write t (off.toNat + nn) (wchunk data nn) n⟩)) →
  {{ osInv (GF := GF) ∗ csInvI (GF := GF) N i γ γa γc Ok ∗ os.ownFile (GF := GF) f fd name dqf ∗
      sl ↦*{dqs} data ∗ osFd (GF := GF) fd dq d ∗
      csOwnIL (GF := GF) i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
      osBytes (GF := GF) i off.toNat (DFrac.own (1 : Qp).half) xs ∗
      mcellsAny (GF := GF) m.maps off.toNat (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      mcellsAny m.maps off.toNat (off.toNat + data.length) ∗
      ∃ (nn : Nat) (m' : OsMeta) (bs' : List ByteG),
        ⌜xs = (bs.drop off.toNat).take data.length ∧ WReachC m bs off.toNat data nn m' bs' ∧
          ((n = W64 data.length ∧ err = interface.nil ∧ nn = data.length ∧
              m'.size = m.size ∧ m'.maps = m.maps ∧
              ∀ i < data.length, (bs'[off.toNat + i]?).map Prod.fst = data[i]?) ∨
           (n = W64 0 ∧ err ≠ interface.nil ∧ ¬ FsNoErr))⌝ ∗
        csOwnIL i γ γa ⟨m', bs', 0, 0, .idle⟩ a ∗
        osBytes i off.toNat (DFrac.own (1 : Qp).half) ((bs'.drop off.toNat).take data.length) }}

variable [os.Assumptions] in
/-- **`os.File.Truncate.specCrashIL` for a target past `maxBytes`**: the model's `ftruncate` fails
(`EFBIG`, `FtruncateFinish` of `Impl.lean`, whatever the file system's errors), retried on `EINTR`;
the file as the first attempt announced it (`TReach.ann`: the bytes it announced past the size keep
their new candidates), of which, and of the start and the attempts in flight, the caller shows
`Ok`. -/
abbrev os.File.Truncate.specCrashILBig : Prop :=
  ∀ {A : Type} [Pos.Countable A] (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64)
    (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop)
    (a : A) (m : OsMeta) (bs : List ByteG),
  d.ino = i → 0 ≤ fd.toInt → d.writable = true → 0 ≤ sz.toInt → m.size ≤ sz.toNat →
  maxBytes < sz.toNat → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ m', (m' = m ∨ m' = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat) →
    Ok a ⟨m', bs, 0, 0, .idle⟩ ∧ ∀ t n, Ok a ⟨m', bs, 0, 0, .trunc t sz.toNat n⟩) →
  {{ osInv (GF := GF) ∗ csInvI (GF := GF) N i γ γa γc Ok ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗ csOwnIL (GF := GF) i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
      mcellsAny (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ⌜err ≠ interface.nil⌝ ∗
      csOwnIL i γ γa ⟨m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat,
        bs, 0, 0, .idle⟩ a ∗
      mcellsAny m.maps m.size (rsHi true m.size sz.toNat) }}

end spec

end EtcdGrove
end Perennial
