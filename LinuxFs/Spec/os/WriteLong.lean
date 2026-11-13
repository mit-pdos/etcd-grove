/-
`f.WriteAt(b, off)` on an open `*os.File` for a non-empty `b` of **any** length (`File__WriteAt.lean`'s
spec takes at most `maxRW`, 1 GiB, for which Go's `poll.FD.Pwrite` makes one `pwrite(2)` per attempt):
past 1 GiB, `Pwrite` (and the model, `TrustedCode/os.lean`'s `File.WriteAt.impl`) writes in chunks of
at most `maxRW` bytes from where the last attempt stopped, each attempt announcing only its chunk.
The pre is `File__WriteAt.lean`'s, with the crash low bound of the size at most the size
(`m.lo ≤ m.size`, which every file's `MetaOk` has: `lo ≤ sizeLo ≤ size`), so that the chunks'
announcements compose into one.

After it, the file is as a write of the first `j` bytes of `b` that announced its first `A`
(`j ≤ A ≤ len(b)`) left it: its `OsMeta` `pwPost m off A j`, its bytes `os.PwOutA` (`os.PwOut`
where only the first `A` bytes have the data's byte among their candidates; the others keep their
old ones). On success `j = A = len(b)` and the result is `(len(b), nil)`, as `File__WriteAt.lean`
says; on failure `(0, err)`. When `len(b) ≤ maxRW` the one chunk is all of `b`: `A = len(b)`.
`j` is a page cut of the write (`PwCut`). WAL W6 (2026-11-13, `wal-bridge`); proved in
`Proof/os/WriteLong.lean`. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.Base
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial

namespace os

/-- The bytes `ys` from `off` on after a `WriteAt` of `data` at `off` that wrote its first `j`
bytes and announced its first `A` (in chunks), over a file of `OsMeta` `m` whose bytes there were
`xs`: `PwOut`, except that only the bytes below `A` are sure to have the data's byte among their
candidates (`extra ≠ []`). -/
def PwOutA (m : Fs.OsMeta) (off : Nat) (data : List w8) (A j : Nat) (xs ys : List Fs.ByteG) : Prop :=
  ys.length = min (off + data.length) (Fs.pwSize m.size off j) - off ∧
  ∀ i (hi : i < ys.length), ys[i].1 = Fs.pwByte off data j xs (off + i) ∧
    ∃ c0 extra, ys[i].2 = c0 ++ extra ∧ (i < A → extra ≠ []) ∧
      (∀ q ∈ extra, q.1 = data.getD i 0) ∧ ∀ (h : i < xs.length), c0 = xs[i].2

end os

namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.WriteAt.specLong : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG),
  d.writable = true → 0 ≤ off.toInt → off.toNat ≤ m.size → off.toNat + data.length < 2 ^ 63 →
  0 < data.length → m.lo ≤ m.size →
  xs.length = min (off.toNat + data.length) m.size - off.toNat →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦*{dqs} data ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
      osBytes (GF := GF) d.ino (off.toNat) (DFrac.own 1) xs ∗
      mcellsAny (GF := GF) m.maps (off.toNat) (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      ∃ (j A : Nat) (ys : List ByteG),
        ⌜j ≤ A ∧ A ≤ data.length ∧ (data.length ≤ 0x40000000 → A = data.length) ∧
          os.PwOutA m off.toNat data A j xs ys ∧ PwCut off.toNat data.length j ∧
          ((j = data.length ∧ n = W64 data.length ∧ err = interface.nil) ∨
           (n = W64 0 ∧ err ≠ interface.nil))⌝ ∗
        osMeta d.ino (DFrac.own 1) (pwPost m off.toNat A j) ∗
        osBytes d.ino (off.toNat) (DFrac.own 1) ys ∗
        mcellsAny m.maps (off.toNat) (off.toNat + data.length) ∗
      fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
