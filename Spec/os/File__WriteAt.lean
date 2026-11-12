/-
`f.WriteAt(b, off)` on an open `*os.File` (this repository's `os`, project `bboltfs`), for a
non-negative offset and a non-empty `b` of at most `maxRW` (1 GiB) bytes, so that Go's
`poll.FD.Pwrite` makes one `pwrite(2)` per attempt (retried on `EINTR`). The model
(`TrustedCode/os.lean`) makes the extension's two steps per attempt (`wp_osPWriteStart`,
`wp_osPWriteFinish`), so the spec takes what they take: the fd, writable; the whole of the
file's `OsMeta` `m`; the bytes the write may change
below the size, `[min off size, min (off + n) size)`, whole; and the client's halves of the cells
of every mapping over `[min off size, off + n)`.

After it, the file is as a write of the first `j` bytes of `b` left it (an attempt that wrote
short is followed by one from where it stopped, and a failed one may have written a prefix): its
`OsMeta` as the write announced it (`pwPost`: the size `pwSize m.size off j`, the range not
durable, a crash bound to the end of the write), and the bytes of the range (`os.PwOut`): their
values, the zero gap past the old end, then `b`'s first `j` bytes, then the old bytes; their
candidates, the old ones, then the data's byte (once per attempt that announced it). On success
`j = n` and the result is `(n, nil)`; on failure, `(0, err)` with a non-nil `err`, its `Error()` a
`fmt`-printable string (`fmtErrorOkOrNil`). Whatever the result, `j` is a page cut of the write
(`PwCut`: `0`, `n`, or ending on a 4096-byte page boundary of the file; the page-cut rule of each
`pwrite`, carried through Go's retries), so one aligned page lands whole or not at all. Proved in `Proof/os/File__WriteAt.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.Base
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
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
abbrev os.File.WriteAt.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG),
  d.writable = true → 0 ≤ off.toInt → off.toNat ≤ m.size → off.toNat + data.length < 2 ^ 63 →
  0 < data.length → data.length ≤ 0x40000000 →
  xs.length = min (off.toNat + data.length) m.size - off.toNat →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦*{dqs} data ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
      osBytes (GF := GF) d.ino (off.toNat) (DFrac.own 1) xs ∗
      mcellsAny (GF := GF) m.maps (off.toNat) (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      ∃ (j : Nat) (ys : List ByteG),
        ⌜j ≤ data.length ∧ os.PwOut m off.toNat data j xs ys ∧ PwCut off.toNat data.length j ∧
          ((j = data.length ∧ n = W64 data.length ∧ err = interface.nil) ∨
           (n = W64 0 ∧ err ≠ interface.nil))⌝ ∗
        osMeta d.ino (DFrac.own 1) (pwPost m off.toNat data.length j) ∗
        osBytes d.ino (off.toNat) (DFrac.own 1) ys ∗
        mcellsAny m.maps (off.toNat) (off.toNat + data.length) ∗
      fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
