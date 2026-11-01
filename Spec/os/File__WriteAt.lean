/-
`f.WriteAt(b, off)` on an open `*os.File` (this repository's `os`, project `bboltfs`), for a
non-negative offset and a non-empty `b` of at most `maxRW` (1 GiB) bytes, so that Go's
`poll.FD.Pwrite` makes one `pwrite(2)` per attempt (retried on `EINTR`). The model
(`TrustedCode/os.lean`) makes the extension's two steps per attempt (`wp_osPWriteStart`,
`wp_osPWriteFinish`), so the spec takes what they take: the fd, writable; a fraction `q` of the
file's `OsMeta` `m`, all of it if the write may extend the file; the bytes the write may change
below the size, `[min off size, min (off + n) size)`, whole; and the client's halves of the cells
of every mapping over `[min off size, off + n)`.

After it, the file is as a write of the first `j` bytes of `b` left it (each attempt rewrites
from the start, and a failed one may have written a prefix): its size `pwSize m.size off j`, the
bytes of the range `pwBytes` (the zero gap past the old end, then `b`'s first `j` bytes, then the
old bytes), not clean. On success `j = n` and the result is `(n, nil)`; on failure, `(0, err)`
with a non-nil `err`. Proved in `Proof/os/File__WriteAt.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.WriteAt.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (q : Qp) (m : OsMeta)
    (xs : List (w8 × Bool)),
  d.writable = true → 0 ≤ off.toInt → 0 < data.length → data.length ≤ 0x40000000 →
  xs.length = min (off.toNat + data.length) m.size - min off.toNat m.size →
  (m.size < off.toNat + data.length → q = 1) →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦*{dqs} data ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.path (DFrac.own q) (some m) ∗
      osBytes (GF := GF) d.path (min off.toNat m.size) (DFrac.own 1) xs ∗
      mcellsAny (GF := GF) m.maps (min off.toNat m.size) (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      ∃ (j : Nat) (ys : List (w8 × Bool)) (h : Nat),
        ⌜j ≤ data.length ∧
          ys.map Prod.fst = (pwBytes m.size off.toNat data j xs).map Prod.fst ∧ m.hi ≤ h ∧
          ((j = data.length ∧ n = W64 data.length ∧ err = interface.nil) ∨
           (n = W64 0 ∧ err ≠ interface.nil))⌝ ∗
        osMeta d.path (DFrac.own q) (some { m with size := pwSize m.size off.toNat j, hi := h }) ∗
        osBytes d.path (min off.toNat m.size) (DFrac.own 1) ys ∗
        mcellsAny m.maps (min off.toNat m.size) (off.toNat + data.length) }}

end spec

end EtcdGrove
end Perennial
