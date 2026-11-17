/-
`f.WriteAt(b, off)` on an open `*os.File` with no I/O error (`File.WriteAt.spec` and `specExt` over
a semantics whose steps satisfy **no I/O error on chosen files**, `FsStepSat (NoIoErr Sio)`; every
inode covered), for a write ending by `maxBytes` (ext4's `s_maxbytes`, where `pwrite` fails with
`EFBIG` whatever the premise): `(len(b), nil)`, every byte written. A short `pwrite` is still
possible (the model's errno-0 short count) and is followed by another attempt.

* `os.File.WriteAt.specNoErr`: `spec` (inside the file, at most 1 GiB) with `j = len(b)`: the
  `OsMeta` `pwPost m off n n`, the bytes `os.PwOut … n` (bbolt's `init` and `writeMeta`).
* `os.File.WriteAt.specExtNoErr`: `specExt` (anywhere, any length) with `j = a = E = len(b)`: the
  `OsMeta` `os.pwPostE m off n n n` (`= pwPost m off n n`, `pwPostE_self`), the values `pwValsG … n`
  (bbolt's `Tx.write`).

Proved in `Proof/os/File__WriteAtNoErr.lean`. Lean-first.
-/
module

public import Spec.os.File__WriteAt
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

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
abbrev os.File.WriteAt.specNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG),
  d.writable = true → 0 ≤ off.toInt → off.toNat ≤ m.size → off.toNat + data.length ≤ maxBytes →
  0 < data.length → data.length ≤ 0x40000000 →
  xs.length = min (off.toNat + data.length) m.size - off.toNat →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦*{dqs} data ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
      osBytes (GF := GF) d.ino (off.toNat) (DFrac.own 1) xs ∗
      mcellsAny (GF := GF) m.maps (off.toNat) (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ RET (PairV #(W64 data.length) #(interface.nil : GoInterface));
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      ∃ ys : List ByteG, ⌜os.PwOut m off.toNat data data.length xs ys⌝ ∗
        osMeta d.ino (DFrac.own 1) (pwPost m off.toNat data.length data.length) ∗
        osBytes d.ino (off.toNat) (DFrac.own 1) ys ∗
        mcellsAny m.maps (off.toNat) (off.toNat + data.length) }}

/-- See the file header. -/
abbrev os.File.WriteAt.specExtNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG),
  d.writable = true → 0 ≤ off.toInt → off.toNat + data.length ≤ maxBytes → 0 < data.length →
  xs.length = min (off.toNat + data.length) m.size - min off.toNat m.size →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦*{dqs} data ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
      osBytes (GF := GF) d.ino (min off.toNat m.size) (DFrac.own 1) xs ∗
      mcellsAny (GF := GF) m.maps (min off.toNat m.size) (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ RET (PairV #(W64 data.length) #(interface.nil : GoInterface));
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      ∃ ys : List ByteG,
        ⌜ys.map Prod.fst = pwValsG m.size off.toNat data data.length xs⌝ ∗
        osMeta d.ino (DFrac.own 1) (os.pwPostE m off.toNat data.length data.length data.length) ∗
        osBytes d.ino (min off.toNat m.size) (DFrac.own 1) ys ∗
        mcellsAny m.maps (min off.toNat m.size) (off.toNat + data.length) }}

end spec

end EtcdGrove
end Perennial
