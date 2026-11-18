/-
`f.WriteAt(b, off)` ending by `maxBytes`, whose error witnesses that **the file system can fail**
(`File.WriteAt.spec` with `⌜¬ FsNoErr⌝` in its error case; session S3f of
`notes/bbolt-integration-plan.md`): under the premises `FsNoErr` names, `specNoErr` (a write past
`maxBytes` fails with `EFBIG` whatever the premises, hence the bound). Proved in
`Proof/os/File__WriteAtW.lean`, from the two.
-/
module

public import Spec.os.File__WriteAt
public import GooseLang.Ext.Fs.FsNoErr

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
abbrev os.File.WriteAt.specW : Prop :=
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
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      ∃ (j : Nat) (ys : List ByteG),
        ⌜j ≤ data.length ∧ os.PwOut m off.toNat data j xs ys ∧ PwCut off.toNat data.length j ∧
          ((j = data.length ∧ n = W64 data.length ∧ err = interface.nil) ∨
           (n = W64 0 ∧ err ≠ interface.nil ∧ ¬ FsNoErr))⌝ ∗
        osMeta d.ino (DFrac.own 1) (pwPost m off.toNat data.length j) ∗
        osBytes d.ino (off.toNat) (DFrac.own 1) ys ∗
        mcellsAny m.maps (off.toNat) (off.toNat + data.length) ∗
      fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
