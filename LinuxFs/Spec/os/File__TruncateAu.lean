/-
`f.Truncate(sz)` on an unmapped file whose resources are **split between the caller and atomic
updates** (I3b of `notes/wal-fsext-plan.md`), as the WAL's tail is between its handle and `walInv`:
`os.File.Truncate.spec` (`File__Truncate.lean`) with the caller's halves of the `OsMeta` and of the
bytes cut off, and a persistent supply of updates (`os.truncAu`), one pair per attempt of the model's
`EINTR` loop, for each state an attempt may start from (`os.TruncFrom`: no attempt landed, the
`OsMeta` `m` or as an attempt announced it; or one did, a resize to the size the file has). Each
attempt's first update lends the other halves at `FtruncateStart` and commits with the token
(`rsTok`, kept by the update's owner while the change is in flight); its commit is the second, which
lends the token at `FtruncateFinish` and commits with what the step left (`rsOutT`, whole), giving
the caller its halves (`os.truncOutH`). The post is `File__Truncate.lean`'s at half (`os.ftDoneH`,
`os.ftUndoneH`). Proof: `Proof/os/File__TruncateAu.lean` (proved: the loop of
`File__Truncate.lean`'s proof over `wp_osFtruncateStart_au`/`Finish_au`). Lean-first.
-/
module

public import LinuxFs.Proof.os.ResizeAu
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

/-- The caller's half of a resize of the unmapped file `p` from `m` to `tg` that landed
(`os.ftDone`'s, the candidates `zs` of the bytes grown over). -/
def os.ftDoneH (p : Ino) (m : OsMeta) (tg : Nat) (zs : List Cands) : IProp GF :=
  iprop(⌜zs.length = tg - m.size⌝ ∗ osMeta p (DFrac.own (1 : Qp).half) (rsPost true m tg tg) ∗
    osBytes p m.size (DFrac.own (1 : Qp).half) (zs.map (fun c => ((0 : w8), c))))

/-- The caller's half of a resize of `p` from `m` to `tg` that did not land (`os.ftUndone`'s, the
bytes it would have cut off `xs'`). -/
def os.ftUndoneH (p : Ino) (m : OsMeta) (tg : Nat) (xs' : List ByteG) : IProp GF :=
  iprop(osMeta p (DFrac.own (1 : Qp).half) (m.announce (min m.size tg) (rsHi true m.size tg) tg) ∗
    osBytes p (min m.size tg) (DFrac.own (1 : Qp).half) xs')

/-- What the caller gets back of an attempt from `m0`, `xs0` whose second step returned `e`: its
halves of the outcome (`rsOutT`'s). -/
def os.truncOutH (p : Ino) (tg : Nat) (m0 : OsMeta) (xs0 : List ByteG) (n : Nat) (e : w64) :
    IProp GF :=
  iprop((⌜e = 0⌝ ∗ ∃ zs, os.ftDoneH p m0 tg zs) ∨
    (⌜e ≠ 0⌝ ∗ ((∃ zs, os.ftDoneH p m0 tg zs) ∨ os.ftUndoneH p m0 tg (rsAnn n xs0))))

/-- **The updates of one attempt** of a resize of `p` to `tg` from `m0`, `xs0`: the start's (the
other halves lent for the token), whose commit is the finish's (the token lent for the outcome,
the caller's halves of it back). -/
def os.truncAu (p : Ino) (tg : Nat) (m0 : OsMeta) (xs0 : List ByteG) : IProp GF :=
  osAUnc (A := Nat × Nat)
    iprop(osMeta p (DFrac.own (1 : Qp).half) m0 ∗
      osBytes p (min m0.size tg) (DFrac.own (1 : Qp).half) xs0)
    (fun tn => rsTok true tn.1 p tg m0 xs0 tn.2)
    (fun tn => osAUnc (A := w64) (rsTok true tn.1 p tg m0 xs0 tn.2) (rsOutT p tg m0 xs0 tn.2)
      (os.truncOutH p tg m0 xs0 tn.2))

/-- The states an attempt of a resize from `m`, `xs` to `tg` may start from. -/
def os.TruncFrom (m : OsMeta) (xs : List ByteG) (tg : Nat) (m0 : OsMeta) (xs0 : List ByteG) : Prop :=
  ((m0 = m ∨ m0 = m.announce (min m.size tg) (rsHi true m.size tg) tg) ∧
    xs0.map Prod.fst = xs.map Prod.fst ∧ xs0.length = m.size - tg) ∨
  (m0 = rsPost true m tg tg ∧ xs0 = [])

/-- See the file header. -/
abbrev os.File.Truncate.specAu : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64) (dq : DFrac) (d : OsFd)
    (m : OsMeta) (xs : List ByteG),
  0 ≤ fd.toInt → d.writable = true → 0 ≤ sz.toInt → m.maps = ∅ → xs.length = m.size - sz.toNat →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own (1 : Qp).half) m ∗
      osBytes (GF := GF) d.ino (min m.size sz.toNat) (DFrac.own (1 : Qp).half) xs ∗
      □ (∀ m0 xs0, ⌜os.TruncFrom m xs sz.toNat m0 xs0⌝ -∗ os.truncAu (GF := GF) d.ino sz.toNat m0 xs0) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ ∃ zs, os.ftDoneH d.ino m sz.toNat zs) ∨
       (⌜err ≠ interface.nil⌝ ∗
         ((∃ zs, os.ftDoneH d.ino m sz.toNat zs) ∨
          ∃ xs' : List ByteG, ⌜xs'.map Prod.fst = xs.map Prod.fst⌝ ∗
            os.ftUndoneH d.ino m sz.toNat xs'))) ∗
      fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
