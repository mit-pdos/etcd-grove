/-
`f.Truncate(sz)` on an unmapped file whose resources are **split between the caller and atomic
updates** (I3b of `notes/wal-fsext-plan.md`), as the WAL's tail is between its handle and `walInv`:
`os.File.Truncate.spec` (`File__Truncate.lean`) with the caller's halves of the `OsMeta` and of the
bytes cut off, a tie `K` the caller holds between attempts (the WAL: its half of the tail record),
and a persistent supply of updates (`os.truncSup`), one pair per attempt of the model's `EINTR` loop.
Each attempt hands the supply the caller's halves and `K`: the first update (`os.truncAuW`) lends the
whole `OsMeta` and bytes cut off at `FtruncateStart` (its owner knows the state from the caller's
halves, by agreement with its own) and commits with the token (`rsTok`, kept by the update's owner
while the change is in flight); its commit is the second, which lends the token at `FtruncateFinish`
and commits with what the step left (`rsOutT`, whole), giving the caller its halves (`os.truncOutH`)
and `K` back. The post is `File__Truncate.lean`'s at half (`os.ftDoneH`, `os.ftUndoneH`), with `K`.
Proof: `Proof/os/File__TruncateAu.lean` (proved: the loop of `File__Truncate.lean`'s proof over
`wp_osFtruncateStart_auW`/`wp_osFtruncateFinish_au`). Lean-first.

(The first form, 2026-11-13 `wal-kz`, had the update lend only the other halves, for states the
caller named: an invariant cannot supply that, as it does not see the caller's halves; and without a
tie the second update cannot find its token in the invariant.)
-/
module

public import LinuxFs.Proof.os.ResizeAuW
public import LinuxFs.Proof.os.TcKnows
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
(`os.ftDone`'s, the candidates `zs` of the bytes grown over), its `OsMeta` up to the candidates it
knows past the size and of its resize stamps (`rsPostK`: the update's owner, holding the other half,
knows them), knowing which bytes past the size have known candidates (`TcKnows`: those the landing
keeps known, `rsTail`'s domain; `wal-tc10`). -/
def os.ftDoneH (p : Ino) (m : OsMeta) (tg : Nat) (zs : List Cands) : IProp GF :=
  iprop(⌜zs.length = tg - m.size⌝ ∗ (∃ tc rz, ⌜TcKnows m tg tg tc⌝ ∗ osMeta p (DFrac.own (1 : Qp).half)
      ((rsPost true m tg tg).withTc tc rz)) ∗
    osBytes p m.size (DFrac.own (1 : Qp).half) (zs.map (fun c => ((0 : w8), c))))

/-- The caller's half of a resize of `p` from `m` to `tg` that did not land (`os.ftUndone`'s, the
bytes it would have cut off `xs'`), its `OsMeta` up to the candidates it knows past the size and of
its resize stamps (`rsUnMeta`: the update's owner, holding the other half, knows them), knowing which
bytes past the size have known candidates (`TcKnows` at the old size: those the not-landed outcome keeps
known). -/
def os.ftUndoneH (p : Ino) (m : OsMeta) (tg : Nat) (xs' : List ByteG) : IProp GF :=
  iprop((∃ tc rz, ⌜TcKnows m tg m.size tc⌝ ∗ osMeta p (DFrac.own (1 : Qp).half)
      ((m.announce (min m.size tg) (rsHi true m.size tg) tg).withTc tc rz)) ∗
    osBytes p (min m.size tg) (DFrac.own (1 : Qp).half) xs')

/-- What the caller gets back of an attempt from `m0`, `xs0` whose second step returned `e`: its
halves of the outcome (`rsOutT`'s). -/
def os.truncOutH (p : Ino) (tg : Nat) (m0 : OsMeta) (xs0 : List ByteG) (n : Nat) (e : w64) :
    IProp GF :=
  iprop((⌜e = 0⌝ ∗ ∃ zs, os.ftDoneH p m0 tg zs) ∨
    (⌜e ≠ 0⌝ ∗ ((∃ zs, os.ftDoneH p m0 tg zs) ∨ os.ftUndoneH p m0 tg (rsAnn n xs0))))

/-- **The updates of one attempt** of a resize of `p` to `tg` from `m0`, `xs0`, the caller's tie `K`:
the start's (the whole `OsMeta` and bytes cut off lent for the token), whose commit is the finish's
(the token lent for the outcome, the caller's halves of it and `K` back). -/
def os.truncAuW (K : IProp GF) (p : Ino) (tg : Nat) (m0 : OsMeta) (xs0 : List ByteG) : IProp GF :=
  osAUnc (A := Nat × Nat)
    iprop(osMeta p (DFrac.own 1) m0 ∗ osBytes p (min m0.size tg) (DFrac.own 1) xs0)
    (fun tn => iprop(rsTok true tn.1 p tg m0 xs0 tn.2 ∗ ⌜0 < tn.2 ∧ m0.TcZ⌝))
    (fun tn => osAUnc (A := w64) (rsTok true tn.1 p tg m0 xs0 tn.2) (rsOutT p tg m0 xs0 tn.2)
      (fun e => iprop(os.truncOutH p tg m0 xs0 tn.2 e ∗ K)))

/-- **The supply of a resize of `p` to `tg`**, the caller's tie `K` (persistent): for any state, the
caller's halves and `K` make the attempt's updates. -/
def os.truncSup (K : IProp GF) (p : Ino) (tg : Nat) : IProp GF :=
  iprop(□ ∀ (m0 : OsMeta) (xs0 : List ByteG), ⌜xs0.length = m0.size - tg⌝ -∗ K -∗
    osMeta p (DFrac.own (1 : Qp).half) m0 -∗
    osBytes p (min m0.size tg) (DFrac.own (1 : Qp).half) xs0 -∗ os.truncAuW K p tg m0 xs0)

instance os.truncSup_persistent (K : IProp GF) (p : Ino) (tg : Nat) :
    Persistent (os.truncSup (GF := GF) K p tg) := by
  unfold os.truncSup; infer_instance

/-- See the file header. -/
abbrev os.File.Truncate.specAu : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64) (dq : DFrac) (d : OsFd)
    (m : OsMeta) (xs : List ByteG) (K : IProp GF),
  0 ≤ fd.toInt → d.writable = true → 0 ≤ sz.toInt → m.maps = ∅ → xs.length = m.size - sz.toNat →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own (1 : Qp).half) m ∗
      osBytes (GF := GF) d.ino (min m.size sz.toNat) (DFrac.own (1 : Qp).half) xs ∗
      K ∗ os.truncSup (GF := GF) K d.ino sz.toNat }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗ K ∗
      ((⌜err = interface.nil⌝ ∗ ∃ zs, os.ftDoneH d.ino m sz.toNat zs) ∨
       (⌜err ≠ interface.nil⌝ ∗
         ((∃ zs, os.ftDoneH d.ino m sz.toNat zs) ∨
          ∃ xs' : List ByteG, ⌜xs'.map Prod.fst = xs.map Prod.fst⌝ ∗
            os.ftUndoneH d.ino m sz.toNat xs'))) ∗
      fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
