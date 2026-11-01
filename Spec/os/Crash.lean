/-
Crash-aware specs of the `os` and `syscall` calls a crash proof makes on one file (this
repository's `os`, project `bboltfs`): `os.OpenFile` (`O_RDWR|O_CREATE`), `(*os.File).WriteAt` and
`syscall.Fdatasync`. The file is in a crash invariant (`cfInv N path γ Good`,
`Proof/os/CrashFile.lean`), which each call opens around each of the extension's steps; the caller
holds its part (`cfOwn path γ s`), and shows that what a crash may leave of the states the call
passes through is `Good`. The other calls need no crash-aware spec: `ReadAt` reads with the
caller's half of the bytes (`File.ReadAt.specRacy`), and `Close` and `Fd` touch no file resource.
Proved in `Proof/os/Crash.lean`. Lean-first (no Rocq counterpart).

* `OpenFile.specCrash`: absent or idle, to `openState s` (created if absent); on failure maybe.
* `File.WriteAt.specCrash`: idle `m`, `bs`, to an idle narrowing (`Narrow`) of it, with the data
  written on success. The caller shows `CrashOk` of the first attempt in flight (`cfWriting`).
* `syscall.Fdatasync.specCrash`: idle to synced (`OsMeta.synced`, `syncedBytes`), which the caller
  shows `CrashOk`; on failure `ok` is lost.
-/
module

public import Proof.os.CrashOps

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
abbrev os.OpenFile.specCrash : Prop :=
  ∀ (path : GoString) (perm : w32) (N : Namespace) (γ : GName) (Good : Option OsFile → Prop)
    (s : CFile),
  (s = none ∨ ∃ m bs, s = some (m, bs, none)) → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  CrashOk Good (openState s) →
  {{ osInv (GF := GF) ∗ cfInv (GF := GF) N path γ Good ∗ cfOwn (GF := GF) path γ s }}
    (App (App (App (Val (@! os.OpenFile)) (Val #path)) (Val #(W64 0x42))) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
      (∃ fd : w64, ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗ os.ownFile f fd path (DFrac.own 1) ∗
          osFd fd (DFrac.own 1) ⟨path, true, true⟩ ∗ cfOwn path γ (openState s)) ∨
      (⌜err ≠ interface.nil ∧ f = null⌝ ∗
        ∃ s' : CFile, ⌜s' = s ∨ s' = openState s⌝ ∗ cfOwn path γ s') }}

/-- See the file header. -/
abbrev os.File.WriteAt.specCrash : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (γ : GName)
    (Good : Option OsFile → Prop) (m : OsMeta) (bs : List (w8 × Bool)),
  d.writable = true → 0 ≤ off.toInt → 0 < data.length → data.length ≤ 0x40000000 →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → CrashOk Good (cfWriting m bs off.toNat data) →
  {{ osInv (GF := GF) ∗ cfInv (GF := GF) N d.path γ Good ∗ os.ownFile (GF := GF) f fd name dqf ∗
      sl ↦*{dqs} data ∗ osFd (GF := GF) fd dq d ∗ cfOwn (GF := GF) d.path γ (some (m, bs, none)) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      ∃ (m' : OsMeta) (bs' : List (w8 × Bool)),
        ⌜Narrow m bs off.toNat data m' bs' ∧
          ((n = W64 data.length ∧ err = interface.nil ∧ off.toNat + data.length ≤ m'.size ∧
              ∀ i < data.length, (bs'[off.toNat + i]?).map Prod.fst = data[i]?) ∨
           (n = W64 0 ∧ err ≠ interface.nil))⌝ ∗
        cfOwn d.path γ (some (m', bs', none)) }}

variable [syscall.Assumptions] in
/-- See the file header. -/
abbrev syscall.Fdatasync.specCrash : Prop :=
  ∀ (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (γ : GName) (Good : Option OsFile → Prop)
    (m : OsMeta) (bs : List (w8 × Bool)),
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → CrashOk Good (some (m.synced, syncedBytes m bs, none)) →
  {{ osInv (GF := GF) ∗ cfInv (GF := GF) N d.path γ Good ∗ osFd (GF := GF) fd dq d ∗
      cfOwn (GF := GF) d.path γ (some (m, bs, none)) }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ cfOwn d.path γ (some (m.synced, syncedBytes m bs, none))) ∨
       (⌜e ≠ 0⌝ ∗ cfOwn d.path γ (some ({ m with ok := false }, bs, none)))) }}

end spec

end EtcdGrove
end Perennial
