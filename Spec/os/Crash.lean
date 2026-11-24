/-
Crash-aware specs of the `os` and `syscall` calls a crash proof makes on one file (this
repository's `os`, project `bboltfs`): `os.OpenFile` (`O_RDWR|O_CREATE`), `(*os.File).WriteAt` and
`syscall.Fdatasync`. The file at the path `p` (in the roots `R`; a name of a root directory, `FileAt`) is in a crash
invariant (`cfInv N p R γ Good`, `Proof/os/CrashFile.lean`), which holds its state and half of the
claim on its name; each call opens it around each of the extension's steps. The caller holds its
part (`cfOwn p R γ s`: the other half of the claim), and shows that what a crash may leave of the
states the call passes through is `Good`. The other calls need no crash-aware
spec: `ReadAt` reads with the caller's half of the bytes (`File.ReadAt.specRacy`), and `Close` and
`Fd` touch no file resource. Proved in `Proof/os/Crash.lean`. Lean-first (no Rocq counterpart).

* `OpenFile.specCrash`: `p = d/b`, with a share of the call permission of `d`'s key; absent or
  idle, to `openSt` of it (created, its `create` logged, if absent), which the caller shows `Good`
  if created; on failure maybe.
* `File.WriteAt.specCrash`: idle `m`, `bs`, the write starting inside the file, to an idle state
  the write may pass through (`WIn`), with the data written on success. The caller shows that
  every file a crash may leave while the write runs is `Good` (`WriteOk`, `Proof/os/CrashWrite.lean`).
* `syscall.Fdatasync.specCrash`: idle to synced (`OsMeta.synced`, every byte durable), which the
  caller shows `FileOk`; on failure unchanged.
-/
module

public import Proof.os.PkgInit
public import Proof.os.CrashOps

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
abbrev os.OpenFile.specCrash : Prop :=
  ∀ (d b : GoString) (perm : w32) (N : Namespace) (R : Roots) (q : Qp) (γ : GName)
    (Good : Option OsFile → Prop) (s : CFile),
  NameOk b → (s = none ∨ ∃ i m bs, s = some (i, m, bs, none)) → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  ↑osShN ⊆ (⊤ : CoPset) \ ↑N → (s = none → FileOk Good (newMeta, [], none)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osCallPerm (GF := GF) (callKey R d) q ∗
      cfInv (GF := GF) N (child d b) R γ Good ∗ cfOwn (GF := GF) (child d b) R γ s }}
    (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #(W64 0x42))) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osCallPerm (callKey R d) q ∗
      ((∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧ (s = none ∨ cIno s = some i)⌝ ∗
          os.ownFile f fd (child d b) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨i, true, true, none, none⟩ ∗
          cfOwn (child d b) R γ (openSt i s)) ∨
      (⌜err ≠ interface.nil ∧ f = null⌝ ∗ (cfOwn (child d b) R γ s ∨
          ∃ i : Ino, cfOwn (child d b) R γ (openSt i s)))) }}

/-- See the file header. -/
abbrev os.File.WriteAt.specCrash : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (p : GoString) (R : Roots)
    (γ : GName) (Good : Option OsFile → Prop) (m : OsMeta) (bs : List ByteG),
  d.writable = true → 0 ≤ off.toInt → off.toNat ≤ m.size → off.toNat + data.length < 2 ^ 63 →
  0 < data.length → data.length ≤ 0x40000000 →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → WriteOk Good m bs off.toNat data →
  {{ osInv (GF := GF) ∗ cfInv (GF := GF) N p R γ Good ∗ os.ownFile (GF := GF) f fd name dqf ∗
      sl ↦*{dqs} data ∗ osFd (GF := GF) fd dq d ∗
      cfOwn (GF := GF) p R γ (some (d.ino, m, bs, none)) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      ∃ (m' : OsMeta) (bs' : List ByteG),
        ⌜WIn m bs off.toNat data m' bs' ∧
          ((n = W64 data.length ∧ err = interface.nil ∧ off.toNat + data.length ≤ m'.size ∧
              ∀ i < data.length, (bs'[off.toNat + i]?).map Prod.fst = data[i]?) ∨
           (n = W64 0 ∧ err ≠ interface.nil))⌝ ∗
        cfOwn p R γ (some (d.ino, m', bs', none)) }}

variable [syscall.Assumptions] in
/-- See the file header. -/
abbrev syscall.Fdatasync.specCrash : Prop :=
  ∀ (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (p : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) (m : OsMeta) (bs : List ByteG),
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → FileOk Good (m.synced, bs.map (fun x => durB x.1), none) →
  {{ osInv (GF := GF) ∗ cfInv (GF := GF) N p R γ Good ∗ osFd (GF := GF) fd dq d ∗
      cfOwn (GF := GF) p R γ (some (d.ino, m, bs, none)) }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ cfOwn p R γ (some (d.ino, m.synced, bs.map (fun x => durB x.1), none))) ∨
       (⌜e ≠ 0⌝ ∗ cfOwn p R γ (some (d.ino, m, bs, none)))) }}

end spec

end EtcdGrove
end Perennial
