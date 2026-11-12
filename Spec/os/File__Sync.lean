/-
`f.Sync()` on an open `*os.File` (this repository's `os`, project `bboltfs`): `fsync`, as
`syscall.Fdatasync` (`Spec/syscall/Fdatasync.lean`, D3), with the whole of the file's `OsMeta`
(no change in flight) and some of its bytes, whole. The model (`TrustedCode/os.lean`) is the
extension's `Fsync` (`wp_osFsync`), retried on `EINTR`, which `Fsync` never returns, so the loop
runs once. The bytes given hold every byte `m` says may not be durable (`m.Covers`). On success
the size and every byte are durable (`OsMeta.synced`, each byte its value alone, `durB`); on
failure nothing changes (no failed writeback: the semantics' rule). `os.File.Sync.specB` is the
byte-less variant (`wp_osFsyncB`), for a client that holds none of the bytes (bbolt's `DB.grow`): on
success the `OsMeta` is `m.bsynced c` for some change number `c` (size and mappings unchanged), on
failure nothing changes. Proved in
`Proof/os/File__Sync.lean`. Lean-first (no Rocq counterpart).
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
abbrev os.File.Sync.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta) (lo : Nat)
    (xs : List ByteG),
  m.Covers lo xs.length →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
      osBytes (GF := GF) d.ino lo (DFrac.own 1) xs }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ osMeta d.ino (DFrac.own 1) m.synced ∗
          osBytes d.ino lo (DFrac.own 1) (xs.map (fun x => durB x.1))) ∨
       (⌜err ≠ interface.nil⌝ ∗ osMeta d.ino (DFrac.own 1) m ∗
          osBytes d.ino lo (DFrac.own 1) xs)) ∗
      fmtErrorOkOrNil err }}

/-- The byte-less variant (see the file header). -/
abbrev os.File.Sync.specB : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ ∃ c, osMeta d.ino (DFrac.own 1) (m.bsynced c)) ∨
       (⌜err ≠ interface.nil⌝ ∗ osMeta d.ino (DFrac.own 1) m)) ∗
      fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
