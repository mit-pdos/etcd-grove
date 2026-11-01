/-
`f.Sync()` on an open `*os.File` (this repository's `os`, project `bboltfs`): `fsync`, as
`syscall.Fdatasync` (`Spec/syscall/Fdatasync.lean`, D3), with the whole of the file's `OsMeta`
(no change in flight) and some of its bytes, whole. The model (`TrustedCode/os.lean`) is the
extension's `Fsync` (`wp_osFsync`), retried on `EINTR`, which `Fsync` never returns, so the loop
runs once. On success the size is durable and the bytes clean unless an earlier failed sync lost
one (`m.ok`); on failure, nothing more is clean, and bytes may be lost. Proved in
`Proof/os/File__Sync.lean`. Lean-first (no Rocq counterpart).
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
abbrev os.File.Sync.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta) (lo : Nat)
    (xs : List (w8 × Bool)),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.path (DFrac.own 1) (some m) ∗
      osBytes (GF := GF) d.path lo (DFrac.own 1) xs }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ osMeta d.path (DFrac.own 1) (some m.synced) ∗
          osBytes d.path lo (DFrac.own 1) (syncedBytes m xs)) ∨
       (⌜err ≠ interface.nil⌝ ∗ osMeta d.path (DFrac.own 1) (some { m with ok := false }) ∗
          osBytes d.path lo (DFrac.own 1) xs)) }}

end spec

end EtcdGrove
end Perennial
