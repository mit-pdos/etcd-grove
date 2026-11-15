/-
`syscall.Fdatasync(fd)` (this repository's `syscall`, project `bboltfs`): the trusted model
(`TrustedCode/syscall.lean`) is the Linux file extension's `Fsync`, so the spec is `wp_osFsync`'s:
with the whole of the file's `OsMeta` and its bytes that may not be durable (those `m` says may
not be, `m.Covers`), whole. On success the size and every byte are durable (`OsMeta.synced`, each
byte its value alone, `durB`); on failure, which is never `EINTR`, nothing changes (no failed
writeback: the semantics' rule).
Proved in `Proof/syscall/Fdatasync.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.syscall.Base

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
variable [syscall.Assumptions]

/-- See the file header. -/
abbrev syscall.Fdatasync.spec : Prop :=
  ∀ (fd : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (lo : Nat) (xs : List ByteG),
  m.Covers lo xs.length →
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
      osBytes (GF := GF) d.ino lo (DFrac.own 1) xs }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ osMeta d.ino (DFrac.own 1) m.synced ∗
          osBytes d.ino lo (DFrac.own 1) (xs.map (fun x => durB x.1))) ∨
       (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗ osMeta d.ino (DFrac.own 1) m ∗
          osBytes d.ino lo (DFrac.own 1) xs)) }}

end spec

end EtcdGrove
end Perennial
