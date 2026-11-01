/-
`syscall.Fdatasync(fd)` (this repository's `syscall`, project `bboltfs`): the trusted model
(`TrustedCode/syscall.lean`) is the Linux file extension's `Fsync`, so the spec is `wp_Fsync`'s:
with the whole of the file's `OsMeta` and some of its bytes, whole. On success the size is durable
and the bytes clean (unless a failed sync lost one, `m.ok`); on failure, bytes may be lost.
Proved in `Proof/syscall/Fdatasync.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.syscall.Base

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
variable [syscall.Assumptions]

/-- See the file header. -/
abbrev syscall.Fdatasync.spec : Prop :=
  ∀ (fd : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (lo : Nat) (xs : List (w8 × Bool)),
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.path (DFrac.own 1) (some m) ∗
      osBytes (GF := GF) d.path lo (DFrac.own 1) xs }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ osMeta d.path (DFrac.own 1) (some m.synced) ∗
          osBytes d.path lo (DFrac.own 1) (syncedBytes m xs)) ∨
       (⌜e ≠ 0⌝ ∗ osMeta d.path (DFrac.own 1) (some { m with ok := false }) ∗
          osBytes d.path lo (DFrac.own 1) xs)) }}

end spec

end EtcdGrove
end Perennial
