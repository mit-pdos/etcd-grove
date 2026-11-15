/-
`syscall.Flock(fd, how)` (this repository's `syscall`, project `bboltfs`): the extension's `flock`
(`wp_osFlock`; the lock semantics of 2026-11-15, `notes/wal-units/locks.md`): for `how` `LOCK_SH`,
`LOCK_EX` or `LOCK_UN`, with or without `LOCK_NB` (`flockReq`: the request `req`), with the whole fd
and the token of its `flock` lock if exclusive (a lock only on a description with no `flock` lock):
`lockOut` (on success the request done, an exclusive lock with its token `osLock .flock d.ino fd`;
a lock's failure changes nothing; an unlock's failure may have released it). Proved in
`Proof/syscall/Flock.lean`. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.syscall.Base
public import GooseLang.Ext.Fs.Locks

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
abbrev syscall.Flock.spec : Prop :=
  ∀ (fd how : w64) (d : OsFd) (req : Option Bool) (nb : Bool),
  flockReq how.toNat = some (req, nb) → (req ≠ none → d.flk = none) →
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd (DFrac.own 1) d ∗ lockTok (GF := GF) .flock fd d }}
    (App (App (Val (@! syscall.Flock)) (Val #fd)) (Val #how))
  {{ (e : w64), RET #(errnoErr e); lockOut (GF := GF) .flock fd d req e }}

end spec

end EtcdGrove
end Perennial
