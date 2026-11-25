/-
The proof of `wal.Repair.specHeld` (`Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean`;
2026-11-15, the lock semantics, `notes/wal-units/locks.md` item 5): `openLast` fails
(`openLast.specHeld`: the last segment's lock is held, so `LockFile` returns only an error, or never
returns), and `Repair` returns `false` before deferring anything. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Repair
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openLast

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
theorem wal.Repair.wp_specHeld
    (wp_openLast : go_etcd_io.etcd.server.v3.storage.wal.openLast.specHeld (GF := GF) (hG := hG)) :
    wal.Repair.specHeld (GF := GF) (hG := hG) := by
  intro lg R dir j X hj segs gL qd dqn k fd hX hsn hino hnd hsort hnmf hgL hdl
  have hdl' : dir.length < 4096 := hdl.1
  wp_start as ⟨#Hzap, #Hinv, #Hsi, Hpd, Hperm, Hj, Hl, #Hk⟩
  ihave %hlgn := zapLoggerOk_ne_null lg $$ Hzap
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  rw [decide_eq_false hlgn]
  try wp_auto
  wp_apply wp_openLast lg R dir j X hj segs gL qd dqn k fd hX hsn hino hnd hsort hnmf hgL hdl
    $$ [Hpd Hperm Hj Hl] as %lf %err ⟨%herr, Hpd, Hperm, Hj, Hl⟩
  · iframe; iframe #
  cases err
  case nil => exact absurd rfl herr
  try wp_auto
  iapply HΦ
  iframe
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
