/-
**etcd's boot path after a failed read** (unit `locks`, session 3): `openWALFromSnapshot`
(`bootstrap.go:683-689`) calls `w.Close()` after a failed `ReadAll`, ignores its error, and calls
`wal.Repair(lg, dir)`. When `Close` fails before unlocking (`w.sync()`'s error, S/wal.go:1060-1066), the
last segment's lock is still held through the handle's tail description, and `Repair`'s `openLast`
takes a blocking `LockFile` on it (`nonissues/etcd-bootstrap-repair-close-error-hang.md`). Over
`WAL.Close.spec` (state `failed`)'s error arm (`walCloseLeft`) and `wal.Repair.specHeld`: `Repair` returns `false`
(or never returns, which partial correctness allows), nothing changed, what `Close` left kept. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Repair

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **`Repair` after `Close.spec` (state `failed`)'s error** (see the file header): with what the failed `Close`
left (`walCloseLeft dir`) and the client's half of the call permission, `Repair(lg, dir)` returns
`false`, and both are kept (`dir` fits, `PathFits`, `Open`'s premise, which the caller knows). -/
theorem wal.Repair.wp_afterCloseFailed (wp_rep : wal.Repair.specHeld (GF := GF) (hG := hG))
    (lg : Loc) (dir : GoString) (hdir : PathFits dir) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal -∗ zapLoggerOk lg -∗
      osInv (GF := GF) -∗ walCloseLeft (GF := GF) dir -∗ osCallPerm (GF := GF) (callKey W.roots dir) (1 : Qp).half -∗
      (∀ b : Bool, ⌜b = false⌝ -∗ walCloseLeft (GF := GF) dir -∗ osCallPerm (GF := GF) (callKey W.roots dir) (1 : Qp).half -∗
        Φ #b) -∗
      WP (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Repair)) (Val #lg)) (Val #dir)) {{ Φ }} := by
  iintro #Hpi #Hzap #Hos Hleft Hp HΦ
  unfold walCloseLeft
  icases Hleft with ⟨%R, %j, %X, %hj, %segs, %gL, %qd, %k, %fd, %hok, #Hsh, %hRW, Hpath, Hnm, Hlk, #Hk, Hp2⟩
  subst hRW
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hok
  have h8 := hdir
  have hs := osCallPerm_split (L := hG.goose_localGS) (callKey W.roots dir) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hs
  ihave Hperm := hs.2 $$ [Hp Hp2]
  · iframe
  iapply (wp_rep lg W.roots dir j X hj segs gL qd (DFrac.own (1 : Qp).half) k fd h1 h2 h3 h4 h5 h6 h7 h8)
    $$ [Hpath Hperm Hnm Hlk]
  · iframe; iframe #
  inext
  iintro %b ⟨%hb, Hpath, Hperm, Hnm, Hlk⟩
  ihave ⟨Hp1, Hp2⟩ := hs.1 $$ Hperm
  iapply HΦ $$ %b %hb [Hpath Hnm Hlk Hp1] Hp2
  iexists W.roots, j, X, hj, segs, gL, qd, k, fd
  iframe; iframe #
  ipureintro; exact ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, rfl⟩

end proof

end EtcdGrove
end Perennial
