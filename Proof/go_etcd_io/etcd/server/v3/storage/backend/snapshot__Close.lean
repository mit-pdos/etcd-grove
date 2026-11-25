/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/snapshot__Close.lean` (S4b, 2026-11-18;
until then a trust-boundary axiom, D22 S-h, over the opaque `snapOpen`): `s.Close()` takes from the
snapshot's invariant the right to close `stopc` (leaving the whole of the ghost variable `γ`, so the
invariant cannot give it twice), closes it, waits for `donec` (closed by `Snapshot`'s goroutine,
`backend__Snapshot.lean`) and rolls back the read transaction with the whole of it (bbolt's
`Tx.Rollback`: nil, and the reader slot's `threadTok` back). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__Close
public import Spec.go_etcd_io.bbolt.Tx__Rollback

@[expose] public section

set_option linter.iris.dupNamespace false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions]

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- bbolt's `Tx.Rollback` of a whole read transaction in the backend's vocabulary, at `theFs`. -/
private theorem bbolt.kvGlue_TxRollback_ro (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Rollback.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (D : backend.Data),
  {{ txLive (GF := GF) tx γ 1 (bbolt.TxView.ro D) }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Rollback")) (Val #()))
  {{ RET #GoInterface.nil; threadTok }} := by
  intro tx γ D
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.txLive, onFs_none hfs]
    iintro %Φ H HΦ
    iexfalso; iexact H
  · simp only [backend.txLive, onFs_some hfs]
    iintro %Φ Hl HΦ
    have h' := h tx γ (TxView.ro D)
    try simp only [TxView.ro.proj_rw] at h'
    wp_apply h' $$ [$Hl] as ⟨-, Ht⟩
    iapply HΦ; iexact Ht

/-- `Close`'s take of `stopc`'s close right from the snapshot's invariant, with the whole of `γ`. -/
private theorem snap_take (sc : GoChan) (γsc : ChanNames) (γ : GName) (tx : Loc) (γd : DBNames) :
    inv snapN iprop(ownBroadcastChan (GF := GF) sc γsc iprop(True) .Pending ∨ ghostVar γ 1 (tx, γd)) ∗
      ghostVar γ 1 (tx, γd) ∗ £ 1 ⊢ |={⊤}=> ownBroadcastChan sc γsc iprop(True) .Pending := by
  iintro ⟨#Hinv, Hg, Hlc⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑snapN) $$ Hlc Hi with Hi
  icases Hi with (Hp | Hg2)
  · imod Hclose $$ [Hg] with -
    · inext; iright; iexact Hg
    imodintro
    iexact Hp
  · ihave %Hv := ghostVar_valid_2 γ (tx, γd) 1 (tx, γd) 1 $$ Hg Hg2
    exfalso
    have h1 := Hv.1
    rw [Qp.le_iff, Qp.val_add, Qp.val_one] at h1
    grind

/-- `s.Close()`: `stopc` closed, `donec` awaited, the read transaction rolled back. -/
theorem backend.snapshot.Close.wp_proof
    (hRollback : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Rollback.spec (GF := GF) (hG := hG)) :
    backend.snapshot.Close.spec (GF := GF) (hG := hG) := by
  replace hRollback := bbolt.kvGlue_TxRollback_ro hRollback
  intro sp D γ
  wp_start as Hs
  iunfold snapOpenQ at Hs
  icases Hs with ⟨%tx, %γd, #Ha, Hg, Hl⟩
  ihave #Ha' := Ha
  iunfold snapAt at Ha'
  icases Ha' with ⟨%sc, %dc, %γsc, %γdc, #Htx, #Hscf, #Hdcf, #Hscb, #Hdcb, #Hinv⟩
  ihave #Hdcc := ownBroadcastChan_is_chan _ _ _ _ $$ Hdcb
  wp_auto_lc 1
  imod (snap_take sc γsc γ tx γd) $$ [$Hinv $Hg $Hlc1] with Hpend
  wp_apply (wp_broadcast_chan_close (ty := go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType []))
    sc γsc iprop(True)) $$ [$Hpend] as -
  · imodintro; itrivial
  wp_apply_core chan.wp_receive (V := Unit) dc γdc $$ Hdcc
  iintro -
  iapply broadcast_chan_receive _ _ _ _ _ $$ Hdcb
  iintro -
  wp_auto
  wp_apply (hRollback tx γd D) $$ [$Hl] as Htok
  iapply HΦ
  iexact Htok

end proof

end EtcdGrove
end Perennial
