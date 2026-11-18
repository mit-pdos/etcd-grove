/-
The lemmas of `WAL__Save.lean`'s proof (`save_slen_zero`, `save_post`, ...), in a module of their own so
that `WAL__SaveNoErr.lean` imports them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Save
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cut
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntry
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveState
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutPre
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAppend
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SavePure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.StreamBound
public import Proof.os.Off
public import Perennial.Proof.sync.Results
public import Proof.ReceiptTactics

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
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- A slice's length is zero iff its list is empty. -/
theorem save_slen_zero (sl : GoSlice) (xs : List Loc) (h1 : xs.length = sint.nat sl.len)
    (h2 : 0 ≤ sint.Z sl.len) : sl.len = W64 0 ↔ xs = [] := by
  rw [← List.length_eq_zero_iff, h1]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    have : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
    word

/-- An offset below ext4's maximum, as a signed word (`cut`'s `cut_off_toInt`). -/
theorem save_off_toInt (a b : Nat) (h : a + b ≤ 0xffffffff000) :
    0 ≤ (W64 ((a : Int) + (b : Int))).toInt ∧ (W64 ((a : Int) + (b : Int))).toInt ≤ 0xffffffff000 ∧
      (W64 ((a : Int) + (b : Int))).toInt = a + b := by
  have : (W64 ((a : Int) + (b : Int))).toInt = a + b := by
    word
  omega

/-- `Save`'s offset test, below the segment size. -/
theorem save_hif (a b : Nat) (hx : (W64 ((a : Int) + (b : Int))).toInt = a + b)
    (h : sint.Z (W64 ((a : Int) + (b : Int))) < sint.Z (W64 64000000)) : a + b < 64000000 := by
  have e1 : sint.Z (W64 ((a : Int) + (b : Int))) = ((a + b : Nat) : Int) := by
    rw [show sint.Z (W64 ((a : Int) + (b : Int))) = (W64 ((a : Int) + (b : Int))).toInt from rfl, hx]; simp
  have e2 : sint.Z (W64 64000000) = 64000000 := by decide
  rw [e1, e2] at h; omega

/-- `walPc_bound`, keeping the receipt. -/
theorem save_pc_bound (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (n : Nat) :
    ⊢@{IProp GF} WalFs.walAreaOk walCodec Mr R jr r -∗ ⧗ (n + 1) -∗ ⧗ (n + 1) ∗ ⌜n + 2 < 2 ^ 63⌝ := by
  iintro #Harea Hr
  have H := persistent_entails_left (PROP := IProp GF)
    (P := iprop(WalFs.walAreaOk walCodec Mr R jr r ∗ ⧗ (n + 1))) (Q := iprop(⌜n + 2 < 2 ^ 63⌝))
    (by iintro ⟨#Ha, Hr⟩; iapply (walPc_bound walCodec Mr R jr r n) $$ Ha Hr)
  ihave Hx := H $$ [Hr]
  · iframe Harea Hr
  icases Hx with ⟨⟨-, Hr⟩, %hb⟩
  iframe Hr; ipureintro; exact hb

/-- **`Save`'s success post** from a quiescent handle (`hc.Done`) and the sync's wand. -/
theorem save_post (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (hs : HardStateM)
    (es : List EntryM) (Q : WalDur → IProp GF) (h hc : WalHS) (hD : hc.Done)
    (hmd : hc.md.length < 2 ^ 41) :
    ⊢ walHandleIn (W := W) P Mr w dir hc TailMetaW -∗ ⧗ hc.pc -∗ WalFs.walLenLb w dir (h.H.length + 1) -∗
      (∃ d : WalDur, Q d ∗ ⌜d.H = h.H⌝) -∗
      (⌜walMustSync (h.H.map WalOpG.toM) hs es⌝ -∗ WalFs.walSyncedLb dir (h.H.length + 1)) -∗
      (walOpenWF (W := W) P Mr w dir ∗ ∃ d : WalDur, Q d ∗ WalFs.walLenLb w dir (d.H.length + 1) ∗
        (⌜walMustSync (d.H.map WalOpG.toM) hs es⌝ -∗ WalFs.walSyncedLb dir (d.H.length + 1))) := by
  iintro Hh Hr #Hlb ⟨%d, HQ, %hd⟩ Hs
  isplitl [Hh Hr]
  · iapply (walOpenWF_iff P Mr w dir).2
    iexists hc
    iframe Hh Hr
    ipureintro; exact ⟨hD, hmd⟩
  iexists d
  rw [hd]
  iframe HQ Hlb Hs

end proof

end EtcdGrove
end Perennial
