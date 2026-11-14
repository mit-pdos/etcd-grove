/-
`(*WAL).Save` over its callees: `sync`, `saveEntry`, `saveState`, `cut` (their specs, hypotheses until
proved: `saveEntry`/`saveState`/`sync` wait for writes past the tail's preallocated size), the laws of
the client's raft messages (`WalPbIn.IsEmptyLaw`, `WalPbIn.MustSyncLaw`, `WalPbIn.ZeroLaw`: the part
cannot import the main tree's raft specs, plan §10), `WAL.tail`, and Perennial's `Mutex`. The update
commits at the call's first step (`walHandleIn_append`); then (S/wal.go:1093-1135): the lock, the
shortcut (an empty state and no entries: nothing written, the committed handle quiescent already), the
nil states replaced by fresh zero ones (`ZeroLaw`), `MustSync`, the entries' records (the loop's
invariant `SaveSt`, `SavePure.lean`), the state's, the tail's offset (`Seek`, always the encoder's
offset), then `sync` if `MustSync` and the tail is below `SegmentSizeBytes`, `cut` if it is not
(its pipeline bound from a step's receipt and the handle's, `walPc_bound`). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Save
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cut
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntry
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveState
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutPre
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAppend
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SavePure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle
public import LinuxFs.Proof.os.Off
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

/-- **`Save`'s success post** from a quiescent handle (`hc.Done`) and the sync's wand. -/
theorem save_post (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (hs : HardStateM)
    (es : List EntryM) (Q : WalDur → IProp GF) (h hc : WalHS) (hD : hc.Done)
    (hmd : hc.md.length < 2 ^ 41) :
    ⊢ walHandleIn (W := W) P Mr w dir hc -∗ ⧗ hc.pc -∗ WalFs.walLenLb w dir (h.H.length + 1) -∗
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

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.wp_proof [os.file.FieldAssumptions]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr)
    (wp_saveEntry : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.spec (W := W) P Mr)
    (wp_saveState : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.spec (W := W) P Mr)
    (wp_cut : go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.spec (W := W) P Mr)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_empty : WalPbIn.IsEmptyLaw (GF := GF) (hG := hG) P)
    (wp_mustSync : WalPbIn.MustSyncLaw (GF := GF) (hG := hG) P)
    (hzero : WalPbIn.ZeroLaw (GF := GF) (hG := hG) P) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.spec (W := W) P Mr := by
  intro R jr r w dir hp hs sl esL es sized Q
  wp_start as ⟨#Harea, Hw, #Hhs, #Hsl, Hes, %hidx, %hsz, Hau⟩
  icases (walOpenWF_iff P Mr w dir).1 $$ Hw with ⟨%h, Hh, %hD, %hmd, Hr⟩
  ihave %hS := walAreaOk_encState walCodec Mr R jr r $$ Harea
  icases walHandleIn_idx P Mr w dir h $$ Hh with ⟨Hh, %hix⟩
  icases walHandleIn_lockFacts P Mr w dir h $$ Hh with ⟨Hh, #Hmu, #Hsync, #Hseg⟩
  have hix0 := hix.1 hD.1
  -- the commit, before the call's first step
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walHandleIn_append P Mr R jr r w dir h (WalOpG.save hs es).toRaw sized Q hD.1
    (saveOp_fit Mr hs es (hS hs) hsz) (fun a b => saveOp_idx Mr h.H hs es _ _ a b)
    $$ Harea Hnc Hh Hau with ⟨Hnc, Hh, #Hlb, HQ, %hcp⟩
  imodintro
  iframe Hnc
  have hcut : ∀ b ∈ h.cuts, b ≤ h.H.length := fun b hb => by
    rcases hcp.1 b hb with h0 | ⟨_, _, h1, _⟩
    · omega
    · have := (List.getElem?_eq_some_iff.1 h1).1; simp at this; omega
  have hs0 := SaveSt.init Mr h hs es
  generalize ({ h with H := h.H ++ [(WalOpG.save hs es).toRaw], rest := (opDs Mr (WalOpG.save hs es).toRaw.toM).length } : WalHS) = h1 at hs0 ⊢
  ihave %hlen := ownSlice_len $$ Hsl
  iunfold walEntsIn at Hes
  icases Hes with #Hes
  ihave %hlen2 := BigSepL2.bigSepL2_length $$ Hes
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  (try wp_auto)
  -- the shortcut's test
  wp_apply (wp_empty hp hs) $$ [] as %b %hb
  · iexact Hhs
  wp_join (Q := fun v => iprop(ents_ptr ↦ sl ∗
      ⌜∃ c : Bool, v = #c ∧ (c = true ↔ hsEmptyP hs ∧ es = [])⌝)) at (if: _ then _ else #false) with [ents]
  · cases b
    · wp_auto
      iframe; ipureintro; exact ⟨false, rfl, by simp only [Bool.false_eq_true, false_iff]; exact fun h => absurd (hb.2 h.1) (by simp)⟩
    · wp_auto
      iframe; ipureintro
      refine ⟨_, rfl, ?_⟩
      rw [decide_eq_true_iff, save_slen_zero sl esL hlen.1 hlen.2, ← List.length_eq_zero_iff, hlen2,
        List.length_eq_zero_iff]
      exact ⟨fun h => ⟨hb.1 rfl, h⟩, fun h => h.2⟩
  iintro ⟨ents, %Hv⟩
  obtain ⟨c, rfl, hc⟩ := Hv
  cases c
  rotate_left
  · -- the shortcut: nothing written, the committed handle quiescent
    obtain ⟨hse, rfl⟩ := hc.1 rfl
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    have hf := SaveSt.finEmpty hs0 hD hse
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    rw [← hs0.pc]
    iapply save_post P Mr w dir hs [] Q h h1 hf.done (by rw [hf.md]; exact hmd) $$ Hh Hr Hlb HQ
    iintro %hm
    exfalso
    rcases hm with hm | ⟨hm, -⟩
    · exact hm rfl
    · exact hm hse
  have hne : ¬ (hsEmptyP hs ∧ es = []) := fun h => by simpa using hc.2 h
  wp_auto
  -- `st == nil`: a fresh zero state
  wp_join iprop(∃ hp' : Loc, st_ptr ↦ hp' ∗ P.hsIn hp' hs ∗ ⌜hp' ≠ null⌝)
    at (if: _ then _ else _) with [st] as ⟨%hp', st, #Hhs', %hp'n⟩
  · iapply wp_fupd
    wp_if_destruct
    · ihave %hz0 := hzero.1 hs $$ Hhs
      subst hz0
      icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr0, %hn⟩
      imod hzero.2 _ ⊤ $$ Hr0 with #Hz
      imodintro
      isplitr
      · ipureintro; trivial
      iexists «$r0_ptr»; iframe st Hz; ipureintro; exact hn
    · imodintro
      isplitr
      · ipureintro; trivial
      iexists hp; iframe st Hhs; ipureintro; exact Hif
  -- `w.state == nil`: a fresh zero state
  icases walHandleIn_state P Mr w dir h1 $$ Hh with ⟨%sp, Hsp, #Hst, Hback⟩
  wp_join iprop(w_ptr ↦ w ∗ ∃ sp' : Loc,
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp' ∗ P.hsIn sp' h1.st)
    at (if: _ then _ else _) with [Hsp w] as ⟨w, %sp', Hsp, #Hst'⟩
  · iapply wp_fupd
    (try wp_auto)
    wp_if_destruct
    · ihave %hz0 := hzero.1 _ $$ Hst
      icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr0, %hn⟩
      imod hzero.2 _ ⊤ $$ Hr0 with #Hz
      imodintro
      isplitr
      · ipureintro; trivial
      iframe w; iexists «$r0_ptr»; rw [hz0]; iframe Hsp Hz
    · imodintro
      isplitr
      · ipureintro; trivial
      iframe w; iexists sp; iframe Hsp Hst
  -- `MustSync`
  wp_apply (wp_mustSync hp' sp' hs h1.st sl.len) $$ [] as %ms %hms
  · iframe Hhs' Hst'
  ihave Hh := Hback $$ Hsp Hst'
  sorry

end proof

end EtcdGrove
end Perennial
