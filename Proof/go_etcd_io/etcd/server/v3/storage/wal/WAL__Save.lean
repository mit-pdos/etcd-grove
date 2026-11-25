/-
`(*WAL).Save` over its callees: `sync`, `saveEntry`, `saveState`, `cut` (their two specs each, chosen at a
call by whether `Sio` covers every inode, `CalleeCov.lean`: their families are left for the queued
cleanup), the laws of the client's raft messages (`WalPbIn.IsEmptyLaw`, `WalPbIn.MustSyncLaw`,
`WalPbIn.ZeroLaw`: the part cannot import the main tree's raft specs, plan §10), `WAL.tail`, and
Perennial's `Mutex`. One proof since wal-link L1a (2026-11-17, `notes/wal-link-scope.md` §8; the former
`wp_proof` and `wp_proofNoErr` merged). After the lock, the deferred `Unlock`'s resolution gives the later
credit with which the share gives the handle (`walOpenWS_acquire`, `walHdl_open`: with the fresh room when
`walCov Sio`); the update commits at the next resolution (`walHandleIn_append`; that step raises the WALs'
step bound read at a look, `walHandleIn_steps`, which the commit deposits); then (S/wal.go:1093-1135): the
shortcut (an empty state and no entries: nothing written, the committed handle quiescent already), the nil
states replaced by fresh zero ones (`ZeroLaw`), `MustSync`, the entries' records (the loop's invariant
`SaveSt`, `SavePure.lean`, with the room left for the batch's remaining frames when covered), the state's,
the tail's offset (`Seek`, always the encoder's offset), then `sync` if `MustSync` and the tail is below
`SegmentSizeBytes`, `cut` if it is not (its pipeline bound from a step's receipt and the handle's,
`walPc_bound`). The room after: the tail below `SegmentSizeBytes`, or the cut's fresh segment, both within
`walFreshRoom`. Before the unlock the handle goes back (`walOpenWS_release`), or, after an error (only when
not covered, and then with the whole share), the whole share is spent (`walOpenWS_finish`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Save
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CalleeCov
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cut
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
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- The remaining frames' room, one entry consumed. -/
theorem save_drop_sum (Mr : WalMarshal) (es : List EntryM) (j : Nat) (e : EntryM) (he : es[j]? = some e) :
    ((es.drop j).map (fun e => (Mr.encEntry e).length + 64)).sum =
      ((Mr.encEntry e).length + 64) + ((es.drop (j + 1)).map (fun e => (Mr.encEntry e).length + 64)).sum := by
  have hj : j < es.length := (List.getElem?_eq_some_iff.1 he).1
  rw [List.getElem?_eq_getElem hj] at he
  cases he
  rw [List.drop_eq_getElem_cons hj, List.map_cons, List.sum_cons]

/-- A slice's length is zero iff its list is empty. -/
theorem save_slen_zero (sl : GoSlice) (xs : List Loc) (h1 : xs.length = sint.nat sl.len)
    (h2 : 0 ≤ sint.Z sl.len) : sl.len = W64 0 ↔ xs = [] := by
  rw [← List.length_eq_zero_iff, h1]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    have : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
    word

/-- **`Save`'s success post** from a quiescent handle (`hc.Done`) and the sync's wand: the handle for the
lock (`walHdl`, the fresh room when covered). -/
theorem save_post (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (γ : WalShN) (hs : HardStateM)
    (es : List EntryM) (Q : WalDur → IProp GF) (h hc : WalHS)
    (hD : hc.Done) (hmd : hc.md.length < 2 ^ 41)
    (hroom : walCov Sio → hc.o0 + hc.out.length + hc.pend.length + walFreshRoom ≤ maxBytes) :
    ⊢ walHandleIn (W := W) P Mr w dir hc TailMetaW -∗ ⧗ hc.pc -∗
      WalFs.walLenLb w dir (h.H.length + 1) -∗
      (∃ d : WalDur, Q d ∗ ⌜d.H = h.H⌝) -∗
      (⌜walMustSync (h.H.map WalOpG.toM) hs es⌝ -∗ WalFs.walSyncedLb dir (h.H.length + 1)) -∗
      (walHdl (W := W) Sio P Mr w dir ∗ ∃ d : WalDur, Q d ∗ WalFs.walLenLb w dir (d.H.length + 1) ∗
        (⌜walMustSync (d.H.map WalOpG.toM) hs es⌝ -∗ WalFs.walSyncedLb dir (d.H.length + 1))) := by
  iintro Hh Hr #Hlb ⟨%d, HQ, %hd⟩ Hs
  isplitl [Hh Hr]
  · iapply walHdl_close Sio P Mr w dir hc hD hmd hroom
    iframe Hh Hr
  iexists d
  rw [hd]
  iframe HQ Hlb Hs

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.wp_proof [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] [FsStepSat (NoMapLockErr Sio)]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr)
    (wp_syncNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specNoErr (Sio := Sio) (W := W) P Mr)
    (wp_saveEntry : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.spec (W := W) P Mr)
    (wp_saveEntryNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.specNoErr (Sio := Sio) (W := W) P Mr)
    (wp_saveState : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.spec (W := W) P Mr)
    (wp_saveStateNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.specNoErr (Sio := Sio) (W := W) P Mr)
    (wp_encodeState : go_etcd_io.etcd.server.v3.storage.wal.WAL.encodeState.spec (W := W) P Mr)
    (wp_encodeStateNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.encodeState.specNoErr (Sio := Sio) (W := W) P Mr)
    (wp_marshal : WalPbIn.MarshalHsLaw P Mr)
    (wp_cut : go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.spec (Sio := Sio) (W := W) P Mr)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_empty : WalPbIn.IsEmptyLaw (GF := GF) (hG := hG) P)
    (wp_mustSync : WalPbIn.MustSyncLaw (GF := GF) (hG := hG) P)
    (hzero : WalPbIn.ZeroLaw (GF := GF) (hG := hG) P) (hzst : WalPbIn.ZeroStLaw (GF := GF) (hG := hG) P Mr)
    (wp_size : WalPbIn.SizeLaw (GF := GF) (hG := hG) P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.spec (Sio := Sio) (W := W) P Mr := by
  intro R jr r w dir γ q hp hs sl esL es sized Q hcov
  wp_start as ⟨#Harea, Hw, %hq, #Hhs, #Hsl, Hes, %hidx, %hsz, Hau⟩
  icases walOpenWS_pers Sio P Mr w dir γ q $$ Hw with ⟨Hw, #Hpers⟩
  icases walShPers_facts Sio P Mr w dir γ $$ Hpers with ⟨#Hmu, #Hsync, #Hseg⟩
  ihave %hS := walAreaOk_encState walCodec Mr R jr r $$ Harea
  ihave %hlen := ownSlice_len $$ Hsl
  iunfold walEntsIn at Hes
  icases Hes with #Hes
  ihave %hlen2 := BigSepL2.bigSepL2_length $$ Hes
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- fix 0009: the batch's bytes (`saveBatchBytes`), summed before the lock; past `MaxSaveBatchBytes`, refused
  ihave #Hwpk := walShPers_pkgInit Sio P Mr w dir γ $$ Hpers
  ihave #Hwi : (wal.walInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hwpk
  ihave #Hmax := wal.walInit_maxSaveBatch $$ Hwi
  ihave #Hbl := wal.walInit_ErrSaveBatchTooLarge $$ Hwi
  ihave #Hpr : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave HL : (∃ (j : w64) (nb : w64) (ep : Loc),
      "i" ∷ i_ptr ↦ j ∗ "n" ∷ n_ptr ↦ nb ∗ "e" ∷ e_ptr ↦ ep ∗
      "%Hn" ∷ ⌜sint.Z nb = saveBatchBytes Mr (es.take (sint.nat j)) ∧
        saveBatchBytes Mr (es.take (sint.nat j)) ≤ maxSaveBatch⌝ ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ es.length⌝ : IProp GF) $$ [i n e]
  · iexists W64 0, W64 0, _
    iframe
    ipureintro
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, saveBatchBytes, maxSaveBatch]
    simp
  wp_for HL
  by_cases Hlt : sint.Z j < sint.Z sl.len
  · -- an entry: its `proto.Size` added
    rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    have hjl : sint.nat j < es.length := by
      have : sint.nat j = (sint.Z j).toNat := rfl
      have : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
      omega
    obtain ⟨l, hl⟩ : ∃ l, esL[sint.nat j]? = some l :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e, he⟩ : ∃ e, es[sint.nat j]? = some e :=
      ⟨_, List.getElem?_eq_getElem hjl⟩
    ihave #Hel := BigSepL2.bigSepL2_lookup hl he $$ Hes
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hlt⟩
    (try wp_auto)
    (try simp only [hb, _root_.and_self, decide_true, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z j) esL DFrac.discard l Hj.1 $$ [Hsl] as -
    · iframe #; ipureintro; exact hl
    (try wp_auto)
    wp_apply (wp_size l e) $$ [] as %sz %Hsz
    · iframe #
    (try wp_auto)
    have hesz := hsz e (List.mem_of_getElem? he)
    have hszv : sint.Z sz = (Mr.encEntry e).length := Hsz (by omega)
    have htake : saveBatchBytes Mr (es.take (sint.nat j + 1)) =
        saveBatchBytes Mr (es.take (sint.nat j)) + ((Mr.encEntry e).length + 64) := by
      unfold saveBatchBytes
      rw [List.take_add_one, he]
      simp
    have hn1 : sint.Z (nb + (sz + W64 64)) = saveBatchBytes Mr (es.take (sint.nat j + 1)) := by
      rw [htake]
      have := Hn.1; have := Hn.2
      unfold maxSaveBatch at *
      word
    rw [show sz + W64 64 = sz + W64 64 from rfl]
    wp_if_destruct
    · -- refused: nothing committed, the share back
      have hbig : maxSaveBatch < saveBatchBytes Mr es := by
        have h1 := Hif
        rw [hn1, show sint.Z (W64 4398046511104) = 4398046511104 from rfl] at h1
        have h2 := congrArg List.sum
          (List.take_append_drop (sint.nat j + 1) (es.map (fun e => (Mr.encEntry e).length + 64)))
        rw [List.sum_append] at h2
        unfold saveBatchBytes maxSaveBatch at *
        rw [List.map_take] at h1
        omega
      iunfold wal.errVar at Hbl
      icases Hbl with ⟨%eb, #Heb, -, -⟩
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      iapply HΦ
      iright
      iright
      iframe Hw
      ipureintro
      exact ⟨by simp, hbig⟩
    · wp_for_post
      iframe
      iexists j + W64 1, _, _
      iframe
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      ipureintro
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [hj1, ← hn1]
      · have h1 := Hif
        rw [hn1, show sint.Z (W64 4398046511104) = 4398046511104 from rfl] at h1
        rw [hj1]; unfold maxSaveBatch; omega
      · word
      · omega
  rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
  have hje0 : sint.nat j = es.length := by
    have : sint.nat j = (sint.Z j).toNat := rfl
    have : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
    omega
  have hfit : saveBatchBytes Mr es ≤ maxSaveBatch := by
    have h1 := Hn.2
    rwa [hje0, List.take_length] at h1
  ispecialize Hau $$ %hfit
  (try wp_auto)
  wp_apply +noauto sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  -- the deferred `w.mu.Unlock`'s resolution: its later credit takes the handle out of the share
  wp_to_resolve
  first
    | wp_bind (App (Val (GoInstruction (FuncResolve _ _))) (Val _))
    | wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
  iapply wp_go_step_receipt'
  case hv => exact isPanic_intoVal _
  inext
  iintro - Hlc
  iapply wp_value'
  iapply fupd_wp
  imod walOpenWS_acquire Sio P Mr w dir γ q $$ [Hw Hlocked Hlc] with ⟨-, Hheld, Hh⟩
  · iframe Hw Hlocked Hlc
  imodintro
  icases walHdl_open Sio P Mr w dir $$ Hh with ⟨%h, Hh, %hD, %hmd, Hr, %hroom⟩
  icases walHandleIn_idx P Mr w dir h TailMetaW $$ Hh with ⟨Hh, %hix⟩
  icases walHandleIn_pkgInit P Mr w dir h TailMetaW $$ Hh with ⟨Hh, #Hwpk0⟩
  have hix0 := hix.1 hD.1
  -- the WALs' step bound at a look (`⧖ |H|`), raised by the next resolution's receipt, deposited by the
  -- commit right after it (`notes/bounds-plan.md`, "The WAL's segment sequence")
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walHandleIn_steps P Mr R jr r w dir h TailMetaW $$ Harea Hnc Hh with ⟨Hnc, Hh, #Hst⟩
  imodintro
  iframe Hnc
  wp_raise_receipt Hst
  -- the commit
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  have hwop : wop h.H (WalOpG.save hs es).toRaw =
      (WalOpG.save (saveHS (walLastHS (h.H.map WalOpG.toM)) hs es) es).toRaw.toM := by
    rw [wop, WalOpG.toM_toRaw, WalOpG.toM_toRaw, normOp_save_eq]
  imod walHandleIn_append P Mr R jr r w dir h (WalOpG.save hs es).toRaw sized
    Q hD.1
    (fun c => by rw [hwop]; exact saveOp_fit Mr _ es (hS _) hsz c)
    (fun a b => by
      have hi := saveOp_idx Mr h.H hs es _ _ a b
      refine ⟨fun h0 => hi.1 ?_, hi.2⟩
      rw [hwop, WalOpG.toM_toRaw] at h0
      rw [WalOpG.toM_toRaw]
      have hes : es = [] := by
        simp only [opDs, List.length_append, List.length_map] at h0
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hes
      simpa [saveHS] using h0)
    (saveOp_noMax hs es hidx) TailMetaW $$ Harea Hnc Hh Hau Hst with ⟨Hnc, Hh, #Hlb, HQ, %hcp⟩
  imodintro
  iframe Hnc
  icases HQ with ⟨%dq, HQ, %hdq⟩
  ihave HQ : (∃ d : WalDur, Q d ∗ ⌜d.H = h.H⌝) $$ [HQ]
  · iexists dq; iframe HQ; ipureintro; exact hdq
  have hcut : ∀ b ∈ h.cuts, b ≤ h.H.length := fun b hb => by
    rcases hcp.1 b hb with h0 | ⟨_, _, h1, _⟩ | ⟨_, _, h1⟩
    · omega
    · have := (List.getElem?_eq_some_iff.1 h1).1; simp at this; omega
    · have := (List.getElem?_eq_some_iff.1 h1).1; simp at this; omega
  have hs0 := SaveSt.init Mr h hs es
  have hroom1 : walCov Sio →
      ({ h with H := h.H ++ [(WalOpG.save hs es).toRaw], rest := (opDs Mr (wop h.H (WalOpG.save hs es).toRaw)).length } : WalHS).o0 +
      ({ h with H := h.H ++ [(WalOpG.save hs es).toRaw], rest := (opDs Mr (wop h.H (WalOpG.save hs es).toRaw)).length } : WalHS).out.length +
      ({ h with H := h.H ++ [(WalOpG.save hs es).toRaw], rest := (opDs Mr (wop h.H (WalOpG.save hs es).toRaw)).length } : WalHS).pend.length +
      walFreshRoom ≤ maxBytes := hroom
  generalize ({ h with H := h.H ++ [(WalOpG.save hs es).toRaw], rest := (opDs Mr (wop h.H (WalOpG.save hs es).toRaw)).length } : WalHS) = h1 at hs0 hroom1 ⊢
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
  obtain ⟨c, rfl, hcms⟩ := Hv
  cases c
  rotate_left
  · -- the shortcut: nothing written, the committed handle quiescent
    obtain ⟨hse, rfl⟩ := hcms.1 rfl
    have hf := SaveSt.finEmpty hs0 hD ⟨rfl, hse⟩
    rw [← hs0.pc]
    ihave ⟨Hhdl, Hpost⟩ := save_post (Sio := Sio) P Mr w dir γ hs [] Q h h1 hf.done
      (by rw [hf.md]; exact hmd) hroom1 $$ Hh Hr Hlb HQ []
    · iintro %hm
      exfalso
      rcases hm with hm | ⟨hm, -⟩
      · exact hm rfl
      · exact hm hse
    wp_auto
    iapply fupd_wp
    imod walOpenWS_release Sio P Mr w dir γ q $$ [Hheld Hhdl] with ⟨Hw, Hlocked⟩
    · iframe Hpers Hheld Hhdl
    imodintro
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iframe Hw Hpost
  have hne : ¬ (es = [] ∧ hsEmptyP hs) := fun h => by simpa using hcms.2 ⟨h.2, h.1⟩
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
  icases walHandleIn_stateNil P Mr w dir h1 TailMetaW $$ Hh with ⟨%sp, Hsp, #Hst, Hback⟩
  wp_join iprop(w_ptr ↦ w ∗ ∃ sp' : Loc,
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp' ∗ walStIn P Mr sp' h1.st ∗
      ⌜sp' ≠ null⌝)
    at (if: _ then _ else _) with [Hsp w] as ⟨w, %sp', Hsp, #Hst', %hsp'n⟩
  · iapply wp_fupd
    (try wp_auto)
    wp_if_destruct
    · ihave #Hst0 : P.hsIn null h1.st $$ []
      · iunfold walStIn at Hst; icases Hst with ⟨#H1, -, -⟩; iexact H1
      ihave %hz0 := hzero.1 _ $$ Hst0
      icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr0, %hn⟩
      imod hzst _ ⊤ $$ Hr0 with ⟨#Hz, #Hzm⟩
      imodintro
      isplitr
      · ipureintro; trivial
      iframe w; iexists «$r0_ptr»; rw [hz0]; iframe Hsp
      isplitl
      · iapply walStIn_intro P Mr _ hsZero false hn; iframe Hz Hzm
      · ipureintro; exact hn
    · imodintro
      isplitr
      · ipureintro; trivial
      iframe w; iexists sp; iframe Hsp
      isplitl
      · iapply walStIn_set P Mr sp h1.st h1.stNil false Hif; iexact Hst
      · ipureintro; exact Hif
  ihave #Hst'h : P.hsIn sp' h1.st $$ []
  · iunfold walStIn at Hst'; icases Hst' with ⟨#H1, -, -⟩; iexact H1
  -- `MustSync`
  wp_apply (wp_mustSync hp' sp' hs h1.st sl.len) $$ [] as %ms %hms
  · iframe Hhs' Hst'h
  ihave Hh := Hback $$ Hsp Hst'
  rename_i _ i_ptr_1
  have hst1 : h1.st = walLastHS (h.H.map WalOpG.toM) := hs0.st.trans hD.2
  have hsl : sint.nat sl.len = es.length := by omega
  have hk : walCov Sio → saveRoom Mr (saveHS (walLastHS (h.H.map WalOpG.toM)) hs es) es ≤ walFreshRoom :=
      fun _ => by
    have h1 := hfit
    have h2 := hS (saveHS (walLastHS (h.H.map WalOpG.toM)) hs es)
    unfold saveRoom walFreshRoom maxBytes
    unfold saveBatchBytes maxSaveBatch at h1
    omega
  -- the entries' records: after `j` of them, the handle at `SaveSt … j`, with room for the rest when covered
  ihave HI : (∃ (j k0 : w64) (hc : WalHS),
      "i" ∷ i_ptr ↦ j ∗ "i0" ∷ i_ptr_1 ↦ k0 ∗ "Hh" ∷ walHandleIn P Mr w dir hc TailMetaW ∗
      "%Hs" ∷ ⌜SaveSt Mr h hs es (sint.nat j) hc⌝ ∗
      "%Hroom" ∷ ⌜walCov Sio → hc.o0 + hc.out.length + hc.pend.length +
        (((es.drop (sint.nat j)).map (fun e => (Mr.encEntry e).length + 64)).sum +
          ((Mr.encState (saveHS (walLastHS (h.H.map WalOpG.toM)) hs es)).length + 64)) ≤ maxBytes⌝ ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ es.length⌝ ∗ "%Hnil" ∷ ⌜hc.stNil = false⌝ : IProp GF)
    $$ [-HΦ Hr HQ Hheld «$res0» w defer ents st mustSync]
  · iexists W64 0, _, { h1 with stNil := false }
    iframe
    ipureintro
    refine ⟨⟨hs0.H, hs0.md, hs0.cuts, hs0.rest, hs0.st, hs0.snapi, hs0.pc, hs0.enti0, hs0.entiS⟩, ?_,
      ⟨by decide, Nat.zero_le _⟩, rfl⟩
    intro hc
    have := hk hc
    have := hroom1 hc
    unfold saveRoom at *
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    omega
  wp_for HI
  by_cases Hlt : sint.Z j < sint.Z sl.len
  · -- an entry
    rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    have hjl : sint.nat j < es.length := by
      have : sint.nat j = (sint.Z j).toNat := rfl
      have : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
      omega
    obtain ⟨l, hl⟩ : ∃ l, esL[sint.nat j]? = some l :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e, he⟩ : ∃ e, es[sint.nat j]? = some e :=
      ⟨_, List.getElem?_eq_getElem hjl⟩
    ihave #Hel := BigSepL2.bigSepL2_lookup hl he $$ Hes
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hlt⟩
    (try wp_auto)
    (try simp only [hb, _root_.and_self, decide_true, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z j) esL DFrac.discard l Hj.1 $$ [Hsl] as -
    · iframe #; ipureintro; exact hl
    (try wp_auto)
    (try simp only [hb, _root_.and_self, decide_true, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z j) esL DFrac.discard l Hj.1 $$ [Hsl] as -
    · iframe #; ipureintro; exact hl
    (try wp_auto)
    obtain ⟨hpos, hlast, hrec⟩ := Hs.entryPre hcut hix.2 e he
    have hei : uint.nat e.Index' < 2 ^ 64 - 1 := hidx e (List.mem_of_getElem? he)
    have hdrop := save_drop_sum Mr es (sint.nat j) e he
    wp_apply (walCov_saveEntry P Mr wp_saveEntry wp_saveEntryNE R jr r w dir hc l e hpos hei
      (hsz e (List.mem_of_getElem? he)) hlast hrec (fun hc => by have := Hroom hc; omega)) $$ [Hh]
      as %err Hres
    · iframe Harea Hh Hel
    icases Hres with (⟨%herr, %out', %pend', %sz', Hh, %hlen'⟩ | %herr)
    · subst herr
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _, _
      iframe
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      ipureintro
      refine ⟨?_, ?_, ⟨?_, ?_⟩, Hnil⟩
      · rw [hj1]; exact Hs.step e he out' pend' sz'
      · intro hc; have := Hroom hc; have := hlen' hc; rw [hj1]; simp only; omega
      · word
      · omega
    · rcases err with ei | _
      rotate_left
      · exact absurd rfl herr.1
      (try wp_auto)
      wp_for_post
      have hq1 : q = 1 := hq.resolve_left (herr).2
      subst hq1
      iapply fupd_wp
      imod walOpenWS_finish Sio P Mr w dir γ $$ [Hheld] with Hlocked
      · iframe Hpers Hheld
      imodintro
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
      (try wp_auto)
      iapply HΦ
      iright
      ileft
      isplitr
      · ipureintro; exact herr
      icases HQ with ⟨%d, HQ, -⟩
      iexists d; iexact HQ
  -- the entries done
  rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
  have hje : sint.nat j = es.length := by
    have : sint.nat j = (sint.Z j).toNat := rfl
    have : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
    omega
  rw [hje] at Hs Hroom
  simp only [List.drop_length, List.map_nil, List.sum_nil, Nat.zero_add] at Hroom
  (try wp_auto)
  -- the state's record (fork `2bd3048d7`): `if len(ents) > 0 { if IsEmptyHardState(st) { st = w.state };
  -- encodeState(st) } else { saveState(st) }`, joined at the handle after it or the error's return
  have hpre := Hs.statePre hcut hix0 hix.2 hne
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ w_ptr ↦ w ∗ (∃ e0 : GoInterface, «$res0_ptr» ↦ e0) ∗
      ∃ hc2 : WalHS, walHandleIn P Mr w dir hc2 TailMetaW ∗
        ⌜SaveFin h hs es hc2 ∧ (walCov Sio → hc2.o0 + hc2.out.length + hc2.pend.length ≤ maxBytes)⌝) ∨
      (⌜v = returnVal #()⌝ ∗ w_ptr ↦ w ∗ ∃ err : GoInterface, «$res0_ptr» ↦ err ∗
        ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝))) at next
    with [Hh st w «$res0»]
  · (try wp_auto)
    wp_if_destruct
    · -- entries: the state record of `saveHS`, `w.state`'s when `st` is empty
      have hes : es ≠ [] := by
        intro h0
        have h1 := (save_slen_zero sl esL hlen.1 hlen.2).2 (by
          rw [← List.length_eq_zero_iff, hlen2, List.length_eq_zero_iff]; exact h0)
        rw [h1] at Hif; simp at Hif
      wp_join iprop(∃ hp2 : Loc, st_ptr ↦ hp2 ∗ w_ptr ↦ w ∗ walHandleIn P Mr w dir hc TailMetaW ∗
          walStIn P Mr hp2 (saveHS (walLastHS (h.H.map WalOpG.toM)) hs es) ∗ ⌜hp2 ≠ null⌝)
        at (if: _ then _ else _) with [st w Hh] as ⟨%hp2, st, w, Hh, #Hst2, %hp2n⟩
      · iapply wp_fupd
        (try wp_auto)
        wp_apply (wp_empty hp' hs) $$ [] as %b2 %hb2
        · iexact Hhs'
        cases b2
        · -- `st` not empty: itself
          have hse : ¬ hsEmptyP hs := fun h0 => Bool.false_ne_true (hb2.2 h0)
          have hsv : saveHS (walLastHS (h.H.map WalOpG.toM)) hs es = hs := by
            unfold saveHS; simp [hse]
          (try wp_auto)
          ihave #Hst2 : walStIn P Mr hp' hs $$ []
          · iapply walStIn_intro P Mr hp' hs false hp'n
            iframe Hhs'
            unfold walStMarsh
            iintro !> %Φ' #Hpk Hk
            wp_apply (wp_marshal hp' hs hse) $$ [] as %d ⟨Hd, %Hdn⟩
            · iexact Hhs'
            iapply Hk $$ [Hd]
            · iexact Hd
            · ipureintro; exact Hdn
          imodintro
          isplitr
          · ipureintro; trivial
          iexists hp'; rw [hsv]; iframe st w Hh Hst2; ipureintro; exact hp'n
        · -- `st` empty: `w.state`, the last state saved
          have hse : hsEmptyP hs := hb2.1 rfl
          have hst2 : hc.st = saveHS (walLastHS (h.H.map WalOpG.toM)) hs es := by
            rw [Hs.st, hD.2]; unfold saveHS; simp [hes, hse]
          icases walHandleIn_state P Mr w dir hc TailMetaW $$ Hh with ⟨%sp2, Hsp2, #Hst2, Hback2⟩
          ihave #Hst2f : walStIn P Mr sp2 hc.st false $$ []
          · rw [← Hnil]; iexact Hst2
          ihave ⟨%hn2, -, -⟩ := walStIn_nn P Mr sp2 hc.st $$ Hst2f
          (try wp_auto)
          ihave Hh := Hback2 $$ Hsp2 Hst2
          imodintro
          isplitr
          · ipureintro; trivial
          iexists sp2; rw [← hst2]; iframe st w Hh Hst2f; ipureintro; exact hn2
      wp_apply (walCov_encodeState P Mr wp_encodeState wp_encodeStateNE R jr r w dir hc hp2 _
          hpre.1 hpre.2.1 hpre.2.2 Hroom) $$ [Hh] as %err Hres
      · iframe Harea Hh Hst2; ipureintro; exact hp2n
      icases Hres with (⟨%herr, %out', %pend', %sz', Hh, %hlen'⟩ | %herr)
      · subst herr
        (try wp_auto)
        ileft
        isplitr
        · ipureintro; rfl
        iframe w
        isplitl [«$res0»]
        · iexists _; iexact «$res0»
        iexists _; iframe Hh; ipureintro
        exact ⟨Hs.finState hne out' pend' sz', fun hc => by
          have := Hroom hc; have := hlen' hc; simp only; omega⟩
      · rcases err with ei | _
        rotate_left
        · exact absurd rfl herr.1
        (try wp_auto)
        iright
        isplitr
        · ipureintro; rfl
        iframe w
        iexists _; iframe «$res0»; ipureintro; exact herr
    · -- no entries: `saveState(st)`, `st` not empty
      have hes : es = [] := by
        have h1 : sl.len = W64 0 := by word
        have := (save_slen_zero sl esL hlen.1 hlen.2).1 h1
        rw [← List.length_eq_zero_iff, ← hlen2, List.length_eq_zero_iff]; exact this
      subst hes
      have hse : ¬ hsEmptyP hs := fun h0 => hne ⟨rfl, h0⟩
      have hsv : saveHS (walLastHS (h.H.map WalOpG.toM)) hs [] = hs := by unfold saveHS; simp
      rw [hsv] at hpre Hroom
      wp_apply (walCov_saveState P Mr wp_saveState wp_saveStateNE R jr r w dir hc hp' hs
        (fun _ => hpre) Hroom) $$ [Hh] as %err Hres
      · iframe Harea Hh Hhs'; ipureintro; exact hp'n
      icases Hres with (⟨⟨%herr, %hse'⟩, Hh⟩ | ⟨⟨%herr, %-⟩, %out', %pend', %sz', Hh, %hlen'⟩ | %herr)
      · exact absurd hse' hse
      · subst herr
        (try wp_auto)
        ileft
        isplitr
        · ipureintro; rfl
        iframe w
        isplitl [«$res0»]
        · iexists _; iexact «$res0»
        iexists _; iframe Hh; ipureintro
        have hf := Hs.finState hne out' pend' sz'
        rw [hsv] at hf
        exact ⟨hf, fun hc => by have := Hroom hc; have := hlen' hc; simp only; omega⟩
      · rcases err with ei | _
        rotate_left
        · exact absurd rfl herr.1
        (try wp_auto)
        iright
        isplitr
        · ipureintro; rfl
        iframe w
        iexists _; iframe «$res0»; ipureintro; exact herr
  iintro (⟨%Hv, w, ⟨%e0, «$res0»⟩, %hc2, Hh, %hf2⟩ | ⟨%Hv, w, %err, «$res0», %herr⟩)
  rotate_left
  · subst Hv
    have hq1 : q = 1 := hq.resolve_left (herr).2
    subst hq1
    iapply fupd_wp
    imod walOpenWS_finish Sio P Mr w dir γ $$ [Hheld] with Hlocked
    · iframe Hpers Hheld
    imodintro
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    iright
    ileft
    isplitr
    · ipureintro; exact herr
    icases HQ with ⟨%d, HQ, -⟩
    iexists d; iexact HQ
  subst Hv
  obtain ⟨hf, hroom2⟩ := hf2
  (try wp_auto)
  -- the tail's offset
  icases walHandleIn_pure P Mr w dir hc2 TailMetaW $$ Hh with ⟨Hh, %hpu2⟩
  icases walHandleIn_seek P Mr w dir hc2 TailMetaW $$ Hh with
    ⟨%locks, %ls, %lt, %f, %fd, %name, Hlocks, Hls, #Hltf, Hf, Hoff, %hsk, Hback⟩
  wp_apply (wp_tail w locks ls lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
  · iframe
  ihave #Hlt0 := Hltf
  iunfold fileutil.lockedFile at Hlt0
  iStructNamed Hlt0
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) (m := go!"Seek")]
  wp_call
  (try wp_auto)
  obtain ⟨ho1, ho2, ho3⟩ := save_off_toInt hc2.o0 hc2.out.length hsk.2
  wp_apply (os.File.Seek.wp_cur f fd name (DFrac.own 1) _ hsk.1 ho1 ho2) $$ [$Hf $Hoff] as ⟨Hf, Hoff⟩
  ihave Hh := Hback $$ Hlocks Hls Hf Hoff
  (try wp_auto)
  have hlenH : hc2.H.length = h.H.length + 1 := by rw [hf.H]; simp
  rw [← hf.pc]
  by_cases Hif : sint.Z (W64 ((hc2.o0 : Int) + (hc2.out.length : Int))) < sint.Z (W64 64000000)
  · -- below the segment size: `sync` if `MustSync`
    rw [decide_eq_true Hif]
    wp_auto
    wp_if_destruct
    · -- no sync due
      ihave ⟨Hhdl, Hpost⟩ := save_post (Sio := Sio) P Mr w dir γ hs es Q h hc2 hf.done
        (by rw [hf.md]; exact hmd)
        (fun hc => save_room_small _ _ _ (by
          have := save_hif hc2.o0 hc2.out.length ho3 Hif; have := hroom2 hc; omega))
        $$ Hh Hr Hlb HQ []
      · iintro %hm
        exfalso
        refine not_walMustSync _ _ _ ?_ hm
        rw [← hst1]
        intro hx
        have hnot : ¬ (sl.len ≠ W64 0 ∨ hs.Vote' ≠ h1.st.Vote' ∨ hs.Term' ≠ h1.st.Term') :=
          fun hy => absurd (hms.2 hy) (by decide)
        apply hnot
        rcases hx with hx | hx
        · left
          intro h0
          apply hx
          rw [← List.length_eq_zero_iff, ← hlen2, List.length_eq_zero_iff]
          exact (save_slen_zero sl esL hlen.1 hlen.2).1 h0
        · right; exact hx
      iapply fupd_wp
      imod walOpenWS_release Sio P Mr w dir γ q $$ [Hheld Hhdl] with ⟨Hw, Hlocked⟩
      · iframe Hpers Hheld Hhdl
      imodintro
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
      (try wp_auto)
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iframe Hw Hpost
    · wp_apply (walCov_sync P Mr wp_sync wp_syncNE R jr r w dir hc2 hf.rest hroom2) $$ [Hh] as %err Hres
      · iframe Harea Hh
      icases Hres with (⟨%herr, Hh, #Hsyn⟩ | %herr)
      · subst herr
        ihave Hh := walHandleIn_win P Mr w dir _ $$ Hh
        ihave ⟨Hhdl, Hpost⟩ := save_post (Sio := Sio) P Mr w dir γ hs es Q h
          { hc2 with out := hc2.out ++ hc2.pend, pend := [], sz := max hc2.sz (hc2.o0 + hc2.out.length + hc2.pend.length) }
          ⟨hf.rest, hf.st⟩ (by simp only; rw [hf.md]; exact hmd)
          (fun hc => save_room_small _ _ _ (by
            have := save_hif hc2.o0 hc2.out.length ho3 Hif
            have := hroom2 hc
            simp only [List.length_append, List.length_nil]; omega))
          $$ Hh Hr Hlb HQ []
        · iintro -
          rw [hlenH]; iexact Hsyn
        iapply fupd_wp
        imod walOpenWS_release Sio P Mr w dir γ q $$ [Hheld Hhdl] with ⟨Hw, Hlocked⟩
        · iframe Hpers Hheld Hhdl
        imodintro
        (try wp_auto)
        wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
        (try wp_auto)
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        iframe Hw Hpost
      · rcases err with ei | _
        rotate_left
        · exact absurd rfl herr.1
        have hq1 : q = 1 := hq.resolve_left (herr).2
        subst hq1
        iapply fupd_wp
        imod walOpenWS_finish Sio P Mr w dir γ $$ [Hheld] with Hlocked
        · iframe Hpers Hheld
        imodintro
        (try wp_auto)
        wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
        (try wp_auto)
        iapply HΦ
        iright
        ileft
        isplitr
        · ipureintro; exact herr
        icases HQ with ⟨%d, HQ, -⟩
        iexists d; iexact HQ
  · -- at the segment size: `cut`
    rw [decide_eq_false Hif]
    wp_take_receipt as Hr1
    ihave Hr2 := (receipt_add hc2.pc 1).2 $$ [Hr Hr1]
    · iframe
    icases save_pc_bound Mr R jr r hc2.pc $$ Harea Hr2 with ⟨Hr2, %hpc⟩
    have hcuts : ∀ b ∈ hc2.cuts, b < hc2.H.length := fun b hb => by
      rw [hf.cuts] at hb; have := hcut b hb; omega
    have hpw : hc2.cuts.Pairwise (· < ·) := by rw [hf.cuts]; exact hcp.2
    have hcpos : walCutPos (hc2.H.map WalOpG.toM) hc2.H.length := by
      rw [hf.H]; exact walCutPos_save h.H hs es (fun h0 => hne ⟨h0.2, h0.1⟩)
    have hsz2 : hc2.md.length + (Mr.encState hc2.st).length < 2 ^ 42 := by
      have := hS hc2.st; rw [hf.md]; omega
    wp_apply (wp_cut R jr r w dir hc2 hf.rest hf.st hpc hcuts hpw hcpos
      (by rw [hf.H]; simp) hsz2 hcov hroom2) $$ [Hh] as %err Hres
    · iframe Harea Hh
    icases Hres with (⟨%herr, %h', Hh, %hh', #Hsyn⟩ | %herr)
    · obtain ⟨hH', hmd', hcuts', hrest', hst', -, -, hpc', hroom'⟩ := hh'
      subst herr
      rw [← hpc'] at *
      ihave Hh := walHandleIn_win P Mr w dir _ $$ Hh
      ihave ⟨Hhdl, Hpost⟩ := save_post (Sio := Sio) P Mr w dir γ hs es Q h h'
        ⟨hrest', by rw [hst', hH']; exact hf.st⟩
        (by rw [hmd', hf.md]; exact hmd) (fun _ => save_room_small _ _ _ hroom') $$ Hh Hr2 Hlb HQ []
      · iintro -
        rw [hlenH]; iexact Hsyn
      iapply fupd_wp
      imod walOpenWS_release Sio P Mr w dir γ q $$ [Hheld Hhdl] with ⟨Hw, Hlocked⟩
      · iframe Hpers Hheld Hhdl
      imodintro
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
      (try wp_auto)
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iframe Hw Hpost
    · rcases err with ei | _
      rotate_left
      · exact absurd rfl herr.1
      have hq1 : q = 1 := hq.resolve_left (herr).2
      subst hq1
      iapply fupd_wp
      imod walOpenWS_finish Sio P Mr w dir γ $$ [Hheld] with Hlocked
      · iframe Hpers Hheld
      imodintro
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
      (try wp_auto)
      iapply HΦ
      iright
      ileft
      isplitr
      · ipureintro; exact herr
      icases HQ with ⟨%d, HQ, -⟩
      iexists d; iexact HQ

end proof

end EtcdGrove
end Perennial
