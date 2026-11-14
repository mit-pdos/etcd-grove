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
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.StreamBound
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

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.wp_proof [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
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
  icases walHandleIn_idx P Mr w dir h TailMetaW $$ Hh with ⟨Hh, %hix⟩
  icases walHandleIn_lockFacts P Mr w dir h TailMetaW $$ Hh with ⟨Hh, #Hmu, #Hsync, #Hseg⟩
  icases walHandleIn_pure P Mr w dir h TailMetaW $$ Hh with ⟨Hh, %hpu0⟩
  have hix0 := hix.1 hD.1
  -- the commit, before the call's first step
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walHandleIn_append P Mr R jr r w dir h (WalOpG.save hs es).toRaw sized Q hD.1
    (saveOp_fit Mr hs es (hS hs) hsz) (fun a b => saveOp_idx Mr h.H hs es _ _ a b)
    TailMetaW $$ Harea Hnc Hh Hau with ⟨Hnc, Hh, #Hlb, HQ, %hcp⟩
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
    iapply save_post P Mr w dir hs [] Q h h1 hf.done (by rw [hf.md]; exact hmd)
      $$ Hh Hr Hlb HQ
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
  icases walHandleIn_state P Mr w dir h1 TailMetaW $$ Hh with ⟨%sp, Hsp, #Hst, Hback⟩
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
  rename_i _ i_ptr_1
  have hst1 : h1.st = walLastHS (h.H.map WalOpG.toM) := hs0.st.trans hD.2
  have hsl : sint.nat sl.len = es.length := by omega
  -- the entries' records: after `j` of them, the handle at `SaveSt … j`
  ihave HI : (∃ (j k0 : w64) (hc : WalHS),
      "i" ∷ i_ptr ↦ j ∗ "i0" ∷ i_ptr_1 ↦ k0 ∗ "Hh" ∷ walHandleIn P Mr w dir hc TailMetaW ∗
      "%Hs" ∷ ⌜SaveSt Mr h hs es (sint.nat j) hc⌝ ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ es.length⌝ : IProp GF)
    $$ [-HΦ Hr HQ «$res0» w Hlocked defer ents st mustSync]
  · iexists W64 0, _, h1
    iframe
    ipureintro
    exact ⟨hs0, by decide, Nat.zero_le _⟩
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
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z j) esL DFrac.discard l Hj.1 $$ [Hsl] as -
    · iframe #; ipureintro; exact hl
    (try wp_auto)
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z j) esL DFrac.discard l Hj.1 $$ [Hsl] as -
    · iframe #; ipureintro; exact hl
    (try wp_auto)
    obtain ⟨hpos, hlast, hrec⟩ := Hs.entryPre hcut hix.2 e he
    have hei : uint.nat e.Index' < 2 ^ 64 - 1 := hidx e (List.mem_of_getElem? he)
    wp_apply (wp_saveEntry R jr r w dir hc l e hpos hei hlast hrec) $$ [Hh] as %err Hres
    · iframe Harea Hh Hel
    icases Hres with (⟨%herr, %out', %pend', %sz', Hh⟩ | %herr)
    · subst herr
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _, _
      iframe
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      ipureintro
      refine ⟨?_, ?_, ?_⟩
      · rw [hj1]; exact Hs.step e he out' pend' sz'
      · word
      · omega
    · rcases err with ei | _
      rotate_left
      · exact absurd rfl herr
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
      (try wp_auto)
      iapply HΦ
      iright
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
  rw [hje] at Hs
  (try wp_auto)
  -- the state's record
  wp_apply (wp_saveState R jr r w dir hc hp' hs (Hs.statePre hcut hix0 hix.2)) $$ [Hh] as %err Hres
  · iframe Harea Hh Hhs'; ipureintro; exact hp'n
  ihave Hres2 : (⌜err = GoInterface.nil⌝ ∗ ∃ hc2 : WalHS, walHandleIn P Mr w dir hc2 TailMetaW ∗
      ⌜SaveFin h hs es hc2⌝) ∨ ⌜err ≠ GoInterface.nil⌝ $$ [Hres]
  · icases Hres with (⟨⟨%herr, %hse⟩, Hh⟩ | ⟨⟨%herr, %hse⟩, %out', %pend', %sz', Hh⟩ | %herr)
    · ileft; iframe; ipureintro; exact ⟨herr, Hs.finEmpty hD hse⟩
    · ileft; isplitr
      · ipureintro; exact herr
      iexists _; iframe Hh; ipureintro; exact Hs.finState hse out' pend' sz'
    · iright; ipureintro; exact herr
  icases Hres2 with (⟨%herr, %hc2, Hh, %hf⟩ | %herr)
  rotate_left
  · rcases err with ei | _
    rotate_left
    · exact absurd rfl herr
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact herr
    icases HQ with ⟨%d, HQ, -⟩
    iexists d; iexact HQ
  subst herr
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
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
      (try wp_auto)
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iapply save_post P Mr w dir hs es Q h hc2 hf.done (by rw [hf.md]; exact hmd) $$ Hh Hr Hlb HQ
      iintro %hm
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
    · wp_apply (wp_sync R jr r w dir hc2 hf.rest) $$ [Hh] as %err Hres
      · iframe Harea Hh
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
      (try wp_auto)
      iapply HΦ
      icases Hres with (⟨%herr, Hh, #Hsyn⟩ | %herr)
      · ileft
        isplitr
        · ipureintro; exact herr
        ihave Hh := walHandleIn_win P Mr w dir _ $$ Hh
        iapply save_post P Mr w dir hs es Q h
          { hc2 with out := hc2.out ++ hc2.pend, pend := [], sz := max hc2.sz (hc2.o0 + hc2.out.length + hc2.pend.length) }
          ⟨hf.rest, hf.st⟩ (by simp only; rw [hf.md]; exact hmd)
          $$ Hh Hr Hlb HQ
        iintro -
        rw [hlenH]; iexact Hsyn
      · iright
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
      rw [hf.H]; exact walCutPos_save h.H hs es hne
    have hsz2 : hc2.md.length + (Mr.encState hc2.st).length < 2 ^ 42 := by
      have := hS hc2.st; rw [hf.md]; omega
    wp_apply (wp_cut R jr r w dir hc2 hf.rest hf.st hpc hcuts hpw hcpos hsz2) $$ [Hh] as %err Hres
    · iframe Harea Hh
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    icases Hres with (⟨%herr, %h', Hh, %hh', #Hsyn⟩ | %herr)
    · obtain ⟨hH', hmd', hcuts', hrest', hst', -, -, hpc'⟩ := hh'
      ileft
      isplitr
      · ipureintro; exact herr
      rw [← hpc'] at *
      ihave Hh := walHandleIn_win P Mr w dir _ $$ Hh
      iapply save_post P Mr w dir hs es Q h h' ⟨hrest', by rw [hst', hH']; exact hf.st⟩
        (by rw [hmd', hf.md]; exact hmd) $$ Hh Hr2 Hlb HQ
      iintro -
      rw [hlenH]; iexact Hsyn
    · iright
      isplitr
      · ipureintro; exact herr
      icases HQ with ⟨%d, HQ, -⟩
      iexists d; iexact HQ

end proof

end EtcdGrove
end Perennial
