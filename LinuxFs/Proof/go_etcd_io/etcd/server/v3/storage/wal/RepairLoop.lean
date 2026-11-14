/- Lean-first (no Rocq counterpart).

# What `Repair`'s `Decode` returns, by the loop's switch (law L2; W7 of `notes/wal-fsext-plan.md`, W7-W12 log,
fourteenth session)

`Repair`'s loop (S/repair.go:44-104) reads the last segment `F` alone (`RepairFile walCodec F.bs rs`) and
switches on `Decode`'s error: `nil` (a record), `errors.Is(err, io.EOF)`, `errors.Is(err,
io.ErrUnexpectedEOF)` (the truncate at `LastOffset()`, the offset `off` the failing `Decode` started at),
anything else. `repair_decNorm` puts `decPostB` (the decoder at `RepairAt walCodec rs off c`) in that
shape:

* a record: `goDecode`'s `.ok` step, the decoder live on `[F]`;
* `io.EOF`: the segment's stream back (`F.S`);
* any other error (a stop, a failed `Unmarshal`, a reader's I/O error): the stream back, and
  `errors.Is(err, io.ErrUnexpectedEOF)` answers `true` only if `off` is the end of the frames
  (`errUeAns`): on a stop and a failed `Unmarshal` because they are at the end (`repairAt_stop`,
  `repairAt_fail`), on an I/O error because it answers `false`.

The I/O arm (`errUeAns_ioe`, from the arm's `notUeof`, and the stream the arm now keeps) is proved
(`wal-vsnap2`, 2026-11-14); the answer on `Decode`'s own errors at the end of the frames (`errUeAns_end`: any,
since `errors.Is(err, io.ErrUnexpectedEOF)` returns, `Decode`'s `decUe`) since `wal-vsnap3` (2026-11-14; ledger,
"no `errors.Is(_, io.ErrUnexpectedEOF)` termination").
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairPre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecStreams
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllExit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecTerm

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section norm
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- **`errors.Is(err, io.ErrUnexpectedEOF)` answers `true` only if `P`** (persistent). -/
def errUeAns (err ueof : GoInterface) (P : Prop) : IProp GF :=
  iprop(□ {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #ueof))
    {{ (b : Bool), RET #b; ⌜b = true → P⌝ }})

instance errUeAns_persistent (err ueof : GoInterface) (P : Prop) :
    Persistent (errUeAns (GF := GF) err ueof P) := by
  unfold errUeAns; infer_instance

/-- The answer on a reader's I/O error: `false` (`notUeof`, which `Decode`'s I/O arm gives). -/
theorem errUeAns_ioe (ueof err : GoInterface) (P : Prop) :
    notUeof (GF := GF) err ∗ globalAddr _root_.Perennial.io.ErrUnexpectedEOF ↦□ ueof ⊢
      errUeAns err ueof P := by
  iintro ⟨#Hn, #Hu⟩
  iunfold notUeof at Hn
  icases Hn with ⟨#Hn, -⟩
  ihave #Hq := Hn $$ %ueof Hu
  unfold errUeAns
  iintro !> %Φ
  iintro !> - HΦ
  wp_apply Hq as %b %hb
  iapply HΦ
  ipureintro
  intro h; rw [hb] at h; cases h

/-- The answer at the end of the frames (`P` holds): any, since the call returns (`decUe`: `Decode`'s own
errors' `errIsTerm`, an I/O error's `notUeof`). -/
theorem errUeAns_end (IoE : GoInterface → Prop) (eof ueof err : GoInterface) (P : Prop) (hP : P)
    (hn : err ≠ GoInterface.nil) :
    decEnv (GF := GF) IoE eof ueof ∗ decUe err ⊢ errUeAns err ueof P := by
  iintro ⟨#Henv, #Hue⟩
  ihave %hp := decEnv_ueof_ptr IoE eof ueof $$ Henv
  iunfold decUe at Hue
  icases Hue with (%h | #Ht | #Hn)
  · exact absurd h hn
  · unfold errUeAns
    iunfold errIsTerm at Ht
    ihave #Hq := Ht $$ %ueof %hp
    iintro !> %Φ
    iintro !> - HΦ
    wp_apply Hq as %b -
    iapply HΦ
    ipureintro
    exact fun _ => hP
  · ihave #Hu : globalAddr _root_.Perennial.io.ErrUnexpectedEOF ↦□ ueof $$ []
    · iunfold decEnv at Henv
      icases Henv with ⟨-, -, -, -, -, -, #Hueof, -⟩
      iexact Hueof
    iapply errUeAns_ioe ueof err P
    iframe Hn Hu

/-- The files' streams, the dropped ones and those left in the decoder. -/
theorem streams_take_drop (d : Loc) (IoE : GoInterface → Prop) (eof : GoInterface) (fs : List (DecFile GF))
    (k off : Nat) (c : w32) (live : Bool) :
    ([∗list] F ∈ fs.take k, ∃ q, F.S q) ∗ ownDecoder d IoE eof (fs.drop k) off c live ⊢
      [∗list] F ∈ fs, ∃ q, F.S q := by
  iintro ⟨Ht, Hd⟩
  ihave Hdr := ownDecoder_streams d IoE eof (fs.drop k) off c live $$ Hd
  have e : ([∗list] F ∈ fs.take k ++ fs.drop k, iprop(∃ q, F.S q)) ⊢
      [∗list] F ∈ fs, iprop(∃ q, F.S q) := by
    rw [List.take_append_drop]
  iapply e
  iapply (BigSepL.bigSepL_append (PROP := IProp GF) (Φ := fun _ (F : DecFile GF) => iprop(∃ q, F.S q))).2
  iframe

/-- A file list of length one dropped by `k` and mapped to `[bs]`: `k = 0`. -/
theorem drop_one_map {F : DecFile GF} {k : Nat} {bs : List w8} (h : ([F].drop k).map (·.bs) = [bs]) :
    k = 0 := by
  cases k with
  | zero => rfl
  | succ k => simp at h

/-- A failed `Unmarshal` in one file leaves it. -/
theorem goFail_one {C : WalCodec} {bs : List w8} {off : Nat} {c : w32} {s : WalStop}
    {fs' : List (List w8)} {off' : Nat} {c' : w32} (h : GoFail C [bs] off c s fs' off' c') : fs' = [bs] := by
  cases h with
  | here _ => rfl

/-- **`decPostB` by `Repair`'s switch** (see the file header). -/
theorem repair_decNorm (d rp : Loc) (IoE : GoInterface → Prop) (eof ueof : GoInterface) (F : DecFile GF)
    (rs : List WalRec) (off : Nat) (c : w32) (err : GoInterface) (hRF : RepairFile walCodec F.bs rs)
    (hat : RepairAt walCodec rs off c) (hIoN : ¬ IoE GoInterface.nil) :
    decEnv (GF := GF) IoE eof ueof ∗ decUe err ∗ decPostB walCodec d rp IoE eof ueof [F] off c err ⊢
      (∃ (r : WalRec) (off' : Nat) (c' : w32),
          ⌜err = GoInterface.nil ∧ goDecode walCodec [F.bs] off c = .ok r [F.bs] off' c'⌝ ∗ ownRec rp r ∗
          ownDecoder d IoE eof [F] off' c' true) ∨
      (⌜err = eof⌝ ∗ ∃ q, F.S q) ∨
      (⌜err ≠ GoInterface.nil ∧ err ≠ eof⌝ ∗ (∃ q, F.S q) ∗
        errUeAns err ueof (off = (recFrames walCodec rs).length)) := by
  iintro ⟨#Henv, #Hue, Hp⟩
  ihave %hnn := decEnv_nonnil IoE eof ueof $$ Henv
  ihave #Henv2 := Henv
  iunfold decEnv at Henv2
  icases Henv2 with ⟨-, -, -, -, -, -, #Hueof, #Hok, -⟩
  iunfold isEofOk at Hok
  icases Hok with ⟨%hne, -⟩
  have hF : [F].map (·.bs) = [F.bs] := rfl
  iunfold decPostB at Hp
  icases Hp with (⟨%k, Ht, Hm⟩ | ⟨%hI, #Hnu, -, %k, %off', %c', Ht, Hd⟩ | ⟨%k, %s, %off', %c', ⟨%hgf, %hse⟩, Hd⟩)
  · rw [hF]
    generalize hg : goDecode walCodec [F.bs] off c = g
    cases g with
    | ok r fs' off' c' =>
      icases Hm with ⟨⟨%he, %hfs⟩, Hr, Hd⟩
      have hfs' : fs' = [F.bs] := by
        rw [goDecode_one] at hg
        split at hg <;> simp_all
      subst hfs'
      obtain rfl := drop_one_map hfs
      ileft
      iexists r, off', c'
      iframe Hr
      isplitr
      · ipureintro; exact ⟨he, rfl⟩
      simp only [List.drop_zero]
      iexact Hd
    | stop s fs' off' c' =>
      icases Hm with ⟨⟨%he, -⟩, -, Hd⟩
      ihave Hs := streams_take_drop d IoE eof [F] k off' c' _ $$ [$Ht $Hd]
      ihave Hs := (BigSepL.bigSepL_singleton (PROP := IProp GF) (Φ := fun _ (F : DecFile GF) => iprop(∃ q, F.S q))).1 $$ Hs
      by_cases hs : s = .eof
      · subst hs
        iright; ileft
        iframe Hs
        ipureintro; exact he
      iright; iright
      have hend := repairAt_stop walCodec_ok hRF hat hg
      have hne2 : err ≠ GoInterface.nil ∧ err ≠ eof := by
        cases s <;> simp only [stopErr] at he
        · exact absurd rfl hs
        all_goals first
          | (subst he; exact ⟨hnn.2, fun h => hne.1 h.symm⟩)
          | exact he
          | (rename_i t; cases t <;> simp only [stopErr] at he
             · exact he
             · subst he; exact ⟨hnn.2, fun h => hne.1 h.symm⟩)
      isplitr
      · ipureintro; exact hne2
      iframe Hs
      iapply errUeAns_end IoE eof ueof err _ hend hne2.1
      iframe Henv Hue
  · -- a reader's I/O error: the stream back (the arm keeps the files), the answer `false`
    ihave Hs := streams_take_drop d IoE eof [F] k off' c' _ $$ [$Ht $Hd]
    ihave Hs := (BigSepL.bigSepL_singleton (PROP := IProp GF) (Φ := fun _ (F : DecFile GF) => iprop(∃ q, F.S q))).1 $$ Hs
    iright; iright
    isplitr
    · ipureintro; exact ⟨fun h => hIoN (h ▸ hI), fun h => hne.2.1 (h ▸ hI)⟩
    iframe Hs
    iapply errUeAns_ioe ueof err _
    iframe Hnu Hueof
  · have hfs' : ([F].drop k).map (·.bs) = [F.bs] := goFail_one hgf
    obtain rfl := drop_one_map hfs'
    have hend := repairAt_fail walCodec_ok hRF hat (by rw [hF] at hgf; exact hgf)
    simp only [List.drop_zero]
    ihave Hs := ownDecoder_streams d IoE eof [F] off' c' false $$ Hd
    ihave Hs := (BigSepL.bigSepL_singleton (PROP := IProp GF) (Φ := fun _ (F : DecFile GF) => iprop(∃ q, F.S q))).1 $$ Hs
    obtain ⟨t, rfl⟩ := goFail_badRec hgf
    have hne2 : err ≠ GoInterface.nil ∧ err ≠ eof := by
      cases t <;> simp only [stopErr] at hse
      · exact hse
      · subst hse; exact ⟨hnn.2, fun h => hne.1 h.symm⟩
    iright; iright
    isplitr
    · ipureintro; exact hne2
    iframe Hs
    iapply errUeAns_end IoE eof ueof err _ hend hne2.1
    iframe Henv Hue

end norm

end WalFs
end EtcdGrove
end Perennial

end
