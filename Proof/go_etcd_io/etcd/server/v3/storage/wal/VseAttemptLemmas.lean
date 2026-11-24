/- Lean-first (no Rocq counterpart).

# `validSnapshotEntries`' attempt: the files back (W8 of `notes/wal-fsext-plan.md`)

The attempt's deferred `closer()` (`openWALFiles`' `wal.walCloser`) needs every opened file back, closable
(`wal.walClosable`), and its post the program's halves of every segment: both are in the decoder's files'
streams (`walFileS`), which the decode loop keeps (the streams of the files it went past, `Hleft`, and the
decoder's).

* `vse_streams`: every file's stream, from those went past and the decoder's.
* `vse_exit_streams`: at the loop's exit (`Decode` returned an error), every file's stream, and either the
  reader read exactly the records handled (a stop, or a failed `Unmarshal`: `vsLoop_stop`, `filesAt_fail`,
  `goFail_take`) or the error is an I/O error with its `notUeof`.
* `walTie_closable`, `vse_close`: the segments' halves and the closer's precondition, from the streams.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VsePure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VseAttemptPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecStreams
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllTail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseOpeningFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- **Every file's stream**, from those of the files went past and the decoder's. -/
theorem vse_streams (d : Loc) (IoE : GoInterface → Prop) (eof : GoInterface) (fs fsD : List (DecFile GF))
    (kD k off : Nat) (c : w32) (live : Bool) (hkD : fsD = fs.drop kD) :
    ([∗list] F ∈ fs.take kD, ∃ q, F.S q) ∗ ([∗list] F ∈ fsD.take k, ∃ q, F.S q) ∗
      ownDecoder d IoE eof (fsD.drop k) off c live ⊢ [∗list] F ∈ fs, ∃ q, F.S q := by
  iintro ⟨Hl, Hk, Hd⟩
  ihave Hl := leftS_merge fs fsD kD k hkD $$ [Hl Hk]
  · iframe
  ihave Hd := ownDecoder_streams d IoE eof (fsD.drop k) off c live $$ Hd
  subst hkD
  rw [List.drop_drop]
  rw [← List.take_append_drop (kD + k) fs]
  iapply (BigSepL.bigSepL_append (PROP := IProp GF) (Φ := fun _ (F : DecFile GF) => iprop(∃ q, F.S q))).2
  rw [List.take_append_drop]
  iframe

/-- **At the loop's exit** (see the file header). -/
theorem vse_exit_streams {C : WalCodec} (hC : C.Ok) (d rp : Loc) (IoE : GoInterface → Prop)
    (eof ueof : GoInterface) (fs fsD : List (DecFile GF)) (kD off : Nat) (c : w32) (e : GoInterface)
    (R0 : DecOut) (acc : List WalRec) (hL : VsLoop C R0 acc (fsD.map (·.bs)) off c)
    (hFA : FilesAt C (fsD.map (·.bs)) off c) (hLO : LaterOk C (fsD.map (·.bs))) (hkD : fsD = fs.drop kD)
    (he : e ≠ GoInterface.nil) :
    decPostB C d rp IoE eof ueof fsD off c e ∗ ([∗list] F ∈ fs.take kD, ∃ q, F.S q) ⊢
      ([∗list] F ∈ fs, ∃ q, F.S q) ∗ (⌜R0.recs = acc⌝ ∨ (⌜IoE e⌝ ∗ notUeof e)) := by
  iintro ⟨Hpb, Hleft⟩
  unfold decPostB
  icases Hpb with (⟨%k, Hk, Hm⟩ | ⟨%hio, #Hn, -, %k, %off', %c', Hk, Hdec⟩ |
    ⟨%k, %s, %off', %c', ⟨%hgf, -⟩, -, Hdec⟩)
  · generalize hgd : goDecode C (fsD.map (·.bs)) off c = gd
    rcases gd with ⟨r, fs', off', c'⟩ | ⟨sx, fs', off', c'⟩
    · icases Hm with ⟨%hst, -, -⟩
      exact absurd hst.1 he
    · icases Hm with ⟨%hst, -, Hdec⟩
      isplitl [Hleft Hk Hdec]
      · iapply vse_streams d IoE eof fs fsD kD k off' c' _ hkD
        iframe
      ileft
      ipureintro
      exact vsLoop_stop hL hgd
  · isplitl [Hleft Hk Hdec]
    · iapply vse_streams d IoE eof fs fsD kD k off' c' false hkD
      iframe
    iright
    iframe Hn
    ipureintro; exact hio
  · have htk := goFail_take hC hLO hgf
    ihave Hk : ([∗list] F ∈ fsD.take k, ∃ q, F.S q) $$ []
    · rw [htk]; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
    isplitl [Hleft Hk Hdec]
    · iapply vse_streams d IoE eof fs fsD kD k off' c' false hkD
      iframe
    ileft
    ipureintro
    have h0 := filesAt_fail hC hFA hgf
    rw [hL.recs, h0, List.append_nil]

/-- **The closer's precondition from the tie's files** (read mode). -/
theorem walTie_closable (dir : GoString) (write : Bool) :
    ∀ (gs : List SegG) (fs : List (DecFile GF)) (fls lfs : List Loc), fs.length = gs.length →
    (∀ g ∈ gs, os.closeErrMax (child dir g.name) ≤ wal.closeMsgMax) →
    ([∗list] k ↦ g ∈ gs, walTieFile (GF := GF) dir write fls k g) ∗
      ([∗list] k ↦ F ∈ fs, walFrFile F.fr (fls.getD k null)) ⊢
      [∗list] m ↦ fr ∈ fs.map (·.fr), wal.walClosable (GF := GF) false fr (lfs.getD m null)
  | [], [], _, _, _, _ => by
    iintro -
    simp only [List.map_nil]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | g :: gs, F :: fs, fls, lfs, hl, hgs => by
    have ih := walTie_closable dir write gs fs fls.tail lfs.tail (by simpa using hl)
      (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    have e1 : ∀ (l : List Loc) (k : Nat), l.getD (k + 1) null = l.tail.getD k null := by
      intro l k; cases l <;> simp
    have e2 : ∀ (k : Nat) (g' : SegG), walTieFile (GF := GF) dir write fls (k + 1) g' =
        walTieFile dir write fls.tail k g' := by
      intro k g'; simp only [walTieFile, e1]
    iintro ⟨Ht, Hf⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Ht with ⟨Ht0, Ht⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hf with ⟨Hf0, Hf⟩
    simp only [e1, e2, List.map_cons]
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitl [Ht0 Hf0]
    · iunfold walTieFile at Ht0
      iunfold walFrFile at Hf0
      icases Ht0 with ⟨%fd, %lo, %lk, Hfl, Hfd, Hlks⟩
      icases Hf0 with ⟨%rl, %hrl, #Hrl⟩
      unfold wal.walClosable
      iexists fls.getD 0 null, rl, fd, _, _
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hfl Hfd Hlks Hrl
      ipureintro; exact ⟨hrl, trivial, hgs g (List.mem_cons_self ..)⟩
    · simp only [e1]
      iapply ih
      iframe
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

/-- **The segments' halves and the closer's precondition, from every file's stream** (read mode). -/
theorem vse_close (dir : GoString) (gs : List SegG) (fs : List (DecFile GF)) (fls lfs : List Loc)
    (htie : WalDecTie dir false gs fs fls)
    (hgs : ∀ g ∈ gs, os.closeErrMax (child dir g.name) ≤ wal.closeMsgMax) :
    ([∗list] k ↦ F ∈ fs, walFrFile F.fr (fls.getD k null)) ∗ ([∗list] F ∈ fs, ∃ q, F.S q) ⊢
      ([∗list] g ∈ gs, segRes (L := hG.goose_localGS) g) ∗
        [∗list] m ↦ fr ∈ fs.map (·.fr), wal.walClosable false fr (lfs.getD m null) := by
  obtain ⟨h1, h2, h3⟩ := htie
  iintro ⟨Hf, Hs⟩
  icases walTie_files dir false gs fs fls h1 h2
    (fun k F g hF hg => (h3 k F g hF hg).2) $$ Hs with ⟨HS, Ht⟩
  iframe HS
  iapply walTie_closable dir false gs fs fls lfs h1 hgs
  iframe

/-- **The first `n` elements, as the full slice `s[0:n:n]`.** -/
theorem ownSlice_fullSlice_take {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice)
    (dq : DFrac) (vs : List V) (n : w64) (hn : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z s.len) :
    (s ↦*{dq} vs : IProp GF) ⊢ slice.fullSlice s V (W64 0) n n ↦*{dq} vs.take (sint.nat n) := by
  iintro Hs
  icases (ownSlice_slice (W64 0) n s dq vs ⟨by decide, hn.1, hn.2⟩).1 $$ Hs with ⟨-, Hm, -⟩
  have hsub : subslice (sint.nat (W64 0)) (sint.nat n) vs = vs.take (sint.nat n) := by
    have h0 : sint.nat (W64 0) = 0 := rfl
    unfold subslice
    rw [h0, List.drop_zero]
  rw [hsub]
  rw [ownSlice_unseal]
  unfold ownSliceDef
  icases Hm with (%H | ⟨H, %_⟩)
  · ileft
    ipureintro
    refine ⟨?_, H.2⟩
    have h := H.1
    simp only [slice.slice, slice.fullSlice, slice.nil, GoSlice.mk.injEq] at h ⊢
    obtain ⟨h1, h2, -⟩ := h
    exact ⟨h1, h2, h2⟩
  · iright
    have hp : (slice.fullSlice s V (W64 0) n n).ptr = (slice.slice s V (W64 0) n).ptr := rfl
    have hl : (slice.fullSlice s V (W64 0) n n).len = (slice.slice s V (W64 0) n).len := rfl
    rw [hp, hl]
    isplitl [H]
    · iexact H
    ipureintro
    simp only [slice.fullSlice]
    exact Int.le_refl _

end lemmas

end WalFs
end EtcdGrove
end Perennial

end
