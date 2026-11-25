/- Lean-first (no Rocq counterpart).

# The running WAL's files are `FilesOk` (pure; gap 4 of W8, `notes/wal-fsext-plan.md`)

`walDecodeFiles_running`'s premises (`walDecodeFiles_running_end`'s proof, kept as a statement): the files
of the segments from the `p`-th on are full files of the chain's segments then the last, one chain from
CRC 0 (a cut file starts with a CRC record), with nothing accepted at the end (`filesOk_running`); and on a
WAL with its tail idle, the named segments from the `kk`-th on (`walFilesOk`, as
`walReadFiles_running_end`). `filesAt_start` then starts a fresh decoder on them.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.FilesAt
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllEnd

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

set_option autoImplicit false

section run
variable [GooseExts]

/-- Every file after the first starts with a cut's header (`ReadAllEnd`'s private `segsDs_cut`). -/
theorem segsDs_cut' (M : WalMarshal) (md : List w8) (first : Bool) (P : WalHist) (Ss : List WalHist)
    (p : Nat) (hp : 1 ≤ p) (D : List (w64 × List w8)) (h : (segsDs M md first P Ss)[p]? = some D) :
    ∃ hs rest, D = cutHdrDs M md hs ++ rest := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  cases Ss with
  | nil => simp [segsDs] at h
  | cons S Ss =>
    simp only [segsDs, List.getElem?_cons_succ] at h
    exact segsDs_false_cut M md (P ++ S) Ss q D h

/-- **The files from segment `p` on are `FilesOk`** (`walDecodeFiles_running`'s premises). -/
theorem filesOk_running {C : WalCodec} (hC : C.Ok) (M : WalMarshal) (md : List w8)
    (A : List WalHist) (Sl : WalHist) (p : Nat) (last : List w8) (Y : List WalRec)
    (hfit : RecsFit C (recsOfSegs C M md (A ++ [Sl]))) (hfitY : RecsFit C Y)
    (hchY : ChainOk C (chainEnd C 0#32 (recsOfSegs C M md (A ++ [Sl]))) Y)
    (hpre : recFrames C (lastRecs C M md A Sl ++ Y) <+: last)
    (hend : ∀ r len c', decStep C true last (recFrames C (lastRecs C M md A Sl ++ Y)).length
      (chainEnd C (chainEnd C 0#32 (recsOfSegs C M md (A ++ [Sl]))) Y) ≠ .accept r len c') :
    FilesOk C 0#32 ((chainSegs C 0#32 (segsDs M md true [] A)).drop p) (lastRecs C M md A Sl ++ Y)
      last := by
  generalize hL : chainSegs C 0#32 (segsDs M md true [] A) = L
  have hfull : recsOfSegs C M md (A ++ [Sl]) = L.flatten ++ lastRecs C M md A Sl := by
    rw [recsOfSegs_snocR, ← hL, flatten_chainSegs]; rfl
  have hchF : ChainOk C 0#32 (recsOfSegs C M md (A ++ [Sl])) :=
    chainOk_chainRecs hC 0#32 _ (segsDs_crcOk M md true [] (A ++ [Sl]))
  have hsplitF : recsOfSegs C M md (A ++ [Sl]) =
      (L.take p).flatten ++ ((L.drop p).flatten ++ lastRecs C M md A Sl) := by
    rw [hfull, ← List.append_assoc, ← List.flatten_append, List.take_append_drop]
  generalize hX : (L.drop p).flatten ++ lastRecs C M md A Sl = X at hsplitF
  have hX0 : ChainOk C 0#32 X ∧ chainEnd C 0#32 X = chainEnd C 0#32 (recsOfSegs C M md (A ++ [Sl])) := by
    rcases Nat.eq_zero_or_pos p with h0 | hpos
    · subst h0
      simp only [List.take_zero, List.flatten_nil, List.nil_append] at hsplitF
      rw [← hsplitF]; exact ⟨hchF, rfl⟩
    · obtain ⟨r, rs, hXr, hrt⟩ : ∃ r rs, X = r :: rs ∧ r.typ = crcType := by
        rw [← hX]
        rcases hd : L.drop p with _ | ⟨rs0, Ls⟩
        · simp only [List.flatten_nil, List.nil_append]
          exact lastRecs_head C M md A Sl
        · have hg : L[p]? = some rs0 := by
            rw [← List.head?_drop, hd]; rfl
          rw [← hL] at hg
          obtain ⟨c', D, hD, hrs⟩ := chainSegs_getElem? C _ _ p rs0 hg
          obtain ⟨hs, rest, rfl⟩ := segsDs_cut' M md true [] A p hpos D hD
          obtain ⟨r, rs, h1, h2⟩ := chainRecs_cutHead C M md c' hs rest
          rw [hrs, h1]
          exact ⟨r, rs ++ (Ls.flatten ++ lastRecs C M md A Sl), by simp, h2⟩
      rw [hsplitF, chainOk_append] at hchF
      rw [hXr] at hchF ⊢
      obtain ⟨h1, h2⟩ := chainOk_crcHead hchF.2 hrt
      refine ⟨h1, ?_⟩
      rw [hsplitF, chainEnd_append, hXr, h2]
  obtain ⟨hchX, hendX⟩ := hX0
  have hfitX : RecsFit C X := fun r hr => hfit r (by rw [hsplitF]; exact List.mem_append_right _ hr)
  rw [← hX] at hchX hfitX hendX
  refine ⟨?_, ?_, hpre, ?_⟩
  · rw [← List.append_assoc]
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hfitX r hr
    · exact hfitY r hr
  · rw [← List.append_assoc, chainOk_append]
    exact ⟨hchX, by rw [hendX]; exact hchY⟩
  · rw [← List.append_assoc, chainEnd_append, hendX]
    exact hend

/-- **A fresh decoder on the named segments from the `kk`-th on is at a frame boundary**
(`walReadFiles_running_end`'s proof, the WAL's tail idle). -/
theorem walFilesAt {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat)
    (hkk : kk < lay.segs.length) :
    FilesAt C ((lay.segs.drop kk).map segImg) 0 0#32 := by
  have hne : lay.segs ≠ [] := hab.nonempty
  obtain ⟨-, -, hfl⟩ := hab.cuts
  generalize hSs : segsOf (histM d) lay.cuts = Ss
  have hSsl : Ss.length = lay.cuts.length + 1 := by rw [← hSs]; simp [segsOf]
  have hSne : Ss ≠ [] := by intro h; rw [h] at hSsl; simp at hSsl
  have hsplit : Ss = Ss.dropLast ++ [Ss.getLast hSne] := (List.dropLast_concat_getLast _).symm
  generalize hA : Ss.dropLast = A at hsplit
  generalize hSl : Ss.getLast hSne = Sl at hsplit
  have hAl : A.length = lay.cuts.length := by rw [← hA, List.length_dropLast, hSsl]; simp
  have hrecs : segRecs C Mr d lay.cuts =
      chainSegs C 0#32 (segsDs Mr d.metadata true [] A) ++ [lastRecs C Mr d.metadata A Sl] := by
    unfold segRecs; rw [hSs, hsplit, chainSegs_snocR]
  have hlenA : (chainSegs C 0#32 (segsDs Mr d.metadata true [] A)).length = A.length := by
    rw [length_chainSegs, length_segsDs]
  have hstreamL : segStream C Mr d lay.cuts lay.cuts.length = recFrames C (lastRecs C Mr d.metadata A Sl) := by
    unfold segStream; rw [hrecs, ← hAl, ← hlenA, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp
  have hstream : ∀ i (hi : i < A.length), segStream C Mr d lay.cuts i =
      recFrames C ((chainSegs C 0#32 (segsDs Mr d.metadata true [] A))[i]'(by omega)) := by
    intro i hi
    unfold segStream
    rw [hrecs, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hsegs : lay.segs = lay.segs.dropLast ++ [lay.segs.getLast hne] := (List.dropLast_concat_getLast _).symm
  generalize hgL : lay.segs.getLast hne = gL at hsegs
  have hgL' : lay.segs.getLast? = some gL := by rw [List.getLast?_eq_getLast hne, hgL]
  have hTL := hab.lastEx hex gL hgL'
  have himg := tailLast_img hTL hwr
  have hfiles : (lay.segs.drop kk).map segImg =
      ((chainSegs C 0#32 (segsDs Mr d.metadata true [] A)).drop (lay.first + kk)).map (recFrames C) ++
        [segImg gL] := by
    have hdl : lay.segs.dropLast.length + 1 = lay.segs.length := by
      rw [List.length_dropLast]; have := List.length_pos_iff.2 hne; omega
    conv => lhs; rw [hsegs]
    rw [List.drop_append_of_le_length (by omega), List.map_append, List.map_singleton]
    congr 1
    apply List.ext_getElem
    · simp only [List.length_map, List.length_drop, hlenA, hAl]; omega
    · intro j h1 h2
      simp only [List.length_map, List.length_drop] at h1
      simp only [List.getElem_map, List.getElem_drop]
      have hj : kk + j + 1 < lay.segs.length := by omega
      have hg : lay.segs[kk + j]? = some (lay.segs.dropLast[kk + j]'(by omega)) := by
        rw [List.getElem_dropLast]; exact List.getElem?_eq_getElem _
      have hint := hab.intact (kk + j) _ hj hg
      rw [segImg, hint, List.map_map]
      have e : (Prod.fst ∘ durB) = (id : w8 → w8) := rfl
      rw [e, List.map_id, hstream (lay.first + (kk + j)) (by omega)]
      congr 2; omega
  rw [hfiles]
  have hfit : RecsFit C (recsOfSegs C Mr d.metadata (A ++ [Sl])) := by
    rw [← hsplit, ← hSs]; exact hab.fit
  have hpendS := hab.tailStop
  rw [hSs, hsplit] at hpendS
  obtain ⟨-, -, h3, h4, -, h6, h7, h8⟩ := hTL
  generalize hS : segStream C Mr d lay.cuts lay.cuts.length = S at *
  generalize hc : chainEnd C 0#32 (recsOfSegs C Mr d.metadata (A ++ [Sl])) = c at *
  have hchE : ∀ es : List EntryM, ChainOk C c (chainRecs C c (pendDs Mr es)) := fun es =>
    chainOk_chainRecs hC _ _ (by intro q hq h; simp [pendDs] at hq; obtain ⟨e, -, rfl⟩ := hq; cases h)
  obtain ⟨es, -, hfE, hpX, hendX⟩ : ∃ es : List EntryM, (es ≠ [] → lay.z0 = S.length) ∧
      RecsFit C (chainRecs C c (pendDs Mr es)) ∧
      recFrames C (lastRecs C Mr d.metadata A Sl ++ chainRecs C c (pendDs Mr es)) <+: segImg gL ∧
      ∀ r len c', decStep C true (segImg gL)
        (recFrames C (lastRecs C Mr d.metadata A Sl ++ chainRecs C c (pendDs Mr es))).length
        (chainEnd C c (chainRecs C c (pendDs Mr es))) ≠ .accept r len c' := by
    by_cases hz : lay.z0 < S.length
    · refine ⟨[], fun h => absurd rfl h, fun _ h => by simp [pendDs, chainRecs] at h, ?_, ?_⟩
      · simp only [pendDs, List.map_nil, chainRecs, List.append_nil]
        rw [himg, ← hstreamL]; exact List.prefix_append _ _
      · intro r len c'
        simp only [pendDs, List.map_nil, chainRecs, List.append_nil]
        rw [← hstreamL]
        apply decStep_zeros_any C true (z := lay.old.length - S.length)
        rw [himg, List.drop_left]
        apply List.ext_getElem
        · simp
        · intro b hb1 hb2
          simp only [List.getElem_drop, List.getElem_replicate]
          have := h8 hz (S.length + b) (by omega) (by simp at hb1; omega)
          rwa [getD_of_lt _ _ _ (by simp at hb1; omega)] at this
    · have hz0 : lay.z0 = S.length := by omega
      have hold : segImg gL = lay.old := by
        rw [himg]
        have : S = lay.old.take S.length := by rw [← hz0, ← h7, hz0, List.take_length]
        conv => lhs; arg 1; rw [this]
        exact List.take_append_drop _ _
      obtain ⟨es, hfE, hpE, hrE⟩ := hpendS hz0
      have hSo : S = lay.old.take lay.z0 := by rw [hz0, ← hold, himg, List.take_left' rfl]
      refine ⟨es, fun _ => hz0, hfE, ?_, ?_⟩
      · rw [hold, recFrames_append, ← hstreamL]
        obtain ⟨t, ht⟩ := hpE
        refine ⟨t, ?_⟩
        rw [List.append_assoc, ht, hSo, List.take_append_drop]
      · intro r len c'
        rw [hold, recFrames_append, List.length_append, ← hstreamL, chainEnd_chainRecs, ← hz0]
        exact hrE r len c'
  subst hc
  apply filesAt_start
  exact filesOk_running hC Mr d.metadata A Sl (lay.first + kk) (segImg gL) _ hfit hfE (hchE es) hpX hendX

end run

end WalFs
end EtcdGrove
end Perennial

end
