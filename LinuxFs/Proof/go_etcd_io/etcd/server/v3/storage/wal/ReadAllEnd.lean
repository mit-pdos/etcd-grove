/- Lean-first (no Rocq counterpart).

# Where `ReadAll`'s reader ends on the running WAL's files (pure; W3/W5 of `notes/wal-fsext-plan.md`)

`walReadFiles_running` (`ReadAllFiles.lean`) says which records the reader reads; what `ReadAll`
does after its loop (S/wal.go:623-669) needs where it ended: `LastOffset()`, the offset the tail is
`Seek`ed to and zeroed from, is the last segment's write position `lay.wr` (the end of its frames),
and `LastCRC()`, the CRC the encoder chains from, is the chain's CRC after every record of the WAL
(`tailCrc`), also when the reader started in a cut file at CRC 0 (the cut's CRC record re-seeds it:
`chainEnd_crcHead`). `walDecodeFiles_intact_last`: intact files then a last one decode to the
intact files' records, then the last file's decoding at the chain's CRC; `walDecodeFrom_framesEnd`:
a file holding the frames of `rs` and nothing the reader accepts after them ends at their end.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllFiles

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section endpos
variable [GooseExts]

/-- A chain starting with a CRC record does not depend on its starting value. -/
theorem chainEnd_crcHead (C : WalCodec) {c c' : w32} {r : WalRec} (rs : List WalRec)
    (ht : r.typ = crcType) : chainEnd C c (r :: rs) = chainEnd C c' (r :: rs) := by
  simp [chainEnd, crcNext, ht]

/-- A chain starting with a CRC record is a chain from CRC 0 (a fresh decoder's). -/
theorem chainOk_crcHead (C : WalCodec) {c : w32} {r : WalRec} {rs : List WalRec}
    (ht : r.typ = crcType) (h : ChainOk C c (r :: rs)) : ChainOk C 0#32 (r :: rs) := by
  obtain ⟨-, h2⟩ := h
  refine ⟨?_, ?_⟩
  · simp [CrcOk, ht]
  · simpa [crcNext, ht] using h2

/-- **One file holding the frames of `rs`, then nothing the reader accepts**: it ends at their end. -/
theorem walDecodeFrom_framesEnd {C : WalCodec} (hC : C.Ok) {last : List w8} {rs : List WalRec}
    {c : w32} (hfit : RecsFit C rs) (hch : ChainOk C c rs) (hpre : recFrames C rs <+: last)
    (hend : ∀ r len c', decStep C true last (recFrames C rs).length (chainEnd C c rs) ≠ .accept r len c') :
    (walDecodeFrom C true last 0 c).recs = rs ∧
    (walDecodeFrom C true last 0 c).off = (recFrames C rs).length ∧
    (walDecodeFrom C true last 0 c).crc = chainEnd C c rs := by
  obtain ⟨rest, hrest⟩ := hpre
  rw [walDecodeFrom_frames hC (last := true) (bs := last) rs (off := 0) (c := c) (rest := rest) hfit hch
    (by rw [List.drop_zero, hrest])]
  rw [Nat.zero_add, walDecodeFrom_unfold]
  generalize hd : decStep C true last (recFrames C rs).length (chainEnd C c rs) = st
  cases st with
  | stop s => simp
  | accept r len c' => exact absurd hd (hend r len c')

/-- **Intact files, then a last file** (see the file header). -/
theorem walDecodeFiles_intact_last {C : WalCodec} (hC : C.Ok) (last : List w8) :
    ∀ (rss : List (List WalRec)) (c : w32), RecsFit C rss.flatten → ChainOk C c rss.flatten →
    walDecodeFiles C (rss.map (recFrames C) ++ [last]) c =
      { walDecodeFrom C true last 0 (chainEnd C c rss.flatten) with
        recs := rss.flatten ++ (walDecodeFrom C true last 0 (chainEnd C c rss.flatten)).recs }
  | [], c, _, _ => by simp [walDecodeFiles, chainEnd]
  | rs :: rss, c, hfit, hch => by
    have hfit1 : RecsFit C rs := fun r hr => hfit r (by simp [hr])
    have hfit2 : RecsFit C rss.flatten := fun r hr => hfit r (by simp only [List.flatten_cons]; simp [hr])
    rw [List.flatten_cons, chainOk_append] at hch
    have ih := walDecodeFiles_intact_last hC last rss (chainEnd C c rs) hfit2 hch.2
    have h1 := walDecodeFrom_segFile hC false hfit1 hch.1 (z := 0) (Or.inl rfl)
    have hseg : segFile C rs 0 = recFrames C rs := by simp [segFile]
    rw [hseg] at h1
    obtain ⟨g, fs, hgf⟩ : ∃ g fs, rss.map (recFrames C) ++ [last] = g :: fs := by
      cases h : rss.map (recFrames C) ++ [last] with
      | nil => simp at h
      | cons g fs => exact ⟨g, fs, rfl⟩
    rw [List.map_cons, List.cons_append, hgf]
    rw [hgf] at ih
    simp only [walDecodeFiles, h1, ↓reduceIte, ih, List.flatten_cons, chainEnd_append, List.append_assoc]

/-- The files of a cut (`segsDs … false …`) start with the cut's header. -/
theorem segsDs_false_cut (M : WalMarshal) (md : List w8) :
    ∀ (P : WalHist) (Ss : List WalHist) (q : Nat) (D : List (w64 × List w8)),
    (segsDs M md false P Ss)[q]? = some D → ∃ hs rest, D = cutHdrDs M md hs ++ rest
  | _, [], _, _, h => by simp [segsDs] at h
  | P, S :: Ss, 0, D, h => by
    simp only [segsDs, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨walLastHS P, S.flatMap (opDs M), by simp [segHdrDs]⟩
  | P, S :: Ss, q + 1, D, h => by
    simp only [segsDs, List.getElem?_cons_succ] at h
    exact segsDs_false_cut M md (P ++ S) Ss q D h

/-- Every file after the first starts with a cut's header. -/
theorem segsDs_cut (M : WalMarshal) (md : List w8) (first : Bool) (P : WalHist) (Ss : List WalHist)
    (p : Nat) (hp : 1 ≤ p) (D : List (w64 × List w8)) (h : (segsDs M md first P Ss)[p]? = some D) :
    ∃ hs rest, D = cutHdrDs M md hs ++ rest := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  cases Ss with
  | nil => simp [segsDs] at h
  | cons S Ss =>
    simp only [segsDs, List.getElem?_cons_succ] at h
    exact segsDs_false_cut M md (P ++ S) Ss q D h

theorem chainSegs_getElem? (C : WalCodec) :
    ∀ (c : w32) (Ds : List (List (w64 × List w8))) (p : Nat) (rs : List WalRec),
    (chainSegs C c Ds)[p]? = some rs → ∃ c' D, Ds[p]? = some D ∧ rs = chainRecs C c' D
  | _, [], _, _, h => by simp [chainSegs] at h
  | c, D :: Ds, 0, rs, h => by
    simp only [chainSegs, List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨c, D, rfl, h.symm⟩
  | c, D :: Ds, p + 1, rs, h => by
    simp only [chainSegs, List.getElem?_cons_succ] at h
    obtain ⟨c', D', h1, h2⟩ := chainSegs_getElem? C _ Ds p rs h
    exact ⟨c', D', by simpa using h1, h2⟩

theorem chainRecs_cutHead (C : WalCodec) (M : WalMarshal) (md : List w8) (c : w32) (hs : HardStateM)
    (rest : List (w64 × List w8)) :
    ∃ r rs, chainRecs C c (cutHdrDs M md hs ++ rest) = r :: rs ∧ r.typ = crcType := by
  simp only [cutHdrDs, List.cons_append, chainRecs]
  exact ⟨_, _, rfl, rfl⟩

/-- **Where the reader ends on the running WAL's files from segment `p` on** (`walDecodeFiles_running`'s
hypotheses): at the end of the last segment's frames, at the chain's CRC after every record. -/
theorem walDecodeFiles_running_end {C : WalCodec} (hC : C.Ok) (M : WalMarshal) (md : List w8)
    (A : List WalHist) (Sl : WalHist) (p : Nat) (hp : p ≤ A.length) (last : List w8)
    (hfit : RecsFit C (recsOfSegs C M md (A ++ [Sl])))
    (hpre : recFrames C (lastRecs C M md A Sl) <+: last)
    (hend : ∀ r len c', decStep C true last (recFrames C (lastRecs C M md A Sl)).length
      (chainEnd C 0#32 (recsOfSegs C M md (A ++ [Sl]))) ≠ .accept r len c') :
    (walDecodeFiles C (((chainSegs C 0#32 (segsDs M md true [] A)).drop p).map (recFrames C) ++ [last])
        0#32).off = (recFrames C (lastRecs C M md A Sl)).length ∧
    (walDecodeFiles C (((chainSegs C 0#32 (segsDs M md true [] A)).drop p).map (recFrames C) ++ [last])
        0#32).crc = chainEnd C 0#32 (recsOfSegs C M md (A ++ [Sl])) := by
  generalize hL : chainSegs C 0#32 (segsDs M md true [] A) = L
  have hLl : L.length = A.length := by rw [← hL, length_chainSegs, length_segsDs]
  have hfull : recsOfSegs C M md (A ++ [Sl]) = L.flatten ++ lastRecs C M md A Sl := by
    rw [recsOfSegs_snocR, ← hL, flatten_chainSegs]; rfl
  have hchF : ChainOk C 0#32 (recsOfSegs C M md (A ++ [Sl])) :=
    chainOk_chainRecs hC 0#32 _ (segsDs_crcOk M md true [] (A ++ [Sl]))
  have hsplitF : recsOfSegs C M md (A ++ [Sl]) =
      (L.take p).flatten ++ ((L.drop p).flatten ++ lastRecs C M md A Sl) := by
    rw [hfull, ← List.append_assoc, ← List.flatten_append, List.take_append_drop]
  generalize hX : (L.drop p).flatten ++ lastRecs C M md A Sl = X at hsplitF
  -- `X` is a chain from CRC 0, ending where the whole chain does.
  have hX0 : ChainOk C 0#32 X ∧ chainEnd C 0#32 X = chainEnd C 0#32 (recsOfSegs C M md (A ++ [Sl])) := by
    rcases Nat.eq_zero_or_pos p with h0 | hpos
    · subst h0
      simp only [List.take_zero, List.flatten_nil, List.nil_append] at hsplitF
      rw [← hsplitF]; exact ⟨hchF, rfl⟩
    · -- the first record of `X` is a cut's CRC record
      obtain ⟨r, rs, hXr, hrt⟩ : ∃ r rs, X = r :: rs ∧ r.typ = crcType := by
        rw [← hX]
        rcases hd : L.drop p with _ | ⟨rs0, Ls⟩
        · have hpA : p = A.length := by
            have := List.drop_eq_nil_iff.1 hd; omega
          have hAne : A ≠ [] := by intro h; rw [h] at hpA; simp at hpA; omega
          simp only [List.flatten_nil, List.nil_append, lastRecs, segHdrDs, if_neg hAne,
            Bool.false_eq_true, ↓reduceIte, List.append_assoc]
          exact chainRecs_cutHead C M md _ _ _
        · have hg : L[p]? = some rs0 := by
            rw [← List.head?_drop, hd]; rfl
          rw [← hL] at hg
          obtain ⟨c', D, hD, hrs⟩ := chainSegs_getElem? C _ _ p rs0 hg
          obtain ⟨hs, rest, rfl⟩ := segsDs_cut M md true [] A p hpos D hD
          obtain ⟨r, rs, h1, h2⟩ := chainRecs_cutHead C M md c' hs rest
          rw [hrs, h1]
          exact ⟨r, rs ++ (Ls.flatten ++ lastRecs C M md A Sl), by simp, h2⟩
      rw [hsplitF, chainOk_append] at hchF
      rw [hXr] at hchF ⊢
      refine ⟨chainOk_crcHead C hrt hchF.2, ?_⟩
      rw [hsplitF, chainEnd_append, hXr]
      exact chainEnd_crcHead C rs hrt
  obtain ⟨hchX, hendX⟩ := hX0
  have hfitX : RecsFit C X := fun r hr => hfit r (by rw [hsplitF]; exact List.mem_append_right _ hr)
  rw [← hX] at hchX hfitX hendX
  rw [chainOk_append] at hchX
  have hfitD : RecsFit C (L.drop p).flatten := fun r hr => hfitX r (List.mem_append_left _ hr)
  have hfitl : RecsFit C (lastRecs C M md A Sl) := fun r hr => hfitX r (List.mem_append_right _ hr)
  rw [walDecodeFiles_intact_last hC last _ 0#32 hfitD hchX.1]
  rw [chainEnd_append] at hendX
  have hE := walDecodeFrom_framesEnd hC hfitl hchX.2 hpre (by rw [hendX]; exact hend)
  exact ⟨hE.2.1, by simp only; rw [hE.2.2, hendX]⟩

/-- **Where `ReadAll`'s reader ends on the named segments from the `kk`-th on**
(`walReadFiles_running`'s premises): at the last segment's write position, at the chain's CRC after
every record of the WAL. -/
theorem walReadFiles_running_end {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat)
    (hkk : kk < lay.segs.length) :
    (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).off = lay.wr ∧
    (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).crc =
      chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)) := by
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
  rw [hfiles, hwr, hstreamL, hsplit]
  apply walDecodeFiles_running_end hC Mr d.metadata A Sl (lay.first + kk) (by omega) (segImg gL)
  · rw [← hsplit, ← hSs]; exact hab.fit
  · rw [himg, ← hstreamL]; exact List.prefix_append _ _
  · intro r len c'
    rw [← hstreamL, ← hsplit, ← hSs]
    obtain ⟨-, -, h3, h4, -, h6, h7, h8⟩ := hTL
    generalize hS : segStream C Mr d lay.cuts lay.cuts.length = S at *
    by_cases hz : lay.z0 < S.length
    · apply decStep_zeros_any C true (z := lay.old.length - S.length)
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
      rw [hold, ← hz0]
      exact hab.tailStop (by rw [hS]; exact hz0) r len c'

/-- **The write position is inside the last file** (`walReadFiles_running`'s premises): `lay.wr` is at
most the length of the last of the files read. -/
theorem walReadFiles_wr_le {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat) (gs : List SegG)
    (hgs : lay.segs.drop kk = gs) (g : SegG) (hg : gs.getLast? = some g) :
    lay.wr ≤ g.bs.length := by
  have hg' : lay.segs.getLast? = some g := by
    have hne : gs ≠ [] := by intro h; rw [h] at hg; simp at hg
    rw [← hgs] at hg hne
    rw [List.getLast?_drop, if_neg (by intro h; exact hne (List.drop_eq_nil_of_le h))] at hg
    exact hg
  have himg := tailLast_img (hab.lastEx hex g hg') hwr
  have := congrArg List.length himg
  simp only [segImg, List.length_map, List.length_append] at this
  omega

end endpos

end WalFs
end EtcdGrove
end Perennial
