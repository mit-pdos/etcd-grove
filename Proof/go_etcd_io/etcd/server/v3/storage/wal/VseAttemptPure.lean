/- Lean-first (no Rocq counterpart).

# `validSnapshotEntries`' attempt: a failed `Unmarshal` drops no file (pure; W8 of `notes/wal-fsext-plan.md`)

`decoder.Decode`'s `GoFail` arm gives back the decoder's files from the one it failed in (`fs.drop k`),
not the streams of the files it dropped first (`GoFail.next`: the end of a file, then a failure at the
start of the next). On a WAL's files no failure is at a file's start: every file after the first starts
with a frame the encoder wrote (`LaterOk`; a cut's header, `walLaterOk`), at which `proto.Unmarshal`
succeeds and the decoder does not see an end (`goFail_here`), so the failure is in the current file and
no file is dropped (`goFail_take`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.FilesAtRun
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VsePure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

set_option autoImplicit false

section later
variable [GooseExts]

/-- **Every file after the first starts with a frame the encoder wrote** (see the file header). -/
def LaterOk (C : WalCodec) (fs : List (List w8)) : Prop :=
  ∀ g ∈ fs.tail, ∃ (y : WalRec) (rest : List w8), g = frame (C.encRec y) ++ rest ∧
    (C.encRec y).length < 2 ^ 56

theorem laterOk_drop {C : WalCodec} {fs : List (List w8)} (h : LaterOk C fs) (k : Nat) :
    LaterOk C (fs.drop k) := by
  intro g hg
  apply h g
  rw [List.tail_drop] at hg
  rw [← List.drop_one]
  rw [show k + 1 = 1 + k by omega, ← List.drop_drop] at hg
  exact List.mem_of_mem_drop hg

/-- At a frame the encoder wrote the decoder sees no end. -/
theorem decRecStep_frame_ne_eof' {C : WalCodec} (hC : C.Ok) (last : Bool) {bs : List w8} {off : Nat}
    {y : WalRec} {rest : List w8} (hfit : (C.encRec y).length < 2 ^ 56)
    (hbs : bs.drop off = frame (C.encRec y) ++ rest) (c : w32) :
    decRecStep C last bs off c ≠ .eof := by
  obtain ⟨data, hd, -⟩ := decFrame_ofFrame hC hfit hbs
  obtain ⟨pad, hp⟩ := decRecStep_decFrame (C := C) (last := last) (c := c) hd
  rw [hp]
  intro h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · cases h

/-- **A failed `Unmarshal` is in the current file** (see the file header). -/
theorem goFail_here {C : WalCodec} (hC : C.Ok) {fs : List (List w8)} {off : Nat} {c : w32}
    {s : WalStop} {fs' : List (List w8)} {off' : Nat} {c' : w32} (hL : LaterOk C fs)
    (h : GoFail C fs off c s fs' off' c') : fs' = fs := by
  cases h with
  | here _ => rfl
  | @next f g gs _ _ _ _ _ _ he hg =>
    exfalso
    obtain ⟨y, rest, hgy, hfit⟩ := hL g (by simp)
    have hbs : g.drop 0 = frame (C.encRec y) ++ rest := by rw [List.drop_zero, hgy]
    cases hg with
    | here hf => exact recFail_frame hC _ hfit hbs hf
    | next he' _ => exact decRecStep_frame_ne_eof' hC false hfit hbs c he'

/-- **No file is dropped at a failed `Unmarshal`** (see the file header). -/
theorem goFail_take {GF : BundledGFunctors} {C : WalCodec} (hC : C.Ok) {fs : List (DecFile GF)} {k : Nat}
    {off : Nat} {c : w32} {s : WalStop} {off' : Nat} {c' : w32} (hL : LaterOk C (fs.map (·.bs)))
    (h : GoFail C (fs.map (·.bs)) off c s ((fs.drop k).map (·.bs)) off' c') : fs.take k = [] := by
  have he := goFail_here hC hL h
  have hl := congrArg List.length he
  simp only [List.length_map, List.length_drop] at hl
  rw [List.take_eq_nil_iff]
  rcases fs with _ | ⟨F, fs⟩
  · exact .inr rfl
  · left; simp only [List.length_cons] at hl; omega

/-- **The WAL's files from the `kk`-th named segment on are `LaterOk`** (the WAL's tail idle; as
`walFilesAt`). -/
theorem walLaterOk {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat) :
    LaterOk C ((lay.segs.drop kk).map segImg) := by
  by_cases hkk : kk < lay.segs.length
  rotate_left
  · rw [List.drop_eq_nil_of_le (by omega)]
    intro g hg; simp at hg
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
  generalize hL : chainSegs C 0#32 (segsDs Mr d.metadata true [] A) = L at hrecs
  have hlenA : L.length = A.length := by rw [← hL, length_chainSegs, length_segsDs]
  have hfit : RecsFit C (L.flatten ++ lastRecs C Mr d.metadata A Sl) := by
    have h := hab.fit
    rw [hSs, hsplit, recsOfSegs_snocR] at h
    rw [← hL, flatten_chainSegs]
    exact h
  have hstreamL : segStream C Mr d lay.cuts lay.cuts.length = recFrames C (lastRecs C Mr d.metadata A Sl) := by
    unfold segStream; rw [hrecs, ← hAl, ← hlenA, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp
  have hstream : ∀ i (hi : i < A.length), segStream C Mr d lay.cuts i = recFrames C (L[i]'(by omega)) := by
    intro i hi
    unfold segStream
    rw [hrecs, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hsegs : lay.segs = lay.segs.dropLast ++ [lay.segs.getLast hne] := (List.dropLast_concat_getLast _).symm
  generalize hgL : lay.segs.getLast hne = gL at hsegs
  have hgL' : lay.segs.getLast? = some gL := by rw [List.getLast?_eq_some_getLast hne, hgL]
  have hTL := hab.lastEx hex gL hgL'
  have himg := tailLast_img hTL hwr
  -- every file of the chain's segments but the first, and the last file, start with a frame
  have hcut : ∀ (p : Nat) (rs : List WalRec), 1 ≤ p → L[p]? = some rs →
      ∃ (y : WalRec) (rest : List w8), recFrames C rs = frame (C.encRec y) ++ rest ∧
        (C.encRec y).length < 2 ^ 56 := by
    intro p rs hp hrs
    have hrs' := hrs
    rw [← hL] at hrs'
    obtain ⟨c', D, hD, hrsD⟩ := chainSegs_getElem? C _ _ p rs hrs'
    obtain ⟨hs, rest, rfl⟩ := segsDs_cut' Mr d.metadata true [] A p hp D hD
    obtain ⟨r, rs', h1, -⟩ := chainRecs_cutHead C Mr d.metadata c' hs rest
    rw [hrsD, h1, recFrames_cons]
    refine ⟨r, _, rfl, hfit r ?_⟩
    apply List.mem_append_left
    apply List.mem_flatten.2
    refine ⟨rs, List.mem_of_getElem? hrs, ?_⟩
    rw [hrsD, h1]; simp
  have hlast : ∃ (y : WalRec) (rest : List w8), segImg gL = frame (C.encRec y) ++ rest ∧
      (C.encRec y).length < 2 ^ 56 := by
    obtain ⟨r, rs', h1, -⟩ := lastRecs_head C Mr d.metadata A Sl
    rw [himg, hstreamL, h1, recFrames_cons, List.append_assoc]
    refine ⟨r, _, rfl, hfit r ?_⟩
    apply List.mem_append_right
    rw [h1]; simp
  have hfiles : (lay.segs.drop kk).map segImg = (L.drop (lay.first + kk)).map (recFrames C) ++ [segImg gL] := by
    have hdl : lay.segs.dropLast.length + 1 = lay.segs.length := by
      rw [List.length_dropLast]; have := List.length_pos_iff.2 hne; omega
    · conv => lhs; rw [hsegs]
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
  intro g hg
  generalize hq : lay.first + kk = q at hfiles hg
  rcases hd : L.drop q with _ | ⟨a, as0⟩
  · rw [hd] at hg; simp at hg
  · rw [hd] at hg
    simp only [List.map_cons, List.cons_append, List.tail_cons, List.mem_append, List.mem_map,
      List.mem_singleton] at hg
    rcases hg with ⟨rs, hrs, rfl⟩ | rfl
    · have has : L.drop (q + 1) = as0 := by
        rw [← List.drop_drop, hd]; rfl
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (has ▸ hrs)
      rw [List.getElem?_drop] at hi
      exact hcut _ rs (by omega) hi
    · exact hlast

end later

/-! ## The filter in place

`snaps[n] = s` for each `s` at or below the commit (S/wal.go:705-712): after `i` snapshots the slice holds
the kept pointers then the original ones from `n` on (`n` the number kept, at most `i`). -/

section keep
variable [GooseExts]

/-- The (pointer, snapshot) pairs at or below the commit `cm`. -/
def vseKeep (cm : w64) (xs : List (Loc × (w64 × w64))) : List (Loc × (w64 × w64)) :=
  xs.filter (fun x => decide (uint.nat x.2.1 ≤ uint.nat cm))

theorem vseKeep_append (cm : w64) (a b : List (Loc × (w64 × w64))) :
    vseKeep cm (a ++ b) = vseKeep cm a ++ vseKeep cm b := by
  simp [vseKeep, List.filter_append]

theorem vseKeep_take_succ (cm : w64) (ps : List Loc) (S : List (w64 × w64)) (i : Nat)
    (hi : i < ps.length) (hS : ps.length = S.length) :
    vseKeep cm ((ps.zip S).take (i + 1)) = vseKeep cm ((ps.zip S).take i) ++
      (if uint.nat (S[i]'(by omega)).1 ≤ uint.nat cm then [(ps[i], S[i]'(by omega))] else []) := by
  have hz : (ps.zip S)[i]? = some (ps[i], S[i]'(by omega)) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨List.getElem?_eq_getElem _, List.getElem?_eq_getElem _⟩
  rw [List.take_add_one, hz, Option.toList_some, vseKeep_append]
  congr 1
  simp only [vseKeep, List.filter_cons, List.filter_nil]
  split <;> simp_all

theorem vseKeep_length_le (cm : w64) (xs : List (Loc × (w64 × w64))) (i : Nat) :
    (vseKeep cm (xs.take i)).length ≤ i := by
  have h1 := List.length_filter_le (fun x : Loc × (w64 × w64) => decide (uint.nat x.2.1 ≤ uint.nat cm)) (xs.take i)
  have h2 := List.length_take_le i xs
  unfold vseKeep; omega

/-- The slice's contents: the kept pointers, then the original ones from their number on. -/
def vseKeepL (K : List (Loc × (w64 × w64))) (ps : List Loc) : List Loc :=
  K.map Prod.fst ++ ps.drop K.length

theorem vseKeepL_get (K : List (Loc × (w64 × w64))) (ps : List Loc) (i : Nat) (hi : K.length ≤ i) :
    (vseKeepL K ps)[i]? = ps[i]? := by
  unfold vseKeepL
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop]
  congr 1; simp; omega

theorem vseKeepL_length (K : List (Loc × (w64 × w64))) (ps : List Loc) (h : K.length ≤ ps.length) :
    (vseKeepL K ps).length = ps.length := by
  unfold vseKeepL; simp; omega

theorem vseKeepL_set (K : List (Loc × (w64 × w64))) (ps : List Loc) (x : Loc) (y : w64 × w64)
    (h : K.length < ps.length) :
    (vseKeepL K ps).set K.length x = vseKeepL (K ++ [(x, y)]) ps := by
  unfold vseKeepL
  rw [List.set_append_right _ _ (by simp)]
  simp only [List.length_map, Nat.sub_self, List.map_append, List.map_cons, List.map_nil,
    List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc,
    List.singleton_append]
  congr 1
  obtain ⟨z, zs, hz⟩ : ∃ z zs, ps.drop K.length = z :: zs := by
    rcases h' : ps.drop K.length with _ | ⟨z, zs⟩
    · have := congrArg List.length h'; simp at this; omega
    · exact ⟨z, zs, rfl⟩
  rw [hz, List.set_cons_zero]
  congr 1
  rw [← List.drop_drop, hz]; rfl

theorem vseKeepL_take (K : List (Loc × (w64 × w64))) (ps : List Loc) :
    (vseKeepL K ps).take K.length = K.map Prod.fst := by
  unfold vseKeepL
  rw [List.take_append_of_le_length (by simp)]
  exact List.take_of_length_le (by simp)

theorem vseKeep_snd (cm : w64) :
    ∀ (ps : List Loc) (S : List (w64 × w64)), ps.length = S.length →
    (vseKeep cm (ps.zip S)).map Prod.snd = S.filter (fun p => decide (uint.nat p.1 ≤ uint.nat cm))
  | [], [], _ => rfl
  | p :: ps, s :: S, h => by
    have ih := vseKeep_snd cm ps S (by simpa using h)
    simp only [List.zip_cons_cons, vseKeep, List.filter_cons] at ih ⊢
    split <;> simp_all
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

end keep

/-! ## The decode loop's steps -/

section step
variable [GooseExts]

/-- No stop returns `nil` (`io.EOF` and `io.ErrUnexpectedEOF` are not `nil`). -/
theorem stopErr_ne_nil {eof ueof : GoInterface} (h1 : eof ≠ GoInterface.nil) (h2 : ueof ≠ GoInterface.nil)
    (s : WalStop) : ¬ stopErr eof ueof s GoInterface.nil := by
  have h1' : GoInterface.nil ≠ eof := fun h => h1 h.symm
  have h2' : GoInterface.nil ≠ ueof := fun h => h2 h.symm
  cases s
  all_goals try rename_i t; cases t
  all_goals (simp only [stopErr]; first | exact h1' | exact h2' | exact fun h => h.1 rfl)

/-- **A record step of the loop's invariant** (`VsLoop ∧ FilesAt ∧ LaterOk`): the decoder's `.ok`, the
reader's CRC check passed. -/
theorem vse_step {GF : BundledGFunctors} {C : WalCodec} (hC : C.Ok) {R0 : DecOut} {acc : List WalRec}
    {fs fsD : List (DecFile GF)} {kD k off off' : Nat} {c c' : w32} {r : WalRec} {fs' : List (List w8)}
    (hL : VsLoop C R0 acc (fsD.map (·.bs)) off c) (hFA : FilesAt C (fsD.map (·.bs)) off c)
    (hLO : LaterOk C (fsD.map (·.bs))) (hkD : fsD = fs.drop kD)
    (h : goDecode C (fsD.map (·.bs)) off c = .ok r fs' off' c') (hfs : (fsD.drop k).map (·.bs) = fs')
    (hnc : ¬ (r.typ = crcType ∧ crcRecBad c' r)) :
    r ∈ R0.recs ∧ VsLoop C R0 (acc ++ [r]) ((fsD.drop k).map (·.bs)) off' (rdCrc c' r) ∧
      FilesAt C ((fsD.drop k).map (·.bs)) off' (rdCrc c' r) ∧ LaterOk C ((fsD.drop k).map (·.bs)) ∧
      fsD.drop k = fs.drop (kD + k) := by
  subst hfs
  obtain ⟨h1, h2⟩ := vsLoop_ok hL h hnc
  refine ⟨h1, h2, filesAt_ok hC hFA h hnc, ?_, ?_⟩
  · rw [List.map_drop]; exact laterOk_drop hLO k
  · rw [hkD, List.drop_drop]

theorem rdCrc_ne {c : w32} {r : WalRec} (h : r.typ ≠ crcType) : rdCrc c r = c := by
  simp [rdCrc, h]

theorem vseSnaps_snoc_snap {U : WalUnmarshal} (acc : List WalRec) {r : WalRec} {p : w64 × w64}
    (hT : r.typ = snapshotType) (hp : U.decSnap r.data = some p) :
    vseSnaps U ((acc ++ [r]).map (fun r => (r.typ, r.data))) =
      vseSnaps U (acc.map (fun r => (r.typ, r.data))) ++ [p] := by
  rw [List.map_append, vseSnaps_append]
  simp [vseSnaps, hT, hp]

theorem vseSnaps_snoc_other {U : WalUnmarshal} (acc : List WalRec) {r : WalRec}
    (hT : r.typ ≠ snapshotType) :
    vseSnaps U ((acc ++ [r]).map (fun r => (r.typ, r.data))) = vseSnaps U (acc.map (fun r => (r.typ, r.data))) := by
  rw [List.map_append, vseSnaps_append]
  simp [vseSnaps, hT]

theorem vseHs_snoc_state {U : WalUnmarshal} (h0 : HardStateM) (acc : List WalRec) {r : WalRec}
    {h : HardStateM} (hT : r.typ = stateType) (hh : U.decState r.data = some h) :
    vseHs U h0 ((acc ++ [r]).map (fun r => (r.typ, r.data))) = h := by
  rw [List.map_append, vseHs_append]
  simp [vseHs, vseHsStep, hT, hh]

theorem vseHs_snoc_other {U : WalUnmarshal} (h0 : HardStateM) (acc : List WalRec) {r : WalRec}
    (hT : r.typ ≠ stateType) :
    vseHs U h0 ((acc ++ [r]).map (fun r => (r.typ, r.data))) = vseHs U h0 (acc.map (fun r => (r.typ, r.data))) := by
  rw [List.map_append, vseHs_append]
  simp [vseHs, vseHsStep, hT]

end step

end WalFs
end EtcdGrove
end Perennial

end
