/- Lean-first (no Rocq counterpart).

# The WAL's crash, pure part (`notes/wal-fsext-plan.md`, §2.2; W1 log)

`crashTo_start`: one WAL's `CrashTo` (what its crash condition gives for a crash) gives its crashed
state (`walCrash d (some d')`, or the WAL gone) and the next generation's layout `lay'` with the
static relation over the crashed tree: the cuts kept, the segments from the first kept on with their
crashed files' start resources (`initMeta`, every byte durable), the last file's image as the bytes
under its stream, nothing appended (`wr = so = z0`, the stream's end).

W1 does not enter here: `CrashTo` is the conclusion of the crash condition `CrashOk`, which takes W1
over the ghost candidates (`W1G`, from W1 over the state by `w1G_of_W1`). The "accepted frames are
the intended frames" step is in the proofs of `CrashOk` (each operation's, and the start's).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SegPre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section crashpure
variable [GooseExts]

/-- A kept segment, with its crashed file's start resources. -/
def newSeg (fo : Ino → Option Fs.OsFile) (g : SegG) : SegG :=
  match fo g.ino with
  | some f => { g with om := initMeta f, bs := f.contents.map durB }
  | none => g

theorem newSeg_some {fo : Ino → Option Fs.OsFile} {g : SegG} {f : Fs.OsFile}
    (h : fo g.ino = some f) :
    newSeg fo g = { g with om := initMeta f, bs := f.contents.map durB } := by
  simp [newSeg, h]

theorem newSeg_ino (fo : Ino → Option Fs.OsFile) (g : SegG) : (newSeg fo g).ino = g.ino := by
  unfold newSeg; split <;> rfl

theorem newSeg_name (fo : Ino → Option Fs.OsFile) (g : SegG) : (newSeg fo g).name = g.name := by
  unfold newSeg; split <;> rfl

/-- **The next generation's layout** after a crash keeping the segments from the `q`-th on, the
last segment's stream `z` bytes long. -/
def crashLay (fo : Ino → Option Fs.OsFile) (lay : WalLay) (q z : Nat) : WalLay :=
  { lay with
    first := lay.first + q
    segs := (lay.segs.drop q).map (newSeg fo)
    old := (lay.segs.getLast?.map (fun g => imgOf (fo g.ino))).getD []
    wr := z
    so := z
    z0 := z }

theorem contents_length (f : Fs.OsFile) : f.contents.length = f.size := by
  simp [Fs.OsFile.contents]

/-- A file listed by a directory of the tree is named in it. -/
theorem named_of_mem_walInos {m : Tree} {J i : Ino} (h : i ∈ walInos (entsOf m J)) :
    Named m i := by
  unfold walInos at h
  obtain ⟨b, -, hb⟩ := List.mem_filterMap.1 h
  cases hm : m !! J with
  | none =>
    have : entsOf m J !! b = none := by simp [entsOf, hm]
    rw [this] at hb; cases hb
  | some D =>
    have he : entsOf m J = D := by simp [entsOf, hm]
    rw [he] at hb
    refine ⟨J, b, ?_⟩
    unfold Tree.entry
    rw [hm]
    simp only [Option.bind_some]
    split at hb
    · rename_i i' hi; cases hb; exact hi
    · cases hb

theorem walImg_length_ge {E : Type} {H I : List (WalOpG E)} {n : Nat} (h : walImg H n I) :
    n ≤ I.length := by
  obtain ⟨j, h1, h2, rfl | ⟨_, _, _, _, _, rfl⟩⟩ := h <;> simp <;> omega

/-- **One WAL across a crash**: from its static relation and the `CrashTo` its crash condition
gives, the WAL gone (only if not `named`, its name absent), or its crashed state `d'` and the next
generation's layout. -/
theorem crashTo_start (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (ents : Ents)
    (m' : Tree) (fo : Ino → Option Fs.OsFile)
    (habs : WalAbsD C Mr d lay ents)
    (hfo : ∀ g ∈ lay.segs, Named m' g.ino → (fo g.ino).isSome)
    (hct : CrashTo C Mr d lay m' fo) :
    (d.named = false ∧ m'.entry lay.jr lay.nm = none) ∨
    ∃ (d' : WalDur) (lay' : WalLay), walCrash d (some d') ∧ lay'.jr = lay.jr ∧ lay'.nm = lay.nm ∧
      m'.entry lay.jr lay.nm = some (.dir lay'.j) ∧
      WalAbsD C Mr d' lay' (entsOf m' lay'.j) ∧
      RecsFit C (recsOfSegs C Mr d'.metadata (segsOf (histM d') lay'.cuts)) ∧
      lay'.wr = lay'.so ∧ lay'.wr = lay'.z0 ∧
      lay'.z0 = (segStream C Mr d' lay'.cuts lay'.cuts.length).length ∧
      (∀ g, lay'.segs.getLast? = some g → g.bs = lay'.old.map durB) ∧
      ∀ g ∈ lay'.segs, g.ino ∈ lay.segs.map (·.ino) ∧
        ∃ f, fo g.ino = some f ∧ g.om = initMeta f ∧ g.bs = f.contents.map durB := by
  rcases hct with hl | ⟨q, I, hent, hq, hinos, himg, hlastI, hpur, hint, hlast⟩
  · exact Or.inl hl
  right
  have hsorted := habs.cuts.2.1
  have hcm : segStart lay.cuts lay.cuts.length ≤ d.m := habs.lastSynced
  have himgM : walImg (d.H.map WalOpG.toM) d.m (I.map WalOpG.toM) :=
    walImg_map WalOpG.toM WalEnt.toM (fun _ _ => rfl) himg
  obtain ⟨htI, hpI⟩ := walImg_segPre Mr himgM hcm
  -- the kept segments' files
  have hsome : ∀ g ∈ lay.segs.drop q, ∃ f, fo g.ino = some f := by
    intro g hg
    have hn : Named m' g.ino := by
      apply named_of_mem_walInos (J := lay.j)
      rw [hinos]; exact List.mem_map_of_mem hg
    have := hfo g (List.mem_of_mem_drop hg) hn
    exact Option.isSome_iff_exists.1 this
  have hne : lay.segs ≠ [] := by intro h; rw [h] at hq; simp at hq
  obtain ⟨g0, hg0⟩ : ∃ g0, lay.segs.getLast? = some g0 := by
    cases h : lay.segs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some g0 => exact ⟨g0, rfl⟩
  have hg0d : g0 ∈ lay.segs.drop q := by
    have : (lay.segs.drop q).getLast? = some g0 := by
      rw [List.getLast?_drop, ite_eq_right (by omega), hg0]
    exact List.mem_of_getLast? this
  obtain ⟨f0, hf0⟩ := hsome g0 hg0d
  obtain ⟨hpre0, hstop0⟩ := hlast g0 hg0
  rw [hf0] at hpre0 hstop0
  simp only [imgOf, Option.map_some, Option.getD_some] at hpre0 hstop0
  -- the new WAL and layout
  let d' : WalDur := { d with
    H := I
    cut := segStart lay.cuts (lay.first + q)
    unl := min d.unl I.length
    pur := min d.pur I.length }
  let S := segStream C Mr d' lay.cuts lay.cuts.length
  have hS : S = segStream C Mr { d with H := I } lay.cuts lay.cuts.length := rfl
  have hold : (crashLay fo lay q S.length).old = f0.contents := by
    simp [crashLay, hg0, hf0, imgOf]
  have hmem : ∀ g ∈ (crashLay fo lay q S.length).segs, ∃ g1 ∈ lay.segs.drop q, ∃ f,
      fo g1.ino = some f ∧ g = { g1 with om := initMeta f, bs := f.contents.map durB } := by
    intro g hg
    obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg
    obtain ⟨f, hf⟩ := hsome g1 hg1
    exact ⟨g1, hg1, f, hf, newSeg_some hf⟩
  have hlast' : (crashLay fo lay q S.length).segs.getLast? =
      some { g0 with om := initMeta f0, bs := f0.contents.map durB } := by
    simp only [crashLay, List.getLast?_map, List.getLast?_drop, ite_eq_right (show ¬ lay.segs.length ≤ q by omega),
      hg0, Option.map_some, newSeg_some hf0]
  have hmapIno : (crashLay fo lay q S.length).segs.map (·.ino) = (lay.segs.drop q).map (·.ino) := by
    simp only [crashLay, List.map_map]
    exact List.map_congr_left (fun g _ => newSeg_ino fo g)
  have hmapName : (crashLay fo lay q S.length).segs.map (·.name) = (lay.segs.drop q).map (·.name) := by
    simp only [crashLay, List.map_map]
    exact List.map_congr_left (fun g _ => newSeg_name fo g)
  have hlenSegs : (crashLay fo lay q S.length).segs.length = lay.segs.length - q := by
    simp [crashLay]
  have hcutsLen := habs.cuts.2.2
  have hpreS : S <+: f0.contents := hpre0
  have hSlen : S.length ≤ f0.contents.length := hpreS.length_le
  refine ⟨d', crashLay fo lay q S.length, Or.inr ⟨I, segStart lay.cuts (lay.first + q), himg,
    hpur, rfl⟩, rfl, rfl, hent, ?abs, ?fit, rfl, rfl, rfl, ?lastbs, ?inos⟩
  case abs =>
    constructor
    · -- names
      refine ⟨?_, ?_⟩
      · show walInos (entsOf m' lay.j) = _
        rw [hinos, hmapIno]
      · rw [hmapName]
        exact habs.names.2.sublist ((List.drop_sublist _ _).map _)
    · -- cuts
      refine ⟨fun b hb => walCutPos_of_take (le_segStart_length hsorted b hb) htI (habs.cuts.1 b hb),
        hsorted, ?_⟩
      show lay.first + q + (crashLay fo lay q S.length).segs.length = lay.cuts.length + 1
      rw [hlenSegs]; omega
    · -- name bound
      intro k g hk
      have hk' : (crashLay fo lay q S.length).segs[k]? = ((lay.segs.drop q)[k]?).map (newSeg fo) := by
        simp [crashLay]
      rw [hk', List.getElem?_drop] at hk
      cases hg1 : lay.segs[q + k]? with
      | none => rw [hg1] at hk; cases hk
      | some g1 =>
        rw [hg1] at hk
        simp only [Option.map_some, Option.some.injEq] at hk
        subst hk
        obtain ⟨sq, ix, hn, hb⟩ := habs.nameBound (q + k) g1 hg1
        refine ⟨sq, ix, by rw [newSeg_name]; exact hn, fun hpos => ?_⟩
        have e : lay.first + (q + k) = (crashLay fo lay q S.length).first + k := by
          simp only [crashLay]; omega
        rw [← e]
        have := hb (by omega)
        have ht := take_of_take (segStart_le_length hsorted (lay.first + (q + k))) htI
        show walLastIdx ((I.map WalOpG.toM).take (segStart lay.cuts (lay.first + (q + k)))) + 1 ≤ ix
        rw [ht]; exact this
    · -- cut
      exact ⟨rfl, fun _ => hpur⟩
    · -- metas
      intro g hg
      obtain ⟨g1, -, f, -, rfl⟩ := hmem g hg
      simp [initMeta, contents_length]
    · -- intact
      intro k g hk hg
      have hk' : (crashLay fo lay q S.length).segs[k]? = ((lay.segs.drop q)[k]?).map (newSeg fo) := by
        simp [crashLay]
      rw [hk'] at hg
      cases hg1 : (lay.segs.drop q)[k]? with
      | none => rw [hg1] at hg; cases hg
      | some g1 =>
        rw [hg1] at hg
        simp only [Option.map_some, Option.some.injEq] at hg
        subst hg
        have hg1m : g1 ∈ lay.segs.drop q := List.mem_of_getElem? hg1
        obtain ⟨f, hf⟩ := hsome g1 hg1m
        rw [hlenSegs] at hk
        have hi := hint k g1 hg1 (by omega)
        rw [hf] at hi
        simp only [imgOf, Option.map_some, Option.getD_some] at hi
        rw [newSeg_some hf]
        show f.contents.map durB = _
        rw [hi]; rfl
    · -- last
      intro g hg
      rw [hlast'] at hg
      cases hg
      simp only []
      refine ⟨Nat.le_refl _, Nat.le_refl _, ?_, ?_, ?_, Nat.le_refl _, ?_, ?_⟩
      · rw [hold]; simp
      · rw [hold]; exact hSlen
      · intro b x hx
        rw [hold]
        simp only [List.getElem?_map] at hx
        cases hb : f0.contents[b]? with
        | none => rw [hb] at hx; cases hx
        | some y =>
          rw [hb] at hx
          simp only [Option.map_some, Option.some.injEq] at hx
          subst hx
          unfold ByteOk
          by_cases hbS : b < S.length
          · have hbS' : b < (crashLay fo lay q S.length).so := hbS
            simp only [hbS', decide_true, ite_true]
            have hSb : S.getD b 0 = y := by
              obtain ⟨t, ht⟩ := hpreS
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbS]
              rw [← ht, List.getElem?_append_left hbS, List.getElem?_eq_getElem hbS] at hb
              cases hb; rfl
            show durB y = durB (S.getD b 0)
            rw [hSb]
          · have hbS' : ¬ b < (crashLay fo lay q S.length).so := hbS
            have hbS'' : ¬ b < (crashLay fo lay q S.length).wr := hbS
            simp only [hbS', hbS'', decide_false]
            simp [List.getD_eq_getElem?_getD, hb]
      · rw [hold]
        obtain ⟨t, ht⟩ := hpreS
        show S.take S.length = f0.contents.take S.length
        rw [← ht, List.take_append_of_le_length (Nat.le_refl _)]
      · intro h; exact absurd h (Nat.lt_irrefl _)
    · -- synced
      refine ⟨Nat.le_trans (walImg_length_ge himg) (Nat.le_refl _), ?_⟩
      show (recFrames C ((segRecs C Mr { d' with H := I.take d.m } lay.cuts).getD lay.cuts.length [])).length ≤ S.length
      have hp := (segs_pre C Mr d.metadata (P := (I.map WalOpG.toM).take d.m)
        (Q := I.map WalOpG.toM) (le_segStart_length hsorted)
        (take_segPre Mr hcm).1 (take_segPre Mr hcm).2).2.2
      have e1 : histM { d' with H := I.take d.m } = (I.map WalOpG.toM).take d.m := by
        simp [histM, List.map_take]
      unfold segRecs
      rw [e1]
      exact (recFrames_prefix C hp).length_le
    · exact hcm
    · -- fit
      have hp := (segs_pre C Mr d.metadata (P := I.map WalOpG.toM) (Q := d.H.map WalOpG.toM)
        (le_segStart_length hsorted) htI hpI).1
      exact fun r hr => habs.fit r (hp.subset hr)
    · -- tail stop
      intro _ r len c'
      rw [hold]
      exact hstop0 r len c'
  case fit =>
    have hp := (segs_pre C Mr d.metadata (P := I.map WalOpG.toM) (Q := d.H.map WalOpG.toM)
      (le_segStart_length hsorted) htI hpI).1
    exact fun r hr => habs.fit r (hp.subset hr)
  case lastbs =>
    intro g hg
    rw [hlast'] at hg
    cases hg
    rw [hold]
  case inos =>
    intro g hg
    obtain ⟨g1, hg1, f, hf, rfl⟩ := hmem g hg
    exact ⟨List.mem_map_of_mem (f := (·.ino)) (List.mem_of_mem_drop hg1), f, hf, rfl, rfl⟩

end crashpure

end WalFs
end EtcdGrove
end Perennial

end
