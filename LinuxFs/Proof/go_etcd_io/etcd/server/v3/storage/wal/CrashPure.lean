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
      (lay'.segs.map (·.ino)).Sublist (lay.segs.map (·.ino)) ∧
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
  have hne' : (crashLay fo lay q S.length).segs ≠ [] := by
    intro h; have := congrArg List.length h; rw [hlenSegs] at this; simp at this; omega
  have hpreS : S <+: f0.contents := hpre0
  have hSlen : S.length ≤ f0.contents.length := hpreS.length_le
  refine ⟨d', crashLay fo lay q S.length, Or.inr ⟨I, segStart lay.cuts (lay.first + q), himg,
    hpur, rfl⟩, rfl, rfl, hent, ?abs, ?fit, rfl, rfl, rfl, ?lastbs, ?sub, ?inos⟩
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
            refine ⟨[], ?_, by simp, fun _ => rfl, ?_⟩ <;> simp [List.getD_eq_getElem?_getD, hb]
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
    · exact hne'
  case fit =>
    have hp := (segs_pre C Mr d.metadata (P := I.map WalOpG.toM) (Q := d.H.map WalOpG.toM)
      (le_segStart_length hsorted) htI hpI).1
    exact fun r hr => habs.fit r (hp.subset hr)
  case lastbs =>
    intro g hg
    rw [hlast'] at hg
    cases hg
    rw [hold]
  case sub =>
    rw [hmapIno]; exact (List.drop_sublist _ _).map _
  case inos =>
    intro g hg
    obtain ⟨g1, hg1, f, hf, rfl⟩ := hmem g hg
    exact ⟨List.mem_map_of_mem (f := (·.ino)) (List.mem_of_mem_drop hg1), f, hf, rfl, rfl⟩

/-! ## All the WALs -/

theorem mem_segsAll {Ls : GMap GoString WalLay} {dir : GoString} {lay : WalLay}
    (h : Ls !! dir = some lay) {g : SegG} (hg : g ∈ lay.segs) : g ∈ segsAll Ls := by
  unfold segsAll
  exact List.mem_flatMap.2 ⟨(dir, lay), (GMap.mem_toList Ls dir lay).2 h, hg⟩

/-- A segment of the layouts is a segment of one of them. -/
theorem segsAll_mem {Ls : GMap GoString WalLay} {g : SegG} (h : g ∈ segsAll Ls) :
    ∃ dir lay, Ls !! dir = some lay ∧ g ∈ lay.segs := by
  unfold segsAll at h
  obtain ⟨⟨dir, lay⟩, hkv, hg⟩ := List.mem_flatMap.1 h
  exact ⟨dir, lay, (GMap.mem_toList Ls dir lay).1 hkv, hg⟩

theorem pairwise_mem_ne {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => by cases ha
  | c :: l, hl, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.1 ha with ea | ha'
    · rcases List.mem_cons.1 hb with eb | hb'
      · exact absurd (ea.trans eb.symm) hne
      · rw [ea]; exact hl.1 b hb'
    · rcases List.mem_cons.1 hb with eb | hb'
      · rw [eb]; exact hs _ _ (hl.1 a ha')
      · exact pairwise_mem_ne hs hl.2 ha' hb' hne

/-- **The segments' inodes are distinct** iff they are within each layout and across layouts. -/
theorem segsAll_nodup_iff (Ls : GMap GoString WalLay) :
    ((segsAll Ls).map (·.ino)).Nodup ↔
      (∀ dir lay, Ls !! dir = some lay → (lay.segs.map (·.ino)).Nodup) ∧
      (∀ dir dir' lay lay', dir ≠ dir' → Ls !! dir = some lay → Ls !! dir' = some lay' →
        ∀ g ∈ lay.segs, ∀ g' ∈ lay'.segs, g.ino ≠ g'.ino) := by
  unfold segsAll
  rw [List.map_flatMap]
  unfold List.Nodup
  rw [List.pairwise_flatMap]
  have hk := GMap.toList_keys_nodup Ls
  unfold List.Nodup at hk
  rw [List.pairwise_map] at hk
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun dir lay h => h1 (dir, lay) ((GMap.mem_toList _ _ _).2 h),
      fun dir dir' lay lay' hne hl hl' g hg g' hg' => ?_⟩
    have := pairwise_mem_ne (R := fun a₁ a₂ : GoString × WalLay =>
        ∀ x ∈ a₁.2.segs.map (·.ino), ∀ y ∈ a₂.2.segs.map (·.ino), x ≠ y)
      (fun a b h x hx y hy => (h y hy x hx).symm) h2 ((GMap.mem_toList _ _ _).2 hl)
      ((GMap.mem_toList _ _ _).2 hl') (fun h => hne (congrArg Prod.fst h))
    exact this _ (List.mem_map_of_mem hg) _ (List.mem_map_of_mem hg')
  · rintro ⟨h1, h2⟩
    refine ⟨fun kv hkv => h1 kv.1 kv.2 ((GMap.mem_toList _ _ _).1 hkv), ?_⟩
    refine hk.imp_of_mem (fun {a b} ha hb hab => ?_)
    intro x hx y hy
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hy
    exact h2 a.1 b.1 a.2 b.2 hab ((GMap.mem_toList _ _ _).1 ha) ((GMap.mem_toList _ _ _).1 hb)
      g hg g' hg'

/-- Layouts whose segments' inodes are each a sublist of an old layout's (at the same directory)
keep the old layouts' inodes distinct. -/
theorem segsAll_nodup_sub {Ls Ls' : GMap GoString WalLay} (h : ((segsAll Ls).map (·.ino)).Nodup)
    (hsub : ∀ dir lay', Ls' !! dir = some lay' → ∃ lay, Ls !! dir = some lay ∧
      (lay'.segs.map (·.ino)).Sublist (lay.segs.map (·.ino))) :
    ((segsAll Ls').map (·.ino)).Nodup := by
  obtain ⟨h1, h2⟩ := (segsAll_nodup_iff Ls).1 h
  refine (segsAll_nodup_iff Ls').2 ⟨fun dir lay' hl' => ?_, fun dir dir' l1 l2 hne h1' h2' g hg g' hg' => ?_⟩
  · obtain ⟨lay, hl, hs⟩ := hsub dir lay' hl'
    exact (h1 dir lay hl).sublist hs
  · obtain ⟨k1, hk1, hs1⟩ := hsub dir l1 h1'
    obtain ⟨k2, hk2, hs2⟩ := hsub dir' l2 h2'
    obtain ⟨x, hx, ex⟩ := List.mem_map.1 (hs1.subset (List.mem_map_of_mem (f := (·.ino)) hg))
    obtain ⟨y, hy, ey⟩ := List.mem_map.1 (hs2.subset (List.mem_map_of_mem (f := (·.ino)) hg'))
    rw [← ex, ← ey]
    exact h2 dir dir' k1 k2 hne hk1 hk2 x hx y hy

theorem inArea_name {r dir nm nm' : GoString} (h : InArea r dir nm) (h' : InArea r dir nm') :
    nm = nm' := by
  have e := h.2.symm.trans h'.2
  exact List.append_cancel_left e

/-- What the crash leaves of the WAL in `dir` (`d` its state): its crashed state and next layout. -/
def CrashGood (C : WalCodec) (Mr : WalMarshal) (jr : Ino) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (m' : Tree) (st' : Fs.OsState) (dir : GoString) (d : WalDur)
    (o : Option (WalDur × WalLay)) : Prop :=
  walCrash d (o.map Prod.fst) ∧
  (o = none → ∃ nm, InArea s.area dir nm ∧ m'.entry jr nm = none) ∧
  (∀ d' lay', o = some (d', lay') → ∃ nm, InArea s.area dir nm ∧
    lay'.jr = jr ∧ lay'.nm = nm ∧ m'.entry jr nm = some (.dir lay'.j) ∧
    WalAbsD C Mr d' lay' (entsOf m' lay'.j) ∧
    RecsFit C (recsOfSegs C Mr d'.metadata (segsOf (histM d') lay'.cuts)) ∧
    lay'.wr = lay'.so ∧ lay'.wr = lay'.z0 ∧
    lay'.z0 = (segStream C Mr d' lay'.cuts lay'.cuts.length).length ∧
    (∀ g, lay'.segs.getLast? = some g → g.bs = lay'.old.map durB) ∧
    (∃ lay, Ls !! dir = some lay ∧ (lay'.segs.map (·.ino)).Sublist (lay.segs.map (·.ino))) ∧
    ∀ g ∈ lay'.segs, g.ino ∈ (segsAll Ls).map (·.ino) ∧
      ∃ f, st'.fs.files !! g.ino = some f ∧ g.om = initMeta f ∧ g.bs = f.contents.map durB)

theorem crashGood_exists (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (s : AbsDiskState) (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat) (m' : Tree)
    (st st' : Fs.OsState) (hok : WalsOk C Mr R jr s Ls cl n)
    (hreg : RegionCrashed cl n m') (htree : st'.fs.treeDur = m') (hw1 : W1 C st st')
    (hfiles : ∀ g ∈ segsAll Ls,
      FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (st'.fs.files !! g.ino) ∧
      (Named m' g.ino → (st'.fs.files !! g.ino).isSome) ∧
      ∃ f, st.fs.files !! g.ino = some f ∧ ∀ b (y : ByteG), g.bs[b]? = some y → f.cand b = y.2)
    (dir : GoString) (d : WalDur) (hd : s.wal !! dir = some d) :
    ∃ o, CrashGood C Mr jr s Ls m' st' dir d o := by
  obtain ⟨lay, nm, hj, hLs, hin, hjr, hnm, -, habs, alt, halt, hcok⟩ := hok.1 dir d hd
  have hf : ∀ g ∈ lay.segs, _ := fun g hg => hfiles g (mem_segsAll hLs hg)
  have hw1G := w1G_of_W1 C st st' m' lay hw1 htree (fun g hg => by
    obtain ⟨hcr, -, hc⟩ := hf g hg
    refine ⟨fun f' hf' => ?_, hc⟩
    have := (hcr f' hf').2.2.1
    rw [(habs.metas g hg).2.2.2] at this
    exact this)
  have hct := hcok m' (fun i => st'.fs.files !! i) hreg (fun g hg => (hf g hg).1)
    (fun g hg => (hf g hg).2.1) hw1G
  -- the layout whose `CrashTo` the crash gives: `lay`, or the one before a pending cut's rename
  obtain ⟨lay0, ents0, habs0, hjr0, hnm0, hpre, hct0⟩ : ∃ lay0 ents0, WalAbsD C Mr d lay0 ents0 ∧
      lay0.jr = lay.jr ∧ lay0.nm = lay.nm ∧ lay0.segs <+: lay.segs ∧
      CrashTo C Mr d lay0 m' (fun i => st'.fs.files !! i) := by
    rcases hct with h | ⟨l0, hl0, h⟩
    · exact ⟨lay, _, habs, rfl, rfl, List.prefix_refl _, h⟩
    · obtain ⟨⟨e0, ha0⟩, h1, h2, -, h3⟩ := halt l0 hl0
      exact ⟨l0, e0, ha0, h1, h2, h3, h⟩
  rcases crashTo_start C Mr d lay0 _ m' (fun i => st'.fs.files !! i) habs0
    (fun g hg => (hf g (hpre.subset hg)).2.1) hct0 with ⟨hn, he⟩ | ⟨d', lay', hc, hjr', hnm', he, hrest⟩
  · refine ⟨none, Or.inl ⟨hn, rfl⟩, ⟨fun _ => ⟨nm, hin, ?_⟩, fun _ _ h => by cases h⟩⟩
    rw [← hjr, ← hnm, ← hjr0, ← hnm0]; exact he
  · refine ⟨some (d', lay'), hc, ⟨fun h => (by cases h), fun d1 l1 h => ?_⟩⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨ha, hfit, h1, h2, h3, h4, hsub, h5⟩ := hrest
    refine ⟨nm, hin, by rw [hjr', hjr0, hjr], by rw [hnm', hnm0, hnm],
      by rw [← hjr, ← hnm, ← hjr0, ← hnm0]; exact he, ha, hfit,
      h1, h2, h3, h4, ⟨lay, hLs, hsub.trans (hpre.sublist.map _)⟩, fun g hg => ?_⟩
    obtain ⟨hi, hrest⟩ := h5 g hg
    refine ⟨?_, hrest⟩
    obtain ⟨g1, hg1, he1⟩ := List.mem_map.1 hi
    rw [← he1]
    exact List.mem_map_of_mem (f := (·.ino)) (mem_segsAll hLs (hpre.subset hg1))

/-- A map with the keys of `m`, each value given by `f`. -/
def gmapBind {K V V' : Type} [DecidableEq K] (m : GMap K V) (f : K → V → Option V') : GMap K V' :=
  ⟨fun k => (m !! k).bind (f k), by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨l, fun k h => hl k ?_⟩
    cases hm : m.lookup k with
    | none =>
      exfalso
      have : (m !! k) = none := hm
      simp [this] at h
    | some v => rfl⟩

theorem gmapBind_lookup {K V V' : Type} [DecidableEq K] (m : GMap K V) (f : K → V → Option V')
    (k : K) : gmapBind m f !! k = (m !! k).bind (f k) := rfl

/-- **What a generation's start says of the WALs** (pure), the tree being `m` (nothing logged):
each WAL of `s` has a layout whose directory is at its name in the area, with the static relation
over the directory's entries, every segment's bytes durable and nothing appended; a directory of
the area with no WAL holds no `.wal` file; every durable directory resolves. -/
def WalsStart (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (m : Tree) : Prop :=
  (∀ dir d, s.wal !! dir = some d → ∃ lay nm, Ls !! dir = some lay ∧ InArea s.area dir nm ∧
    lay.jr = jr ∧ lay.nm = nm ∧ m.entry jr nm = some (.dir lay.j) ∧
    WalAbsD C Mr d lay (entsOf m lay.j) ∧
    RecsFit C (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)) ∧
    lay.wr = lay.so ∧ lay.wr = lay.z0 ∧ lay.z0 = (segStream C Mr d lay.cuts lay.cuts.length).length ∧
    (∀ g, lay.segs.getLast? = some g → g.bs = lay.old.map durB)) ∧
  (∀ dir, s.wal !! dir = none → Ls !! dir = none) ∧
  (∀ dir nm, InArea s.area dir nm → s.wal !! dir = none → ∀ J, m.entry jr nm = some (.dir J) →
    walInos (entsOf m J) = []) ∧
  (∀ dd, s.dirs !! dd = some () → ∃ J, lookupH R (m, []) dd = some (.dir J))

/-- **The crash's pure core** (plan §2.2): from what the invariant says of the WALs, what a crash of
the claims allows of the tree (`m'`), what the crash did to each segment (`FileCrashedR` of its
halves, its candidates the state's) and W1: the crashed WAL state `s'` (`walStCrash s s'`) and its
layouts over `m'` and the crashed files. Each WAL's crash condition gives its `CrashTo` (W1 over the
ghost candidates, `W1G`, from W1 over the state's: `w1G_of_W1`, the only place W1 enters); the new
layout keeps the cuts, the kept segments with their files' start resources, the last file's image
as the bytes under its stream (`crashTo_start`). -/
theorem walCrash_pure (C : WalCodec) (_hC : C.Ok) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (s : AbsDiskState) (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat) (m' : Tree)
    (st st' : Fs.OsState) (hok : WalsOk C Mr R jr s Ls cl n) (hk : walKeysInArea s)
    (hreg : RegionCrashed cl n m') (htree : st'.fs.treeDur = m') (hw1 : W1 C st st')
    (hfiles : ∀ g ∈ segsAll Ls,
      FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (st'.fs.files !! g.ino) ∧
      (Named m' g.ino → (st'.fs.files !! g.ino).isSome) ∧
      ∃ f, st.fs.files !! g.ino = some f ∧ ∀ b (y : ByteG), g.bs[b]? = some y → f.cand b = y.2) :
    ∃ (s' : AbsDiskState) (Ls' : GMap GoString WalLay), walStCrash s s' ∧ s'.area = s.area ∧
      walKeysInArea s' ∧ WalsStart C Mr R jr s' Ls' m' ∧ ((segsAll Ls').map (·.ino)).Nodup ∧
      ∀ dir lay, Ls' !! dir = some lay → ∀ g ∈ lay.segs, g.ino ∈ (segsAll Ls).map (·.ino) ∧
        ∃ f, st'.fs.files !! g.ino = some f ∧ g.om = initMeta f ∧ g.bs = f.contents.map durB := by
  classical
  let G := CrashGood C Mr jr s Ls m' st'
  let F : GoString → WalDur → Option (WalDur × WalLay) := fun dir d =>
    if h : ∃ o, G dir d o then Classical.choose h else none
  have hF : ∀ dir d, s.wal !! dir = some d → G dir d (F dir d) := by
    intro dir d hd
    have h := crashGood_exists C Mr R jr s Ls cl n m' st st' hok hreg htree hw1 hfiles dir d hd
    show G dir d (if h : ∃ o, G dir d o then Classical.choose h else none)
    rw [dite_eq_left h]
    exact Classical.choose_spec h
  let s' : AbsDiskState := { s with wal := gmapBind s.wal (fun k d => (F k d).map Prod.fst) }
  let Ls' : GMap GoString WalLay := gmapBind s.wal (fun k d => (F k d).map Prod.snd)
  have hs' : ∀ dir, s'.wal !! dir = (s.wal !! dir).bind (fun d => (F dir d).map Prod.fst) :=
    fun dir => gmapBind_lookup _ _ _
  have hLs' : ∀ dir, Ls' !! dir = (s.wal !! dir).bind (fun d => (F dir d).map Prod.snd) :=
    fun dir => gmapBind_lookup _ _ _
  -- the new WALs, from their old ones
  have hsome : ∀ dir d', s'.wal !! dir = some d' → ∃ d lay, s.wal !! dir = some d ∧
      F dir d = some (d', lay) := by
    intro dir d' h
    rw [hs'] at h
    cases hd : s.wal !! dir with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h
      simp only [Option.bind_some] at h
      cases hFd : F dir d with
      | none => rw [hFd] at h; cases h
      | some p =>
        rw [hFd] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact ⟨d, p.2, rfl, by rw [hFd, ← h]⟩
  have hsomeL : ∀ dir lay, Ls' !! dir = some lay → ∃ d d', s.wal !! dir = some d ∧
      F dir d = some (d', lay) := by
    intro dir lay h
    rw [hLs'] at h
    cases hd : s.wal !! dir with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h
      simp only [Option.bind_some] at h
      cases hFd : F dir d with
      | none => rw [hFd] at h; cases h
      | some p =>
        rw [hFd] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact ⟨d, p.1, rfl, by rw [hFd, ← h]⟩
  refine ⟨s', Ls', ⟨rfl, rfl, fun dir d hd => ?_, fun dir hd => ?_⟩, rfl, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hs', hd]; exact (hF dir d hd).1
  · rw [hs', hd]; rfl
  · intro k d' h
    obtain ⟨d, -, hd, -⟩ := hsome k d' h
    exact hk k d hd
  · intro dir d' h
    obtain ⟨d, lay, hd, hFd⟩ := hsome dir d' h
    obtain ⟨nm, hin, hjr, hnm, he, ha, hfit, h1, h2, h3, h4, -, -⟩ := (hF dir d hd).2.2 d' lay hFd
    refine ⟨lay, nm, ?_, hin, hjr, hnm, he, ha, hfit, h1, h2, h3, h4⟩
    rw [hLs', hd]; simp [hFd]
  · intro dir h
    rw [hLs']
    rw [hs'] at h
    cases hd : s.wal !! dir with
    | none => rfl
    | some d =>
      rw [hd] at h
      simp only [Option.bind_some] at h ⊢
      cases hFd : F dir d with
      | none => rfl
      | some p => rw [hFd] at h; cases h
  · intro dir nm hin h J hJ
    rw [hs'] at h
    cases hd : s.wal !! dir with
    | none => exact hok.2.2.2.2.1 dir nm hin hd m' hreg J hJ
    | some d =>
      rw [hd] at h
      simp only [Option.bind_some] at h
      cases hFd : F dir d with
      | none =>
        obtain ⟨nm', hin', he⟩ := (hF dir d hd).2.1 hFd
        rw [inArea_name hin hin', he] at hJ; cases hJ
      | some p => rw [hFd] at h; cases h
  · intro dd hdd
    exact hok.2.2.2.2.2 dd hdd m' hreg
  · refine segsAll_nodup_sub hok.2.2.1 (fun dir lay h => ?_)
    obtain ⟨d, d', hd, hFd⟩ := hsomeL dir lay h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h5, -⟩ := (hF dir d hd).2.2 d' lay hFd
    exact h5
  · intro dir lay h
    obtain ⟨d, d', hd, hFd⟩ := hsomeL dir lay h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h5⟩ := (hF dir d hd).2.2 d' lay hFd
    exact h5

end crashpure

end WalFs
end EtcdGrove
end Perennial

end
