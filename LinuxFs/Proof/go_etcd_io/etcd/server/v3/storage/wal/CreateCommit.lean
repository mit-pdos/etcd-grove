/- Lean-first (no Rocq counterpart).

# `Create`'s commit at the rename, pure part (W4, `notes/wal-fsext-plan.md`, "W4 implementation log")

`walsOk_create`: the invariant's pure facts after `renameWAL`'s rename of `nm.tmp` (the directory `J`,
holding the fresh WAL's one segment, synced, and its directory entry committed: F-N1) onto the
WAL-less name `nm` of the area, logged at `x` in the area claim `(jr, N, h)` by a call begun at `st`:
the WAL state with `dir ↦ walDurFresh md`, the layout `lay` of the new WAL, the claims with the area
claim logged (`replClaim`) and `J`'s claim appended (`createClaims`).

* A crash dropping the rename (`¬ K x`) is a crash of the claims before it
  (`regionCrashedK_create_drop`): `nm` absent (`AbsentNone`), the fresh WAL unnamed (`CrashTo`'s left
  disjunct); the other WALs as before.
* A crash keeping it keeps every earlier entry of the area claim and of `J`'s (they took effect before
  the rename's call began): `nm` holds `J`, whose `.wal` names are as now, the segment synced
  (`crashTo_synced`); the tree with the rename undone (`treeSetE` twice) is a crash of the claims
  before it (`regionCrashedK_create_keep`), which the other WALs' crash conditions see as the crashed
  tree itself (they read only `.wal` names and their own names in the area: `crashTo_congr`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCrash
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSynced
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamed
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Crash
public import LinuxFs.Spec.os.Rename

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-! ## Trees with one entry set -/

/-- The tree `m` with the name `b` of the directory `j` set to `v`. -/
def treeSetE (m : Tree) (j : Ino) (b : GoString) (v : Option Node) : Tree :=
  m.upd j (fun D => match v with
    | none => GMap.delete b D
    | some n => <[b := n]> D)

theorem treeSetE_entry (m : Tree) (j : Ino) (b : GoString) (v : Option Node) (j' : Ino)
    (b' : GoString) :
    (treeSetE m j b v).entry j' b' = if j' = j ∧ b' = b then v else m.entry j' b' := by
  unfold treeSetE Tree.upd Tree.entry
  by_cases hj : j' = j
  · subst hj
    rw [GMap.lookup_insert]
    simp only [Option.bind_some]
    by_cases hb : b' = b
    · subst hb
      cases v with
      | none => simp
      | some n => simp [GMap.lookup_insert]
    · simp only [hb, and_false, ite_false]
      cases v with
      | none =>
        simp only
        rw [GMap.lookup_delete_ne _ (Ne.symm hb)]
        cases m !! j' <;> simp
      | some n =>
        simp only
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hb)]
        cases m !! j' <;> simp
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hj)]
    simp [hj]

/-! ## The rename's entry -/

theorem renDirEnt_writes (jr J : Ino) (tmp nm : GoString) (st : Nat) (j : Ino) (b : GoString) :
    (renDirEnt jr tmp nm J st).op.Writes j b ↔ j = jr ∧ (b = tmp ∨ b = nm) := by
  unfold renDirEnt MetaOp.Writes MetaOp.slots
  constructor
  · rintro (h | ⟨j0, b0, h⟩)
    · simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr rfl⟩
    · cases h
  · rintro ⟨rfl, rfl | rfl⟩
    · left; simp
    · left; simp

/-- The area claim's names after the rename (`os.Rename.specDirS`'s `renDirOut`). -/
def renCur (N : NameSet) (h : NamesH) (tmp nm : GoString) (J : Ino) : Ents :=
  restrictN N (<[nm := Node.dir J]> (GMap.delete tmp h.cur))

/-- The claims after the rename: the area claim logged, `J`'s claim appended. -/
def createClaims (cl : List Claim) (jr : Ino) (N : NameSet) (h : NamesH) (x : Nat) (e : LogEntry)
    (c : Ents) (J : Ino) (X : List GoString) (hJ : NamesH) : List Claim :=
  replClaim (jr, N, h) (jr, N, h.log x e c) cl ++ [(J, NameSet.except X, hJ)]

/-! ## Region crashes after the rename -/

/-- `RegionCrashedK` of fewer claims. -/
theorem regionCrashedK_sub {cl1 cl2 : List Claim} {n : Nat} {m' : Tree} {K : Nat → Prop}
    (hsub : ∀ c ∈ cl1, c ∈ cl2) (h : RegionCrashedK cl2 n m' K) : RegionCrashedK cl1 n m' K :=
  ⟨fun c hc c' hc' => h.1 c (hsub c hc) c' (hsub c' hc'), fun c hc => h.2.1 c (hsub c hc),
    fun c hc => h.2.2 c (hsub c hc)⟩

/-- **A crash dropping the rename** is a crash of the claims before it. -/
theorem regionCrashedK_create_drop {cl : List Claim} {n : Nat} {m' : Tree} {K : Nat → Prop}
    {jr : Ino} {N : NameSet} {h : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {J : Ino}
    {X : List GoString} {hJ : NamesH}
    (hK : RegionCrashedK (createClaims cl jr N h x e c J X hJ) n m' K) (hx : ¬ K x) :
    RegionCrashedK cl n m' K :=
  regionCrashedK_unlog cl n m' K jr N h x e c
    (regionCrashedK_sub (fun c' hc' => List.mem_append_left _ hc') hK) hx

theorem mem_createClaims_area {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {x : Nat}
    {e : LogEntry} {c : Ents} {J : Ino} {X : List GoString} {hJ : NamesH} (hc : (jr, N, h) ∈ cl) :
    (jr, N, h.log x e c) ∈ createClaims cl jr N h x e c J X hJ := by
  classical
  refine List.mem_append_left _ ?_
  simpa using mem_replClaim (c0 := (jr, N, h)) (c1 := (jr, N, h.log x e c)) hc

theorem mem_createClaims_J {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {x : Nat}
    {e : LogEntry} {c : Ents} {J : Ino} {X : List GoString} {hJ : NamesH} :
    (J, NameSet.except X, hJ) ∈ createClaims cl jr N h x e c J X hJ :=
  List.mem_append_right _ (List.mem_singleton_self _)

theorem mem_createClaims_other {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {x : Nat}
    {e : LogEntry} {c : Ents} {J : Ino} {X : List GoString} {hJ : NamesH} {c1 : Claim}
    (hc : c1 ∈ cl) (hne : c1 ≠ (jr, N, h)) : c1 ∈ createClaims cl jr N h x e c J X hJ := by
  classical
  refine List.mem_append_left _ ?_
  simpa [hne] using mem_replClaim (c0 := (jr, N, h)) (c1 := (jr, N, h.log x e c)) hc

/-- The tree with the rename undone: `tmp` holding `J` again, `nm` free. -/
def treeUnren (m' : Tree) (jr : Ino) (tmp nm : GoString) (J : Ino) : Tree :=
  treeSetE (treeSetE m' jr nm none) jr tmp (some (.dir J))

theorem treeUnren_entry (m' : Tree) (jr : Ino) (tmp nm : GoString) (J : Ino) (j : Ino)
    (b : GoString) (hne : tmp ≠ nm) :
    (treeUnren m' jr tmp nm J).entry j b =
      if j = jr ∧ b = tmp then some (.dir J) else if j = jr ∧ b = nm then none else m'.entry j b := by
  unfold treeUnren
  rw [treeSetE_entry, treeSetE_entry]

theorem treeUnren_entry_other {m' : Tree} {jr : Ino} {tmp nm : GoString} {J : Ino} {j : Ino}
    {b : GoString} (hne : tmp ≠ nm) (h : ¬ (j = jr ∧ (b = tmp ∨ b = nm))) :
    (treeUnren m' jr tmp nm J).entry j b = m'.entry j b := by
  rw [treeUnren_entry _ _ _ _ _ _ _ hne]
  have h1 : ¬ (j = jr ∧ b = tmp) := fun ⟨a, b'⟩ => h ⟨a, Or.inl b'⟩
  have h2 : ¬ (j = jr ∧ b = nm) := fun ⟨a, b'⟩ => h ⟨a, Or.inr b'⟩
  simp only [h1, h2, ite_false]

theorem named_treeUnren {m' : Tree} {jr : Ino} {tmp nm : GoString} {J : Ino} {i : Ino}
    (hne : tmp ≠ nm) (h : Named (treeUnren m' jr tmp nm J) i) : Named m' i := by
  obtain ⟨j, b, hb⟩ := h
  refine ⟨j, b, ?_⟩
  rw [treeUnren_entry _ _ _ _ _ _ _ hne] at hb
  split at hb
  · cases hb
  · split at hb
    · cases hb
    · exact hb

/-- **A crash keeping the rename** keeps every earlier entry of the coherent area claim, and, with the
rename undone, is a crash of the claims before it. -/
theorem regionCrashedK_create_keep {cl : List Claim} {n : Nat} {m' : Tree} {K : Nat → Prop}
    {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat} {tmp nm : GoString} {J : Ino}
    {X : List GoString} {hJ : NamesH}
    (hK : RegionCrashedK (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J)
      J X hJ) n m' K) (hx : K x)
    (hc : (jr, N, h) ∈ cl) (hcoh : ClaimCoh h jr N) (hs : h.next ≤ st) (hne : tmp ≠ nm)
    (hnmN : N.Mem nm) (htmpN : N.Mem tmp)
    (hcnm : h.cur !! nm = none) (hctmp : h.cur !! tmp = some (.dir J))
    (hothers : ∀ c' ∈ cl, c' ≠ (jr, N, h) → c'.1 = jr → ¬ c'.2.1.Mem nm ∧ ¬ c'.2.1.Mem tmp) :
    (∀ xe ∈ h.ents, K xe.1) ∧ RegionCrashedK cl n (treeUnren m' jr tmp nm J) K := by
  classical
  generalize he : renDirEnt jr tmp nm J st = e at hK
  generalize hcd : renCur N h tmp nm J = c at hK
  have hc1 := mem_createClaims_area (x := x) (e := e) (c := c) (J := J) (X := X) (hJ := hJ) hc
  have hold : ∀ xe ∈ h.ents, K xe.1 := by
    intro xe hxe
    exact hK.1 _ hc1 _ hc1 x e c xe.1 xe.2.1 xe.2.2 (by simp [NamesH.log])
      (by simp [NamesH.log, hxe]) hx (Nat.lt_of_lt_of_le (hcoh.1 xe hxe) (by rw [← he]; exact hs))
  refine ⟨hold, ?_⟩
  let f : Claim → Claim := fun c' => if c' = (jr, N, h) then (jr, N, h.log x e c) else c'
  have hfm : ∀ c' ∈ cl, f c' ∈ createClaims cl jr N h x e c J X hJ := fun c' hc' =>
    List.mem_append_left _ (mem_replClaim hc')
  have hfe : ∀ c' y, y ∈ c'.2.2.ents → y ∈ (f c').2.2.ents := fun c' y hy => by
    simp only [f]; split
    · rename_i hc'; subst hc'; simp [NamesH.log, hy]
    · exact hy
  obtain ⟨h1, h2, h3⟩ := hK
  refine ⟨fun c1 hc1' c2 hc2 x' e' E y e'' E' hx' hy hKx hlt => ?_, fun c1 hc1' y e' E hy hlt => ?_,
    fun c1 hc1' b hb => ?_⟩
  · exact h1 (f c1) (hfm c1 hc1') (f c2) (hfm c2 hc2) x' e' E y e'' E'
      (hfe c1 _ hx') (hfe c2 _ hy) hKx hlt
  · exact h2 (f c1) (hfm c1 hc1') y e' E (hfe c1 _ hy) hlt
  · have h3' := h3 (f c1) (hfm c1 hc1')
    by_cases hcc : c1 = (jr, N, h)
    · subst hcc
      simp only [f, ite_true] at h3'
      simp only at hb ⊢
      rw [treeUnren_entry _ _ _ _ _ _ _ hne]
      by_cases hbt : b = tmp
      · subst hbt
        simp only [and_self, ite_true]
        rw [hcoh.2 K hold b hb, hctmp]
      · by_cases hbn : b = nm
        · subst hbn
          simp only [hbt, and_false, ite_false, and_self, ite_true]
          rw [hcoh.2 K hold b hb, hcnm]
        · simp only [hbt, hbn, and_false, ite_false]
          rw [h3' b hb]
          refine valAfter_log_notWrites _ _ _ _ _ _ _ (fun hw => ?_)
          rw [← he] at hw
          rcases ((renDirEnt_writes jr J tmp nm st jr b).1 hw).2 with h' | h'
          · exact hbt h'
          · exact hbn h'
    · simp only [f, hcc, ite_false] at h3'
      rw [treeUnren_entry_other hne]
      · exact h3' b hb
      · rintro ⟨hj, hb' | hb'⟩
        · exact (hothers c1 hc1' hcc hj).2 (hb' ▸ hb)
        · exact (hothers c1 hc1' hcc hj).1 (hb' ▸ hb)

/-! ## The other WALs' crash conditions -/

theorem walNameP_false_of_ok {b : GoString} (h : walNameOk b) : walNameP b = false := by
  unfold walNameP
  simp only [decide_eq_false_iff_not]
  intro hs
  apply h.2.2
  exact hs.subset (by decide)

/-- `CrashTo` reads of the crashed tree only the WAL's name in the area and its directory's `.wal`
names. -/
theorem crashTo_congr {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {m1 m2 : Tree}
    {fo : Ino → Option Fs.OsFile} (he : m1.entry lay.jr lay.nm = m2.entry lay.jr lay.nm)
    (hw : walInos (entsOf m1 lay.j) = walInos (entsOf m2 lay.j))
    (h : CrashTo C Mr d lay m1 fo) : CrashTo C Mr d lay m2 fo := by
  rcases h with ⟨h1, h2⟩ | ⟨q, I, h1, h2, h3, rest⟩
  · exact Or.inl ⟨h1, he ▸ h2⟩
  · exact Or.inr ⟨q, I, he ▸ h1, h2, hw ▸ h3, rest⟩

theorem entsOf_entry (m : Tree) (j : Ino) (b : GoString) : entsOf m j !! b = m.entry j b := by
  unfold entsOf Tree.entry
  cases m !! j <;> rfl

theorem walInos_treeUnren (m' : Tree) (jr : Ino) (tmp nm : GoString) (J : Ino) (j : Ino)
    (hne : tmp ≠ nm) (htw : walNameP tmp = false) (hnw : walNameP nm = false) :
    walInos (entsOf (treeUnren m' jr tmp nm J) j) = walInos (entsOf m' j) := by
  apply walInos_congr
  intro b hb
  rw [entsOf_entry, entsOf_entry]
  refine treeUnren_entry_other hne ?_
  rintro ⟨-, rfl | rfl⟩
  · rw [htw] at hb; cases hb
  · rw [hnw] at hb; cases hb

/-- **Another WAL's crash condition after the rename** (its name in the area neither `nm` nor
`tmp`). -/
theorem crashOkW_create_other {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat}
    {tmp nm : GoString} {J : Ino} {X : List GoString} {hJ : NamesH}
    (hok : CrashOkW C Mr d lay cl n) (hjr : lay.jr = jr) (hnm1 : lay.nm ≠ nm) (hnm2 : lay.nm ≠ tmp)
    (hc : (jr, N, h) ∈ cl) (hcoh : ClaimCoh h jr N) (hs : h.next ≤ st) (hne : tmp ≠ nm)
    (hnmN : N.Mem nm) (htmpN : N.Mem tmp)
    (hcnm : h.cur !! nm = none) (hctmp : h.cur !! tmp = some (.dir J))
    (hothers : ∀ c' ∈ cl, c' ≠ (jr, N, h) → c'.1 = jr → ¬ c'.2.1.Mem nm ∧ ¬ c'.2.1.Mem tmp)
    (htw : walNameP tmp = false) (hnw : walNameP nm = false) :
    CrashOkW C Mr d lay
      (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ) n := by
  classical
  obtain ⟨alt, halt, hcr⟩ := hok
  refine ⟨alt, halt, fun m' fo hr hf hn hw => ?_⟩
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  by_cases hx : K x
  · obtain ⟨-, hK'⟩ := regionCrashedK_create_keep hK hx hc hcoh hs hne hnmN htmpN hcnm hctmp
      hothers
    have hwi := walInos_treeUnren m' jr tmp nm J lay.j hne htw hnw
    have hent : ∀ b, b ≠ nm → b ≠ tmp →
        (treeUnren m' jr tmp nm J).entry jr b = m'.entry jr b := fun b h1 h2 =>
      treeUnren_entry_other hne (fun ⟨_, h3⟩ => h3.elim h2 h1)
    rcases hcr (treeUnren m' jr tmp nm J) fo ((regionCrashed_iff _ _ _).2 ⟨K, hK'⟩) hf
      (fun g hg hin => hn g hg (by rw [← hwi]; exact hin)) (by rw [hwi]; exact hw)
      with hct | ⟨lay0, h0, hct⟩
    · left
      exact crashTo_congr (by rw [hjr]; exact hent _ hnm1 hnm2) hwi hct
    · right
      obtain ⟨-, h1, h2, h3, -⟩ := halt lay0 h0
      refine ⟨lay0, h0, crashTo_congr ?_ (by rw [h3]; exact hwi) hct⟩
      rw [h1, h2, hjr]; exact hent _ hnm1 hnm2
  · exact hcr m' fo ((regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_create_drop hK hx⟩) hf hn hw


/-! ## The new WAL's crash condition -/

/-- **The fresh WAL's crash condition**: a crash dropping the rename leaves `nm` absent (as before
it, `hgone`), the WAL unnamed; keeping it, `nm` holds `J`, whose `.wal` names are as now (every
entry of `J`'s coherent claim took effect before the rename's call began), its segment synced. -/
theorem crashOk_create_new {C : WalCodec} {Mr : WalMarshal} {md : List w8} {lay : WalLay}
    {cl : List Claim} {n : Nat} {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat}
    {tmp nm : GoString} {J : Ino} {X : List GoString} {hJ : NamesH}
    (hc : (jr, N, h) ∈ cl) (hnmN : N.Mem nm)
    (hlay : lay.jr = jr ∧ lay.nm = nm ∧ lay.j = J)
    (hJcoh : ClaimCoh hJ J (.except X)) (hJs : hJ.next ≤ st) (hX : ∀ b ∈ X, walNameP b = false)
    (habs : WalAbsD C Mr (walDurFresh md) lay hJ.cur) (hex : TailExact lay)
    (hdur : ∀ g ∈ lay.segs, ∀ y ∈ g.bs, y = durB y.1)
    (htail : lay.wr = (segStream C Mr (walDurFresh md) lay.cuts lay.cuts.length).length)
    (hold0 : ∀ b, lay.wr ≤ b → b < lay.old.length → lay.old.getD b 0 = 0)
    (hz : lay.old.length - lay.wr = 0 ∨ 8 ≤ lay.old.length - lay.wr)
    (hgone : ∀ m', RegionCrashed cl n m' → m'.entry jr nm = none) :
    CrashOk C Mr (walDurFresh md) lay
      (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ) n := by
  classical
  obtain ⟨hljr, hlnm, hlj⟩ := hlay
  intro m' fo hr hf hn _hw
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  by_cases hx : K x
  · have hc1 := mem_createClaims_area (x := x) (e := renDirEnt jr tmp nm J st)
      (c := renCur N h tmp nm J) (J := J) (X := X) (hJ := hJ) hc
    have hcJ := mem_createClaims_J (cl := cl) (jr := jr) (N := N) (h := h) (x := x)
      (e := renDirEnt jr tmp nm J st) (c := renCur N h tmp nm J) (J := J) (X := X) (hJ := hJ)
    have hold : ∀ xe ∈ hJ.ents, K xe.1 := fun xe hxe =>
      hK.1 _ hc1 _ hcJ x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) xe.1 xe.2.1 xe.2.2
        (by simp [NamesH.log]) (by simpa using hxe) hx (Nat.lt_of_lt_of_le (hJcoh.1 xe hxe) hJs)
    refine crashTo_synced C Mr (walDurFresh md) lay hJ.cur m' fo habs hex rfl hdur htail hold0 hz ?_ ?_
      hf hn
    · apply walInos_congr
      intro b hb
      have hbX : (NameSet.except X).Mem b := fun hbX => by rw [hX b hbX] at hb; cases hb
      rw [entsOf_entry, hlj, hK.2.2 _ hcJ b hbX]
      exact hJcoh.2 K hold b hbX
    · right
      rw [hljr, hlnm, hlj, hK.2.2 _ hc1 nm hnmN]
      show NamesH.valAfter (h.log x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J)) jr K nm = _
      rw [valAfter_log_last _ _ _ _ _ _ _ hx ((renDirEnt_writes jr J tmp nm st jr nm).2
        ⟨rfl, Or.inr rfl⟩)]
      unfold renCur
      rw [restrictN_lookup _ _ _ hnmN, GMap.lookup_insert_eq]
  · left
    refine ⟨rfl, ?_⟩
    rw [hljr, hlnm]
    exact hgone m' ((regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_create_drop hK hx⟩)

/-! ## The invariant's pure facts after the rename -/

/-- The static relation reads the directory's entries only through its `.wal` files. -/
theorem walAbsD_congr {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {e1 e2 : Ents}
    (hw : walInos e1 = walInos e2) (h : WalAbsD C Mr d lay e1) : WalAbsD C Mr d lay e2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨hw ▸ h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- **A WAL directory's claim after the rename** (the area claim, if it were one, logged: the rename
writes no `.wal` name). -/
theorem walDirClaim_create {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat} {tmp nm : GoString}
    {J : Ino} {X : List GoString} {hJ : NamesH} {hj : NamesH}
    (hW : WalDirClaim lay.j hj cl) (habs : WalAbsD C Mr d lay hj.cur)
    (hsx : h.next ≤ x) (htw : walNameP tmp = false) (hnw : walNameP nm = false) :
    ∃ hj', WalDirClaim lay.j hj'
        (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ) ∧
      WalAbsD C Mr d lay hj'.cur := by
  classical
  obtain ⟨X', hX', hm, hcoh⟩ := hW
  by_cases hcc : (lay.j, NameSet.except X', hj) = (jr, N, h)
  · simp only [Prod.mk.injEq] at hcc
    obtain ⟨hj1, hj2, rfl⟩ := hcc
    refine ⟨hj.log x (renDirEnt jr tmp nm J st) (renCur N hj tmp nm J), ⟨X', hX', ?_, ?_⟩, ?_⟩
    · rw [hj1, ← hj2]
      exact mem_createClaims_area (hj1 ▸ hj2 ▸ hm)
    · refine claimCoh_log _ _ _ _ _ _ hcoh hsx (fun b hb hw => ?_)
      have hbn : b ≠ nm := fun hb' => hw ((renDirEnt_writes jr J tmp nm st lay.j b).2
        ⟨hj1, Or.inr hb'⟩)
      have hbt : b ≠ tmp := fun hb' => hw ((renDirEnt_writes jr J tmp nm st lay.j b).2
        ⟨hj1, Or.inl hb'⟩)
      unfold renCur
      rw [← hj2, restrictN_lookup _ _ _ hb, GMap.lookup_insert_ne _ _ (Ne.symm hbn),
        GMap.lookup_delete_ne _ (Ne.symm hbt)]
    · refine walAbsD_congr ?_ habs
      apply walInos_congr
      intro b hb
      have hbn : b ≠ nm := fun h' => by rw [h', hnw] at hb; cases hb
      have hbt : b ≠ tmp := fun h' => by rw [h', htw] at hb; cases hb
      show hj.cur !! b = (renCur N hj tmp nm J) !! b
      unfold renCur
      have hbN : N.Mem b := by
        rw [← hj2]; intro hbX; rw [hX' b hbX] at hb; cases hb
      rw [restrictN_lookup _ _ _ hbN, GMap.lookup_insert_ne _ _ (Ne.symm hbn),
        GMap.lookup_delete_ne _ (Ne.symm hbt)]
  · exact ⟨hj, ⟨X', hX', mem_createClaims_other hm hcc, hcoh⟩, habs⟩

/-- The WAL state after the commit: `dir` holds the fresh WAL. -/
def createSt (s : AbsDiskState) (dir : GoString) (md : List w8) : AbsDiskState :=
  { s with wal := <[dir := walDurFresh md]> s.wal }

theorem inArea_ne {r dir dir' nm nm' : GoString} (h : InArea r dir nm) (h' : InArea r dir' nm')
    (hne : dir' ≠ dir) : nm' ≠ nm := by
  rintro rfl; exact hne (h'.2.trans h.2.symm)

theorem not_inArea_tmp {r dir' nm' tmp : GoString} (h' : InArea r dir' nm') (htmp : ¬ walNameOk tmp) :
    nm' ≠ tmp := by
  rintro rfl; exact htmp h'.1

/-- **Strong absence after the commit**: the other WAL-less names keep their entries. -/
theorem absentNone_create {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat}
    {dir nm tmp : GoString} {md : List w8} {N : NameSet} {h : NamesH} {J : Ino} {x st : Nat}
    {X : List GoString} {hJ : NamesH}
    (han : AbsentNone s jr cl n) (hin : InArea s.area dir nm)
    (hc : (jr, N, h) ∈ cl) (hcoh : ClaimCoh h jr N) (hs : h.next ≤ st) (hne : tmp ≠ nm)
    (hnmN : N.Mem nm) (htmpN : N.Mem tmp) (hcnm : h.cur !! nm = none)
    (hctmp : h.cur !! tmp = some (.dir J))
    (hothers : ∀ c' ∈ cl, c' ≠ (jr, N, h) → c'.1 = jr → ¬ c'.2.1.Mem nm ∧ ¬ c'.2.1.Mem tmp)
    (htmp : ¬ walNameOk tmp) (hJjr : J ≠ jr) :
    AbsentNone (createSt s dir md) jr
      (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ) n := by
  classical
  intro dir' nm' hin' hnone
  have hdd : dir' ≠ dir := by
    rintro rfl; simp [createSt, GMap.lookup_insert_eq] at hnone
  have hnone' : s.wal !! dir' = none := by
    unfold createSt at hnone
    rwa [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hnone
  have hin'' : InArea s.area dir' nm' := hin'
  have h1 : nm' ≠ nm := inArea_ne hin hin'' hdd
  have h2 : nm' ≠ tmp := not_inArea_tmp hin'' htmp
  obtain ⟨hcur, hcr⟩ := han dir' nm' hin'' hnone'
  refine ⟨fun N' h' hm hN' => ?_, fun m' hr => ?_⟩
  · rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨c1, hc1, he⟩ := List.mem_map.1 hm
      by_cases hcc : c1 = (jr, N, h)
      · subst hcc
        simp only [ite_true, Prod.mk.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        show renCur N h tmp nm J !! nm' = none
        unfold renCur
        rw [restrictN_lookup _ _ _ hN', GMap.lookup_insert_ne _ _ (Ne.symm h1),
          GMap.lookup_delete_ne _ (Ne.symm h2)]
        exact hcur N h hc hN'
      · simp only [hcc, ite_false] at he
        subst he
        exact hcur N' h' hc1 hN'
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      exact absurd hm.1.symm hJjr
  · obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
    by_cases hx : K x
    · obtain ⟨-, hK'⟩ := regionCrashedK_create_keep hK hx hc hcoh hs hne hnmN htmpN hcnm hctmp
        hothers
      rw [← treeUnren_entry_other (jr := jr) (tmp := tmp) (nm := nm) (J := J) hne
        (fun ⟨_, h3⟩ => h3.elim h2 h1)]
      exact hcr _ ((regionCrashed_iff _ _ _).2 ⟨K, hK'⟩)
    · exact hcr m' ((regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_create_drop hK hx⟩)

/-- Strong absence gives `AbsentOk`. -/
theorem absentOk_of_absentNone {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat}
    (h : AbsentNone s jr cl n) : AbsentOk s jr cl n := by
  intro dir nm hin hnone m' hr J hJ
  rw [(h dir nm hin hnone).2 m' hr] at hJ; cases hJ

/-- **The durable directories after the rename** (they resolve through neither `tmp` nor `nm`). -/
theorem dirsOk_create {R : Roots} {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat}
    {nm tmp : GoString} {N : NameSet} {h : NamesH} {J : Ino} {x st : Nat}
    {X : List GoString} {hJ : NamesH}
    (hdo : DirsOk R s cl n) (hav : DirsAvoid R jr s)
    (hc : (jr, N, h) ∈ cl) (hcoh : ClaimCoh h jr N) (hs : h.next ≤ st) (hne : tmp ≠ nm)
    (hnmN : N.Mem nm) (htmpN : N.Mem tmp) (hcnm : h.cur !! nm = none)
    (hctmp : h.cur !! tmp = some (.dir J))
    (hothers : ∀ c' ∈ cl, c' ≠ (jr, N, h) → c'.1 = jr → ¬ c'.2.1.Mem nm ∧ ¬ c'.2.1.Mem tmp)
    (hnmS : AreaSlot nm) (htmpS : AreaSlot tmp) :
    DirsOk R s
      (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ) n := by
  intro dd hdd m' hr
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  by_cases hx : K x
  · obtain ⟨-, hK'⟩ := regionCrashedK_create_keep hK hx hc hcoh hs hne hnmN htmpN hcnm hctmp
      hothers
    obtain ⟨J', hJ'⟩ := hdo dd hdd _ ((regionCrashed_iff _ _ _).2 ⟨K, hK'⟩)
    refine ⟨J', ?_⟩
    rw [← hav dd hdd (treeUnren m' jr tmp nm J) m' (fun j b hjb => treeUnren_entry_other hne
      (fun ⟨h1, h2⟩ => hjb ⟨h1, h2.elim (fun e => e ▸ htmpS) (fun e => e ▸ hnmS)⟩))]
    exact hJ'
  · exact hdo dd hdd m' ((regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_create_drop hK hx⟩)

/-- `Create`'s framed part after the rename: the area claim keeps its names. -/
theorem walsCreateOk_create {jr : Ino} {cl : List Claim} {N : NameSet} {h : NamesH} {x : Nat}
    {e : LogEntry} {c : Ents} {J : Ino} {X : List GoString} {hJ : NamesH}
    (hw : WalsCreateOk jr cl) : WalsCreateOk jr (createClaims cl jr N h x e c J X hJ) := by
  classical
  intro nm' hnm'
  obtain ⟨N', h', hc, hN⟩ := hw nm' hnm'
  by_cases hcc : (jr, N', h') = (jr, N, h)
  · simp only [Prod.mk.injEq] at hcc
    obtain ⟨-, rfl, rfl⟩ := hcc
    exact ⟨N', h'.log x e c, mem_createClaims_area hc, hN⟩
  · exact ⟨N', h', mem_createClaims_other hc hcc, hN⟩

/-- **The invariant's pure facts after `Create`'s rename** (the commit; see the file header). The
area claim `(jr, N, h)` is coherent and holds `nm` (free: `AbsentNone`) and `tmp` (holding `J`),
which no other claim of `jr` holds; the call began at `st` after its last change; `J`'s claim
`(J, except X, hJ)` is coherent and changed last before `st`, its `.wal` names the new layout's one
segment, all of whose bytes are durable (`hdur`, the stream then zeros: `htail`, `hold0`, `hz`).
The durable directories resolve through neither `tmp` nor `nm` (`hav`, `htmpS`). -/
theorem walsOk_create {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir nm tmp : GoString}
    {md : List w8} {N : NameSet} {h : NamesH} {J : Ino} {x st : Nat} {X : List GoString}
    {hJ : NamesH} {lay : WalLay}
    (hok : WalsOk C Mr R jr s Ls cl n) (han : AbsentNone s jr cl n)
    (hd : s.wal !! dir = none) (hin : InArea s.area dir nm)
    (hc : (jr, N, h) ∈ cl) (hcoh : ClaimCoh h jr N) (hs : h.next ≤ st) (hsx : st ≤ x)
    (hne : tmp ≠ nm) (hnmN : N.Mem nm) (htmpN : N.Mem tmp)
    (hctmp : h.cur !! tmp = some (.dir J))
    (hothers : ∀ c' ∈ cl, c' ≠ (jr, N, h) → c'.1 = jr → ¬ c'.2.1.Mem nm ∧ ¬ c'.2.1.Mem tmp)
    (htmp : ¬ walNameOk tmp) (htw : walNameP tmp = false) (hJjr : J ≠ jr)
    (hlay : lay.jr = jr ∧ lay.nm = nm ∧ lay.j = J)
    (hJcoh : ClaimCoh hJ J (.except X)) (hJs : hJ.next ≤ st) (hX : ∀ b ∈ X, walNameP b = false)
    (habs : WalAbsD C Mr (walDurFresh md) lay hJ.cur) (hex : TailExact lay)
    (hdur : ∀ g ∈ lay.segs, ∀ y ∈ g.bs, y = durB y.1)
    (htail : lay.wr = (segStream C Mr (walDurFresh md) lay.cuts lay.cuts.length).length)
    (hold0 : ∀ b, lay.wr ≤ b → b < lay.old.length → lay.old.getD b 0 = 0)
    (hz : lay.old.length - lay.wr = 0 ∨ 8 ≤ lay.old.length - lay.wr)
    (hnd : (lay.segs.map (·.ino)).Nodup)
    (hdisj : ∀ g ∈ lay.segs, ∀ g' ∈ segsAll Ls, g.ino ≠ g'.ino)
    (hcut : ∀ g ∈ lay.segs, g.om.cut = none)
    (hav : DirsAvoid R jr s) (htmpS : AreaSlot tmp) :
    WalsOk C Mr R jr (createSt s dir md) (<[dir := lay]> Ls)
      (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ) n ∧
    AbsentNone (createSt s dir md) jr
      (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ) n := by
  classical
  have hnw : walNameP nm = false := walNameP_false_of_ok hin.1
  obtain ⟨hcnm, hgone⟩ := han dir nm hin hd
  have hcnm' := hcnm N h hc hnmN
  have han' := absentNone_create (x := x) (X := X) (hJ := hJ) (md := md) han hin hc hcoh hs hne
    hnmN htmpN hcnm' hctmp hothers htmp hJjr
  obtain ⟨h1, h2, h3, h4, -, hdo⟩ := hok
  have hdok := dirsOk_create (x := x) (X := X) (hJ := hJ) hdo hav hc hcoh hs hne hnmN htmpN hcnm'
    hctmp hothers ⟨nm, hin.1, Or.inl rfl⟩ htmpS
  refine ⟨⟨fun dir' d' hd' => ?_, fun dir' hn' => ?_, ?_, ?_, absentOk_of_absentNone han', hdok⟩,
    han'⟩
  · by_cases hdd : dir' = dir
    · subst hdd
      simp only [createSt, GMap.lookup_insert_eq, Option.some.injEq] at hd'
      subst hd'
      refine ⟨lay, nm, hJ, GMap.lookup_insert_eq .., hin, hlay.1, hlay.2.1,
        ⟨X, hX, hlay.2.2 ▸ mem_createClaims_J, hlay.2.2 ▸ hJcoh⟩, habs,
        crashOkW_of_crashOk ?_⟩
      exact crashOk_create_new hc hnmN hlay hJcoh hJs hX habs hex hdur htail hold0 hz hgone
    · simp only [createSt, GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hd'
      obtain ⟨lay', nm', hj', hL', hin', hjr', hnm', hW, habs', hco'⟩ := h1 dir' d' hd'
      obtain ⟨hj'', hW', habs''⟩ := walDirClaim_create (x := x) (st := st) (tmp := tmp) (nm := nm)
        (J := J) (X := X) (hJ := hJ) (jr := jr) (N := N) (h := h) hW habs'
        (Nat.le_trans hs hsx) htw hnw
      refine ⟨lay', nm', hj'', by rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]; exact hL', hin',
        hjr', hnm', hW', habs'', ?_⟩
      exact crashOkW_create_other hco' hjr' (hnm' ▸ inArea_ne hin hin' hdd)
        (hnm' ▸ not_inArea_tmp hin' htmp) hc hcoh hs hne hnmN htmpN hcnm' hctmp hothers htw hnw
  · have hdd : dir' ≠ dir := by
      rintro rfl; simp [createSt, GMap.lookup_insert_eq] at hn'
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]
    unfold createSt at hn'
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hn'
    exact h2 dir' hn'
  · obtain ⟨n1, n2⟩ := (segsAll_nodup_iff Ls).1 h3
    refine (segsAll_nodup_iff _).2 ⟨fun dir' lay' hl => ?_, fun d1 d2 l1 l2 hne' hl1 hl2 => ?_⟩
    · by_cases hdd : dir' = dir
      · subst hdd; rw [GMap.lookup_insert_eq] at hl; cases hl; exact hnd
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl; exact n1 dir' lay' hl
    · by_cases e1 : d1 = dir
      · subst e1
        rw [GMap.lookup_insert_eq] at hl1; cases hl1
        rw [GMap.lookup_insert_ne _ _ hne'] at hl2
        exact fun g hg g' hg' => hdisj g hg g' (mem_segsAll hl2 hg')
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e1)] at hl1
        by_cases e2 : d2 = dir
        · subst e2
          rw [GMap.lookup_insert_eq] at hl2; cases hl2
          exact fun g hg g' hg' => (hdisj g' hg' g (mem_segsAll hl1 hg)).symm
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e2)] at hl2
          exact n2 d1 d2 l1 l2 hne' hl1 hl2
  · intro g hg
    obtain ⟨dir', lay', hl, hg'⟩ := segsAll_mem hg
    by_cases hdd : dir' = dir
    · subst hdd; rw [GMap.lookup_insert_eq] at hl; cases hl; exact hcut g hg'
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl; exact h4 g (mem_segsAll hl hg')

end pure

end WalFs
end EtcdGrove
end Perennial

end
