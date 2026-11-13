/- Lean-first (no Rocq counterpart).

# `Create`'s commit and the invariant's later conjuncts (W1 log, seventh session, task 3)

The facts `walCreate_osAUnc`'s commit (`CreateAu.lean`) needs beyond `walsOk_create`
(`CreateCommit.lean`): the directory keys (`dirKeysOk_create`: the new WAL keyed at `(J, X)`, the other
keys' claims kept, every WAL without an alternative layout, `crashOkA_none_create_other`), the segments at
their names (`walsNamed_create`) and the parked halves (`walParked_create`: the new segment and `J`'s claim
out, the area claim no WAL directory's). They rest on the creating entry's `CreatingNew`: no claim of `J`
among the invariant's holds a `.wal` name, and the area claim leaves one out.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailAcc
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAuLemmas

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- A file named in a directory's `.wal` names. -/
theorem walInos_mem {E : Ents} {i : Ino} (h : i ∈ walInos E) :
    ∃ b, walNameP b = true ∧ E !! b = some (.file i) := by
  unfold walInos at h
  obtain ⟨b, hb, hm⟩ := List.mem_filterMap.1 h
  have hb' : b ∈ ((GMap.toList E).map (·.1)).filter walNameP := List.mem_mergeSort.1 hb
  refine ⟨b, of_decide_eq_true (by simpa using (List.mem_filter.1 hb').2), ?_⟩
  split at hm
  · rename_i i' heq
    cases hm; exact heq
  · cases hm

/-- `SegsNamedC` reads the directory only at `.wal` names. -/
theorem segsNamedC_congr_ents {segs : List SegG} {E1 E2 : Ents}
    (h : ∀ b, walNameP b = true → E1 !! b = E2 !! b) (hs : SegsNamedC segs E1) :
    SegsNamedC segs E2 := by
  refine ⟨fun g hg => ?_, fun b e hb he => hs.2.1 b e hb (by rw [h b hb]; exact he),
    fun i hi => hs.2.2 i (by rw [walInos_congr h]; exact hi)⟩
  obtain ⟨hw, hin⟩ := hs.1 g hg
  refine ⟨hw, fun hi => ?_⟩
  rw [← h _ hw]
  exact hin (by rw [walInos_congr h]; exact hi)

theorem claimOnce_mem {c : Claim} {cl : List Claim} (h : ClaimOnce c cl) : c ∈ cl := by
  obtain ⟨l1, l2, hcl, -, -⟩ := h; rw [hcl]; simp

/-- The claims after the commit: `J`'s, the area claim logged, or another of the claims before. -/
theorem mem_createClaims_cases {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {x : Nat}
    {e : LogEntry} {cc : Ents} {J : Ino} {X : List GoString} {hJ : NamesH} {c' : Claim}
    (hc' : c' ∈ createClaims cl jr N h x e cc J X hJ) :
    c' = (J, NameSet.except X, hJ) ∨ c' = (jr, N, h.log x e cc) ∨ (c' ∈ cl ∧ c' ≠ (jr, N, h)) := by
  classical
  unfold createClaims replClaim at hc'
  rcases List.mem_append.1 hc' with hc' | hc'
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc'
    by_cases h0 : c0 = (jr, N, h)
    · right; left; simp [h0]
    · right; right; simp only [if_neg h0]; exact ⟨hc0, h0⟩
  · left; simpa using hc'

/-- **Another WAL's crash condition after the rename, with no alternative** (as
`crashOkW_create_other`). -/
theorem crashOkA_none_create_other {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} {jr : Ino} {N : NameSet} {h : NamesH} {x st : Nat}
    {tmp nm : GoString} {J : Ino} {X : List GoString} {hJ : NamesH}
    (hok : CrashOkA C Mr d lay none cl n) (hjr : lay.jr = jr) (hnm1 : lay.nm ≠ nm)
    (hnm2 : lay.nm ≠ tmp)
    (hc : (jr, N, h) ∈ cl) (hcoh : ClaimCoh h jr N) (hs : h.next ≤ st) (hne : tmp ≠ nm)
    (hnmN : N.Mem nm) (htmpN : N.Mem tmp)
    (hcnm : h.cur !! nm = none) (hctmp : h.cur !! tmp = some (.dir J))
    (hothers : ∀ c' ∈ cl, c' ≠ (jr, N, h) → c'.1 = jr → ¬ c'.2.1.Mem nm ∧ ¬ c'.2.1.Mem tmp)
    (htw : walNameP tmp = false) (hnw : walNameP nm = false) :
    CrashOkA C Mr d lay none
      (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ) n := by
  classical
  intro m' fo hr hf hn hw
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  by_cases hx : K x
  · obtain ⟨-, hK'⟩ := regionCrashedK_create_keep hK hx hc hcoh hs hne hnmN htmpN hcnm hctmp
      hothers
    have hwi := walInos_treeUnren m' jr tmp nm J lay.j hne htw hnw
    have hent : ∀ b, b ≠ nm → b ≠ tmp →
        (treeUnren m' jr tmp nm J).entry jr b = m'.entry jr b := fun b h1 h2 =>
      treeUnren_entry_other hne (fun ⟨_, h3⟩ => h3.elim h2 h1)
    rcases hok (treeUnren m' jr tmp nm J) fo ((regionCrashed_iff _ _ _).2 ⟨K, hK'⟩) hf
      (fun g hg hin => hn g hg (by rw [← hwi]; exact hin)) (by rw [hwi]; exact hw)
      with hct | ⟨lay0, h0, -⟩
    · left
      exact crashTo_congr (by rw [hjr]; exact hent _ hnm1 hnm2) hwi hct
    · cases h0
  · exact hok m' fo ((regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_create_drop hK hx⟩) hf hn hw

/-- **The directory keys after the commit**: the new WAL keyed `(J, X)` (its claim appended once,
the only claim of `J` holding a `.wal` name: `CreatingNew`), the other keys as before (their
directories neither `jr` nor `J`), every WAL without an alternative layout but the pending cut's. -/
theorem dirKeysOk_create {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {c : Option GoString}
    {CR : GMap GoString (NameSet × NamesH × Ino)} {dir nm tmp : GoString}
    {md : List w8} {N : NameSet} {h : NamesH} {J : Ino} {x st : Nat} {X : List GoString}
    {hJ : NamesH} {lay : WalLay}
    (hok : WalsOk C Mr R jr s Ls cl n) (han : AbsentNone s jr cl n)
    (hk : DirKeysOk C Mr jr s Ls cl n K c) (hnew : CreatingNew jr cl CR dir N J)
    (hd : s.wal !! dir = none) (hin : InArea s.area dir nm)
    (hc : (jr, N, h) ∈ cl) (hcoh : ClaimCoh h jr N) (hs : h.next ≤ st)
    (hne : tmp ≠ nm) (hnmN : N.Mem nm) (htmpN : N.Mem tmp)
    (hctmp : h.cur !! tmp = some (.dir J))
    (hothers : ∀ c' ∈ cl, c' ≠ (jr, N, h) → c'.1 = jr → ¬ c'.2.1.Mem nm ∧ ¬ c'.2.1.Mem tmp)
    (htmp : ¬ walNameOk tmp) (htw : walNameP tmp = false)
    (hlay : lay.jr = jr ∧ lay.nm = nm ∧ lay.j = J)
    (hJcoh : ClaimCoh hJ J (.except X)) (hJs : hJ.next ≤ st) (hX : ∀ b ∈ X, walNameP b = false)
    (habs : WalAbsD C Mr (walDurFresh md) lay hJ.cur)
    (hdur : ∀ g ∈ lay.segs, ∀ y ∈ g.bs, y = durB y.1)
    (htail : lay.wr = (segStream C Mr (walDurFresh md) lay.cuts lay.cuts.length).length)
    (hold0 : ∀ b, lay.wr ≤ b → b < lay.old.length → lay.old.getD b 0 = 0)
    (hz : lay.old.length - lay.wr = 0 ∨ 8 ≤ lay.old.length - lay.wr) :
    DirKeysOk C Mr jr (createSt s dir md) (<[dir := lay]> Ls)
      (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ) n
      (<[dir := (J, X)]> K) c := by
  classical
  obtain ⟨hJjr, hJc, -, b0, hb0, -⟩ := hnew
  have hnw : walNameP nm = false := walNameP_false_of_ok hin.1
  obtain ⟨hcnm, hgone⟩ := han dir nm hin hd
  have hcnm' := hcnm N h hc hnmN
  have hexc : ∀ X' : List GoString, (∀ b ∈ X', walNameP b = false) → (NameSet.except X').Mem b0 :=
    fun X' hX' hb => by rw [hX' b0 hb] at hb0; cases hb0
  refine ⟨fun dir' j X' hk' => ?_, fun dir' d' lay' hd' hl' hcd => ?_⟩
  · by_cases hdd : dir' = dir
    · subst hdd
      rw [GMap.lookup_insert_eq] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq] at hk'
      obtain ⟨rfl, rfl⟩ := hk'
      refine ⟨lay, hJ, GMap.lookup_insert_eq .., hlay.2.2, hJjr, hX, ?_, hJcoh, ?_⟩
      · refine ⟨replClaim (jr, N, h) (jr, N, h.log x (renDirEnt jr tmp nm J st)
          (renCur N h tmp nm J)) cl, [], rfl, ?_, by simp⟩
        intro hm
        rcases mem_createClaims_cases (List.mem_append_left [(J, NameSet.except X, hJ)] hm) with
          he | he | ⟨hm', -⟩
        · -- the appended claim is not in the replaced list
          unfold replClaim at hm
          obtain ⟨c0, hc0, hfc⟩ := List.mem_map.1 hm
          by_cases h0 : c0 = (jr, N, h)
          · simp only [if_pos h0, Prod.mk.injEq] at hfc; exact hJjr hfc.1.symm
          · simp only [if_neg h0] at hfc
            subst hfc
            exact hJc _ hc0 rfl b0 hb0 (hexc X hX)
        · simp only [Prod.mk.injEq] at he; exact hJjr he.1
        · exact hJc _ hm' rfl b0 hb0 (hexc X hX)
      · intro c' hc' hne' hcj b hb
        rcases mem_createClaims_cases hc' with he | he | ⟨hm', -⟩
        · exact (hne' he).elim
        · rw [he] at hcj; exact (hJjr hcj.symm).elim
        · exact hJc c' hm' hcj b hb
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hk'
      obtain ⟨lay1, hj, hl1, hlj, hjjr, hX', honce, hcoh', hex⟩ := hk.1 dir' j X' hk'
      have hjJ : j ≠ J := fun e => hJc _ (claimOnce_mem honce) e b0 hb0 (hexc X' hX')
      refine ⟨lay1, hj, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]; exact hl1, hlj, hjjr, hX',
        claimOnce_createClaims honce (fun e => hjjr (by simp only [Prod.mk.injEq] at e; exact e.1))
          (fun e => hjjr (by simp only [Prod.mk.injEq] at e; exact e.1)) hjJ, hcoh', ?_⟩
      intro c' hc' hne' hcj b hb
      rcases mem_createClaims_cases hc' with he | he | ⟨hm', -⟩
      · rw [he] at hcj; exact (hjJ hcj.symm).elim
      · rw [he] at hcj; exact (hjjr hcj.symm).elim
      · exact hex c' hm' hne' hcj b hb
  · by_cases hdd : dir' = dir
    · subst hdd
      simp only [createSt, GMap.lookup_insert_eq, Option.some.injEq] at hd'
      rw [GMap.lookup_insert_eq] at hl'
      simp only [Option.some.injEq] at hl'
      subst hd' hl'
      exact (crashOkA_none_iff _ _ _ _ _ _).2
        (crashOk_create_new hc hnmN hlay hJcoh hJs hX habs hdur htail hold0 hz hgone)
    · simp only [createSt, GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hd'
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl'
      obtain ⟨lay1, nm', hj', hL', hin', hjr', hnm', -, -, -⟩ := hok.1 dir' d' hd'
      rw [hl'] at hL'
      simp only [Option.some.injEq] at hL'
      subst hL'
      exact crashOkA_none_create_other (hk.2 dir' d' lay' hd' hl' hcd) hjr'
        (hnm' ▸ inArea_ne hin hin' hdd) (hnm' ▸ not_inArea_tmp hin' htmp) hc hcoh hs hne hnmN
        htmpN hcnm' hctmp hothers htw hnw

/-- **The segments at their names after the commit**: the new WAL's (its directory's claim the
appended one: `hsn` now, `hJC` after a crash, of every crash of `J`'s claim), the others' as
before (their directories not `J`; a crash keeping the rename is one of the claims before on the
`.wal` names, `treeUnren`). -/
theorem walsNamed_create {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {CR : GMap GoString (NameSet × NamesH × Ino)} {dir nm tmp : GoString}
    {N : NameSet} {h : NamesH} {J : Ino} {x st : Nat} {X : List GoString}
    {hJ : NamesH} {lay : WalLay}
    (hok : WalsOk C Mr R jr s Ls cl n) (hW : WalsNamed Ls cl n) (hnew : CreatingNew jr cl CR dir N J)
    (hc : (jr, N, h) ∈ cl) (hcoh : ClaimCoh h jr N) (hs : h.next ≤ st)
    (hne : tmp ≠ nm) (hnmN : N.Mem nm) (htmpN : N.Mem tmp)
    (hcnm : h.cur !! nm = none) (hctmp : h.cur !! tmp = some (.dir J))
    (hothers : ∀ c' ∈ cl, c' ≠ (jr, N, h) → c'.1 = jr → ¬ c'.2.1.Mem nm ∧ ¬ c'.2.1.Mem tmp)
    (htw : walNameP tmp = false) (hnw : walNameP nm = false)
    (hlj : lay.j = J) (hX : ∀ b ∈ X, walNameP b = false)
    (hsn : SegsNamed lay.segs hJ.cur)
    (hJC : ∀ (K : Nat → Prop) (E : Ents), (∀ b, walNameP b = true → E !! b = hJ.valAfter J K b) →
      SegsNamedC lay.segs E) :
    WalsNamed (<[dir := lay]> Ls)
      (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ) n := by
  classical
  obtain ⟨hJjr, hJc, -, b0, hb0, hNb0⟩ := hnew
  have hexc : ∀ X' : List GoString, (∀ b ∈ X', walNameP b = false) → (NameSet.except X').Mem b0 :=
    fun X' hX' hb => by rw [hX' b0 hb] at hb0; cases hb0
  intro dir' lay' hl'
  by_cases hdd : dir' = dir
  · subst hdd
    rw [GMap.lookup_insert_eq] at hl'
    simp only [Option.some.injEq] at hl'
    subst hl'
    refine ⟨fun hj' hWc => ?_, fun m' hr => ?_⟩
    · obtain ⟨X', hX', hm, -⟩ := hWc
      rcases mem_createClaims_cases hm with he | he | ⟨hm', -⟩
      · simp only [Prod.mk.injEq] at he; rw [he.2.2]; exact hsn
      · simp only [Prod.mk.injEq] at he; exact absurd (hlj.symm.trans he.1) hJjr
      · exact absurd (hexc X' hX') (hJc _ hm' (by rw [hlj]) b0 hb0)
    · obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
      refine hJC K _ (fun b hb => ?_)
      have hbX : (NameSet.except X).Mem b := fun hbX => by rw [hX b hbX] at hb; cases hb
      rw [entsOf_entry, hlj]
      exact hK.2.2 _ mem_createClaims_J b hbX
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl'
    -- the other WAL's directory is not `J`
    have hd' : ∃ d', s.wal !! dir' = some d' := by
      cases e : s.wal !! dir' with
      | none => rw [hok.2.1 dir' e] at hl'; cases hl'
      | some d' => exact ⟨d', rfl⟩
    obtain ⟨d', hd'⟩ := hd'
    obtain ⟨lay1, -, hj0, hl1, -, -, -, ⟨X0, hX0, hm0, -⟩, -, -⟩ := hok.1 dir' d' hd'
    rw [hl'] at hl1; simp only [Option.some.injEq] at hl1; subst hl1
    have hjJ : lay'.j ≠ J := fun e => hJc _ hm0 e b0 hb0 (hexc X0 hX0)
    obtain ⟨h1, h2⟩ := hW dir' lay' hl'
    refine ⟨fun hj' hWc => ?_, fun m' hr => ?_⟩
    · obtain ⟨X', hX', hm, hcoh'⟩ := hWc
      rcases mem_createClaims_cases hm with he | he | ⟨hm', -⟩
      · simp only [Prod.mk.injEq] at he; exact absurd he.1 hjJ
      · simp only [Prod.mk.injEq] at he
        exact absurd (he.2.1 ▸ hexc X' hX') hNb0
      · exact h1 hj' ⟨X', hX', hm', hcoh'⟩
    · obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
      by_cases hx : K x
      · obtain ⟨-, hK'⟩ := regionCrashedK_create_keep hK hx hc hcoh hs hne hnmN htmpN hcnm hctmp
          hothers
        refine segsNamedC_congr_ents (fun b hb => ?_) (h2 _ ((regionCrashed_iff _ _ _).2 ⟨K, hK'⟩))
        rw [entsOf_entry, entsOf_entry]
        refine treeUnren_entry_other hne ?_
        rintro ⟨-, rfl | rfl⟩
        · rw [htw] at hb; cases hb
        · rw [hnw] at hb; cases hb
      · exact h2 m' ((regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_create_drop hK hx⟩)

/-- **A claim parked after the commit iff before** (`walParked_create`): `J`'s new claim is out (in
`D`); the area claim, before and after, is no WAL directory's (it leaves out a `.wal` name); the
others are the same claims of the same directories, none `J`'s (`CreatingNew`). -/
theorem parkedClaim_create {Ls : GMap GoString WalLay} {cl : List Claim} {D : List Claim}
    {CR : GMap GoString (NameSet × NamesH × Ino)} {jr : Ino} {dir : GoString} {N : NameSet}
    {J : Ino} {X : List GoString} {hJ : NamesH} {lay : WalLay} {c : Claim}
    (hnew : CreatingNew jr cl CR dir N J) (hlj : lay.j = J) (hLd : Ls !! dir = none)
    (hX : ∀ b ∈ X, walNameP b = false) (hc : c ∈ cl) :
    ParkedClaim (<[dir := lay]> Ls) ((J, NameSet.except X, hJ) :: D) c ↔ ParkedClaim Ls D c := by
  classical
  obtain ⟨-, hJc, -, b0, hb0, -⟩ := hnew
  have hcJ : c.1 = J → ∀ X' : List GoString, (∀ b ∈ X', walNameP b = false) →
      c.2.1 ≠ .except X' := fun e X' hX' hN => by
    refine hJc c hc e b0 hb0 ?_
    rw [hN]; intro hb; rw [hX' b0 hb] at hb0; cases hb0
  unfold ParkedClaim WalDirClaimOf
  constructor
  · rintro ⟨⟨dir', lay', hl', hj, X', hN, hX'⟩, hD⟩
    by_cases hdd : dir' = dir
    · subst hdd
      rw [GMap.lookup_insert_eq] at hl'
      simp only [Option.some.injEq] at hl'
      subst hl'
      exact absurd hN (hcJ (hj.trans hlj) X' hX')
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl'
      exact ⟨⟨dir', lay', hl', hj, X', hN, hX'⟩, fun hm => hD (List.mem_cons_of_mem _ hm)⟩
  · rintro ⟨⟨dir', lay', hl', hj, X', hN, hX'⟩, hD⟩
    have hdd : dir' ≠ dir := by rintro rfl; rw [hLd] at hl'; cases hl'
    refine ⟨⟨dir', lay', by rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]; exact hl', hj, X', hN, hX'⟩,
      fun hm => ?_⟩
    rcases List.mem_cons.1 hm with he | hm
    · subst he; exact (hcJ rfl X hX rfl).elim
    · exact hD hm

/-- **`WalsAt` after `Create`'s commit** (W3/W5's gap 1): the rename puts the new WAL's directory `J`
at its name `nm` in the area claim; the other WALs' names (neither `nm` nor `tmp`: other directories
of the area, `InArea`) keep their entries; the other area claims hold neither name; `J`'s new claim
is not the area's. -/
theorem walsAt_create {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {CR : GMap GoString (NameSet × NamesH × Ino)} {dir nm tmp : GoString}
    {N : NameSet} {h : NamesH} {J : Ino} {x st : Nat} {X : List GoString}
    {hJ : NamesH} {lay : WalLay}
    (hA : WalsAt jr Ls cl) (hok : WalsOk C Mr R jr s Ls cl n) (hnew : CreatingNew jr cl CR dir N J)
    (hin : InArea s.area dir nm) (htmp : ¬ walNameOk tmp) (hc : (jr, N, h) ∈ cl)
    (hothers : ∀ c' ∈ cl, c' ≠ (jr, N, h) → c'.1 = jr → ¬ c'.2.1.Mem nm ∧ ¬ c'.2.1.Mem tmp)
    (hlay : lay.jr = jr ∧ lay.nm = nm ∧ lay.j = J) :
    WalsAt jr (<[dir := lay]> Ls)
      (createClaims cl jr N h x (renDirEnt jr tmp nm J st) (renCur N h tmp nm J) J X hJ) := by
  classical
  have hJjr := hnew.1
  -- another WAL's name is neither `nm` nor `tmp`
  have hnms : ∀ dir' lay', dir' ≠ dir → Ls !! dir' = some lay' → lay'.nm ≠ nm ∧ lay'.nm ≠ tmp := by
    intro dir' lay' hdd hl'
    obtain ⟨d', hd'⟩ : ∃ d', s.wal !! dir' = some d' := by
      cases hw : s.wal !! dir' with
      | none => rw [hok.2.1 dir' hw] at hl'; cases hl'
      | some d' => exact ⟨d', rfl⟩
    obtain ⟨lay'', nm', -, hl'', hin', -, hnm', -⟩ := hok.1 dir' d' hd'
    rw [hl'] at hl''; cases hl''
    rw [hnm']
    exact ⟨inArea_ne hin hin' hdd, not_inArea_tmp hin' htmp⟩
  intro dir' lay' hl'
  refine ⟨?_, fun N' h' hm hN' => ?_⟩
  · by_cases hdd : dir' = dir
    · subst hdd
      rw [GMap.lookup_insert_eq] at hl'
      cases hl'
      rw [hlay.2.2]; exact hJjr
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl'
      exact hA.ne hl'
  rcases mem_createClaims_cases hm with he | he | ⟨hm', hne⟩
  · simp only [Prod.mk.injEq] at he; exact absurd he.1 (Ne.symm hJjr)
  · cases he
    simp only [NamesH.log]
    unfold renCur
    rw [restrictN_lookup _ _ _ hN']
    by_cases hdd : dir' = dir
    · subst hdd
      rw [GMap.lookup_insert_eq] at hl'
      cases hl'
      rw [hlay.2.1, GMap.lookup_insert_eq, hlay.2.2]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl'
      obtain ⟨h1, h2⟩ := hnms dir' lay' hdd hl'
      rw [GMap.lookup_insert_ne _ _ (Ne.symm h1), GMap.lookup_delete_ne _ (Ne.symm h2)]
      exact hA.at hl' hc hN'
  · by_cases hdd : dir' = dir
    · subst hdd
      rw [GMap.lookup_insert_eq] at hl'
      cases hl'
      rw [hlay.2.1] at hN'
      exact absurd hN' (hothers _ hm' hne rfl).1
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl'
      exact hA.at hl' hm' hN'

/-- **`WalsAt` after a cut's commit** (W3/W5's gap 1): the WAL directory's claim replaced by
another of the same directory (not the area's), the layout by one of the same name and directory. -/
theorem walsAt_repl {jr : Ino} {Ls : GMap GoString WalLay} {cl : List Claim} {dir : GoString}
    {lay lay' : WalLay} {c0 c1 : Claim} (hA : WalsAt jr Ls cl) (hl : Ls !! dir = some lay)
    (hnm : lay'.nm = lay.nm) (hj : lay'.j = lay.j) (hc1 : c1.1 ≠ jr) :
    WalsAt jr (<[dir := lay']> Ls) (replClaim c0 c1 cl) := by
  classical
  refine walsAt_congr (fun dir' l hl' => ?_) (fun N' h' hm => ?_) hA
  · by_cases hd : dir' = dir
    · subst hd
      rw [GMap.lookup_insert_eq] at hl'
      cases hl'
      exact ⟨lay, hl, hnm.symm, hj.symm⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)] at hl'
      exact ⟨l, hl', rfl, rfl⟩
  · unfold replClaim at hm
    obtain ⟨c, hc, he⟩ := List.mem_map.1 hm
    by_cases h0 : c = c0
    · rw [if_pos h0] at he; rw [he] at hc1; exact absurd rfl hc1
    · rw [if_neg h0] at he; rw [← he]; exact hc

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The parked halves after the commit** (the lock token's flag `false`): the new segment's
inode and `J`'s claim out (`O`, `D`), the rest as before. -/
theorem walParked_create (Ls : GMap GoString WalLay) (cl : List Claim)
    (CR : GMap GoString (NameSet × NamesH × Ino)) (jr : Ino) (dir : GoString) (N : NameSet)
    (h : NamesH) (h' : NamesH) (J : Ino) (X : List GoString) (hJ : NamesH) (lay : WalLay) (g : SegG)
    (hnew : CreatingNew jr cl CR dir N J) (hlj : lay.j = J) (hLd : Ls !! dir = none)
    (hX : ∀ b ∈ X, walNameP b = false) (hsegs : lay.segs = [g]) (hino : ∀ g' ∈ segsAll Ls, g'.ino ≠ g.ino) :
    ⊢ walParked (L := L) (W := W) Ls cl -∗ walParkFrag (W := W) false -∗
      walParked (L := L) (W := W) (<[dir := lay]> Ls)
        (replClaim (jr, N, h) (jr, N, h') cl ++ [(J, NameSet.except X, hJ)]) ∗
      walParkFrag (W := W) false := by
  classical
  have ⟨_, _, _, b0, hb0, hNb0⟩ := hnew
  unfold walParked
  iintro ⟨%b, %O, %D, Ha, %hb, Hs, Hc, Ht⟩ Hf
  icases walPark_agree (W := W) b false $$ Ha Hf with %hbf
  subst hbf
  iframe Hf
  iexists false, g.ino :: O, (J, NameSet.except X, hJ) :: D
  iframe Ha
  isplitr
  · ipureintro; intro h; cases h
  isplitl [Hs]
  · iapply (segsAll_sep_map (fun x => iprop(if x.ino ∈ g.ino :: O then emp else segResP (L := L) x))
      _).2
    iapply (BigSepM.bigSepM_insert (Φ := fun (_ : GoString) (lay : WalLay) =>
      iprop([∗list] x ∈ lay.segs, if x.ino ∈ g.ino :: O then emp else segResP (L := L) x)) hLd).2
    isplitr
    · rw [hsegs]
      iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)
        (Φ := fun _ x => iprop(if x.ino ∈ g.ino :: O then emp else segResP (L := L) x))).2
      rw [if_pos (List.mem_cons_self ..)]
      iempintro
    ihave Hs := (segsAll_sep_map (fun x => iprop(if x.ino ∈ O then emp else segResP (L := L) x))
      Ls).1 $$ Hs
    iapply BigSepM.bigSepM_mono (fun {k lay'} hl => ?_) $$ Hs
    iapply BigSepL.bigSepL_mono (fun {i x} hx => ?_)
    have hx' : x.ino ≠ g.ino := hino x (mem_segsAll hl (List.mem_of_getElem? hx))
    have e : (x.ino ∈ g.ino :: O) ↔ x.ino ∈ O := by
      simp only [List.mem_cons, hx', false_or]
    simp only [propext e]
    exact .rfl
  isplitl [Hc]
  · iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
    isplitl [Hc]
    · unfold replClaim
      rw [BigSepL.bigSepL_map]
      iapply BigSepL.bigSepL_mono (fun {i c} hci => ?_) $$ Hc
      have hcm : c ∈ cl := List.mem_of_getElem? hci
      by_cases h0 : c = (jr, N, h)
      · -- the area claim: no WAL directory's, before or after
        have hn : ∀ N' : NameSet, N' = N → ∀ (Ls' : GMap GoString WalLay) (D' : List Claim)
            (h'' : NamesH), ¬ ParkedClaim Ls' D' (jr, N', h'') := by
          rintro N' rfl Ls' D' h'' ⟨⟨-, -, -, -, X', hN, hX'⟩, -⟩
          apply hNb0
          change (jr, N', h'').2.1.Mem b0
          rw [hN]; intro hb; rw [hX' b0 hb] at hb0; cases hb0
        rw [if_pos h0, if_neg (hn N rfl _ _ h'), h0, if_neg (hn N rfl _ _ h)]
      · rw [if_neg h0]
        have e := parkedClaim_create (X := X) (hJ := hJ) (D := D) hnew hlj hLd hX hcm (Ls := Ls)
          (lay := lay)
        simp only [propext e]
        exact .rfl
    · iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)
        (Φ := fun _ c => iprop(if ParkedClaim (<[dir := lay]> Ls) ((J, NameSet.except X, hJ) :: D) c then
          osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp))).2
      rw [if_neg (fun hp => hp.2 (List.mem_cons_self ..))]
      iempintro
  · iapply walTmpParked_create Ls dir lay $$ Ht

end iris

end WalFs
end EtcdGrove
end Perennial

end
