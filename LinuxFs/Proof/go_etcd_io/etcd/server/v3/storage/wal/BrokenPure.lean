/- Lean-first (no Rocq counterpart).

# A WAL directory's claim logged at a non-`.wal` name (`wal.Repair`'s `.broken` file, law L3;
`notes/wal-fsext-plan.md`, W7-W12 log, eighth and ninth sessions)

`Repair` creates `<segment>.wal.broken` in the WAL directory `j` (`createNewWALFile(…, true)`, an
`O_CREAT|O_TRUNC` open). The name is in the invariant's claim `(j, .except X, hj)` (not one of `X`,
the pipeline's names), so the create joins the program's half of that claim with the invariant's at
the open's atomic update, and the claim's history gets the create: `hj.log x e c`, `e` writing only
the free name `bt` (`walNameP bt = false`), `c` agreeing with `hj.cur` on every `.wal` name. The WAL
state, the layouts, the keys and the pending cut are unchanged.

Every pure conjunct of `walInvBody` is kept (`brokenHist_pure`): the layouts' relations read only
`.wal` entries (`walInos`, `SegsNamed`), the crash conditions only the `.wal` entries of the WAL
directories and the area's entries (`j` is not the area directory), and a crash of the new claims is
one of the old on the tree itself (the create dropped) or without `(j, bt)` (kept,
`regionCrashed_cut`), which agree with it on all of that (`TreeNearW`). Like the cut's
(`CutCommit.lean`), it needs that no other claim of `j` holds `bt` (`hothers`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCommit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSynced

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

/-- Two trees agreeing on every entry but the non-`.wal` names of the directory `j`. -/
def TreeNearW (j : Ino) (m1 m2 : Tree) : Prop :=
  ∀ j' b, (j' = j → walNameP b = true) → m1.entry j' b = m2.entry j' b

theorem treeNearW_refl (j : Ino) (m : Tree) : TreeNearW j m m := fun _ _ _ => rfl

theorem treeNearW_treeDel {j : Ino} {bt : GoString} (hbt : walNameP bt = false) (m : Tree) :
    TreeNearW j (treeDel m j bt) m := by
  intro j' b hb
  rw [treeDel_entry]
  split
  · rename_i h
    obtain ⟨rfl, rfl⟩ := h
    rw [hb rfl] at hbt; cases hbt
  · rfl

/-- The `.wal` inodes of a directory, in two such trees. -/
theorem TreeNearW.walInos {j : Ino} {m1 m2 : Tree} (h : TreeNearW j m1 m2) (J : Ino) :
    walInos (entsOf m1 J) = walInos (entsOf m2 J) :=
  walInos_congr (fun b hb => by rw [entsOf_entry, entsOf_entry]; exact h J b (fun _ => hb))

theorem TreeNearW.ents_wal {j : Ino} {m1 m2 : Tree} (h : TreeNearW j m1 m2) (J : Ino) (b : GoString)
    (hb : walNameP b = true) : entsOf m1 J !! b = entsOf m2 J !! b := by
  rw [entsOf_entry, entsOf_entry]; exact h J b (fun _ => hb)

theorem TreeNearW.ents_ne {j : Ino} {m1 m2 : Tree} (h : TreeNearW j m1 m2) {J : Ino} (hJ : J ≠ j) :
    entsOf m1 J = entsOf m2 J := by
  apply GMap.ext; intro b
  rw [entsOf_entry, entsOf_entry]; exact h J b (fun e => absurd e hJ)

/-- **A crash of the claims after the create** (the entry `e` logged at `x` in the coherent claim
`(j, N, h)`, writing among its names only the free non-`.wal` name `bt`, which no other claim of `j`
holds): one of the claims before, on a tree agreeing with it but at `j`'s non-`.wal` names. -/
theorem regionCrashed_nonwal {cl : List Claim} {n : Nat} {m' : Tree} {j : Ino} {N : NameSet}
    {h : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hr : RegionCrashed (replClaim (j, N, h) (j, N, h.log x e c) cl) n m')
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt) (hcur : h.cur !! bt = none)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt)
    (hbtw : walNameP bt = false) :
    ∃ m'', RegionCrashed cl n m'' ∧ TreeNearW j m'' m' := by
  rcases regionCrashed_cut hr hcl hcoh hs hbt hcur hothers with hr' | hr'
  · exact ⟨_, hr', treeNearW_treeDel hbtw m'⟩
  · exact ⟨m', hr', treeNearW_refl j m'⟩

/-- The hypotheses of a history change at a non-`.wal` name of the claim `(j, N, h)`. -/
structure NonWalLog (cl : List Claim) (j : Ino) (N : NameSet) (h : NamesH) (x : Nat) (e : LogEntry)
    (c : Ents) (bt : GoString) : Prop where
  mem : (j, N, h) ∈ cl
  coh : ClaimCoh h j N
  start : h.next ≤ e.start
  writes : ∀ b, N.Mem b → e.op.Writes j b → b = bt
  cur : h.cur !! bt = none
  others : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt
  nonwal : walNameP bt = false

theorem NonWalLog.crash {cl : List Claim} {j : Ino} {N : NameSet} {h : NamesH} {x : Nat}
    {e : LogEntry} {c : Ents} {bt : GoString} (H : NonWalLog cl j N h x e c bt) {n : Nat} {m' : Tree}
    (hr : RegionCrashed (replClaim (j, N, h) (j, N, h.log x e c) cl) n m') :
    ∃ m'', RegionCrashed cl n m'' ∧ TreeNearW j m'' m' :=
  regionCrashed_nonwal hr H.mem H.coh H.start H.writes H.cur H.others H.nonwal

/-- **A WAL's crash condition after the create** (its area directory not `j`; its alternative, if
any, on the same names). -/
theorem crashOkA_nonwal {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {alt : Option WalLay} {cl : List Claim} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hok : CrashOkA C Mr d lay alt cl n)
    (halt : ∀ lay0, alt = some lay0 → lay0.jr = lay.jr ∧ lay0.nm = lay.nm ∧ lay0.j = lay.j)
    (hljr : lay.jr ≠ j) (H : NonWalLog cl j N h x e c bt) :
    CrashOkA C Mr d lay alt (replClaim (j, N, h) (j, N, h.log x e c) cl) n := by
  intro m' fo hr hf hn hw
  obtain ⟨m'', hr', hnear⟩ := H.crash hr
  have hwi := hnear.walInos lay.j
  have hent : m''.entry lay.jr lay.nm = m'.entry lay.jr lay.nm :=
    hnear _ _ (fun e => absurd e hljr)
  rcases hok m'' fo hr' hf (fun g hg hin => hn g hg (by rw [← hwi]; exact hin))
    (by rw [hwi]; exact hw) with hct | ⟨lay0, h0, hct⟩
  · exact Or.inl (crashTo_congr hent hwi hct)
  · obtain ⟨h1, h2, h3⟩ := halt lay0 h0
    refine Or.inr ⟨lay0, h0, crashTo_congr ?_ (by rw [h3]; exact hwi) hct⟩
    rw [h1, h2]; exact hent

theorem crashOkW_nonwal {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hok : CrashOkW C Mr d lay cl n) (hljr : lay.jr ≠ j) (H : NonWalLog cl j N h x e c bt) :
    CrashOkW C Mr d lay (replClaim (j, N, h) (j, N, h.log x e c) cl) n := by
  obtain ⟨alt, halt, hc⟩ := hok
  refine ⟨alt, halt, crashOkA_nonwal hc (fun lay0 h0 => ?_) hljr H⟩
  obtain ⟨-, h1, h2, h3, -⟩ := halt lay0 h0
  exact ⟨h1, h2, h3⟩

/-- **A directory of the area with no WAL, after the create.** -/
theorem absentOk_nonwal {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat} {j : Ino}
    {N : NameSet} {h : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hao : AbsentOk s jr cl n) (hjjr : j ≠ jr) (H : NonWalLog cl j N h x e c bt) :
    AbsentOk s jr (replClaim (j, N, h) (j, N, h.log x e c) cl) n := by
  intro dir nm hin hnone m' hr J hJ
  obtain ⟨m'', hr', hnear⟩ := H.crash hr
  rw [← hnear.walInos J]
  exact hao dir nm hin hnone m'' hr' J (by rw [hnear _ _ (fun e => absurd e.symm hjjr)]; exact hJ)

/-- `SegsNamed` over a directory changed only at non-`.wal` names. -/
theorem segsNamed_congr_wal {segs : List SegG} {E1 E2 : Ents}
    (h : ∀ b, walNameP b = true → E1 !! b = E2 !! b) (hs : SegsNamed segs E1) :
    SegsNamed segs E2 :=
  ⟨fun g hg => ⟨(hs.1 g hg).1, by rw [← h _ (hs.1 g hg).1]; exact (hs.1 g hg).2⟩,
    fun b e hb he => hs.2 b e hb (by rw [h b hb]; exact he)⟩

/-- The new claim once in the claims after the replacement, coherent, exclusive on `.wal` names
(`DirClaimOk` of the keyed claim replaced). -/
theorem dirClaimOk_nonwal {jr : Ino} {cl : List Claim} {j : Ino} {X : List GoString} {hj : NamesH}
    {x : Nat} {e : LogEntry} {c : Ents}
    (hD : DirClaimOk jr cl j X hj) (hcoh' : ClaimCoh (hj.log x e c) j (.except X)) :
    DirClaimOk jr (replClaim (j, NameSet.except X, hj) (j, NameSet.except X, hj.log x e c) cl)
      j X (hj.log x e c) := by
  classical
  obtain ⟨hjjr, hX, hc0, -, hexcl⟩ := hD
  have hne10 : (j, NameSet.except X, hj.log x e c) ≠ (j, NameSet.except X, hj) := by
    intro h; simp only [Prod.mk.injEq] at h; exact namesH_log_ne _ _ _ _ h.2.2
  refine ⟨hjjr, hX, ?_, hcoh', fun c' hc' hne hcj b hb => ?_⟩
  · obtain ⟨l1, l2, hcl', hrep⟩ := claimOnce_repl (c' := (j, NameSet.except X, hj.log x e c)) hc0
    have hnot : ∀ l : List Claim, (∀ y ∈ l, y ∈ cl) → (j, NameSet.except X, hj.log x e c) ∉ l :=
      fun l hsub hm => hexcl _ (hsub _ hm) hne10 rfl _ walNameP_wal (except_mem_wal hX)
    exact ⟨l1, l2, hrep, hnot l1 (fun y hy => by rw [hcl']; exact List.mem_append_left _ hy),
      hnot l2 (fun y hy => by rw [hcl']; simp [hy])⟩
  · rcases mem_replClaim_cases hc' with he | ⟨hc'', hne0⟩
    · exact absurd he hne
    · exact hexcl c' hc'' hne0 hcj b hb

/-- Another directory's claim, unchanged by the replacement. -/
theorem dirClaimOk_nonwal_other {jr : Ino} {cl : List Claim} {j : Ino} {X : List GoString}
    {hj : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {j' : Ino} {X' : List GoString} {hj1 : NamesH}
    (hj'j : j' ≠ j) (hD : DirClaimOk jr cl j' X' hj1) :
    DirClaimOk jr (replClaim (j, NameSet.except X, hj) (j, NameSet.except X, hj.log x e c) cl)
      j' X' hj1 := by
  obtain ⟨hj1jr, hX1, honce1, hcoh1, hex1⟩ := hD
  have hne0 : (j', NameSet.except X', hj1) ≠ (j, NameSet.except X, hj) := fun e => hj'j
    (by simp only [Prod.mk.injEq] at e; exact e.1)
  have hne1 : (j', NameSet.except X', hj1) ≠ (j, NameSet.except X, hj.log x e c) := fun e =>
    hj'j (by simp only [Prod.mk.injEq] at e; exact e.1)
  refine ⟨hj1jr, hX1, claimOnce_repl_other honce1 hne0 hne1, hcoh1, fun c' hc' hne hc1 b hb => ?_⟩
  rcases mem_replClaim_cases hc' with he | ⟨hc'', -⟩
  · rw [he] at hc1; exact absurd hc1.symm hj'j
  · exact hex1 c' hc'' hne hc1 b hb

/-- **The pure facts after a create at a non-`.wal` name of a keyed WAL directory's claim** (see the
file header). The old state: the invariant's pure conjuncts (any pending cut `cp`), the WAL of
`dir` with its layout `lay`, keyed `(lay.j, X)`, its claim `(lay.j, .except X, hj)`; the new claim
`hj.log x e c`, coherent, `c` agreeing with `hj.cur` on the `.wal` names; `e` writing only `bt`,
free, non-`.wal`, held by no other claim of `lay.j`. -/
theorem brokenHist_pure {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {CR : GMap GoString (NameSet × NamesH × Ino)} {K : GMap GoString (Ino × List GoString)}
    {cp : Option GoString} {dir : GoString} {lay : WalLay} {X : List GoString} {hj : NamesH}
    {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hW : WalsOk C Mr R jr s Ls cl n) (hWC : WalsCreateOk jr cl) (hCO : CreatingOk jr cl CR)
    (hAN : AbsentNone s jr cl n) (hNm : WalsNamed Ls cl n)
    (hDK : DirKeysOk C Mr jr s Ls cl n K cp) (hAt : WalsAt jr Ls cl)
    (hK : K !! dir = some (lay.j, X)) (hl : Ls !! dir = some lay)
    (hc0 : ClaimOnce (lay.j, .except X, hj) cl)
    (hcoh' : ClaimCoh (hj.log x e c) lay.j (.except X))
    (hc : ∀ b, walNameP b = true → c !! b = hj.cur !! b)
    (hs : hj.next ≤ e.start) (hbt : ∀ b, (NameSet.except X).Mem b → e.op.Writes lay.j b → b = bt)
    (hcur : hj.cur !! bt = none)
    (hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j → ¬ c'.2.1.Mem bt)
    (hbtw : walNameP bt = false) :
    let cl' := replClaim (lay.j, .except X, hj) (lay.j, .except X, hj.log x e c) cl
    WalsOk C Mr R jr s Ls cl' n ∧ WalsCreateOk jr cl' ∧ CreatingOk jr cl' CR ∧
      AbsentNone s jr cl' n ∧ WalsNamed Ls cl' n ∧ DirKeysOk C Mr jr s Ls cl' n K cp ∧
      WalsAt jr Ls cl' := by
  classical
  intro cl'
  obtain ⟨lay1, hj1, hl1, hlj, hjjr, hX, -, hcoh1, hexcl1⟩ := hDK.1 dir lay.j X hK
  rw [hl] at hl1
  cases hl1
  have hcl : (lay.j, NameSet.except X, hj) ∈ cl := claimOnce_mem hc0
  have hj1e := walClaim_eq hexcl1 hX hcl
  simp only [Prod.mk.injEq, true_and] at hj1e
  subst hj1e
  have hD : DirClaimOk jr cl lay.j X hj := ⟨hjjr, hX, hc0, hcoh1, hexcl1⟩
  have H : NonWalLog cl lay.j (.except X) hj x e c bt :=
    ⟨hcl, hcoh1, hs, hbt, hcur, hothers, hbtw⟩
  have hD' := dirClaimOk_nonwal (x := x) (e := e) (c := c) hD hcoh'
  -- a WAL directory claim of the new claims
  have hwdc : ∀ (j' : Ino) (hj'' : NamesH), WalDirClaim j' hj'' cl' →
      (j' = lay.j ∧ hj'' = hj.log x e c) ∨ (j' ≠ lay.j ∧ WalDirClaim j' hj'' cl) := by
    intro j' hj'' ⟨X', hX', hm, hcoh''⟩
    rcases mem_replClaim_cases hm with he | ⟨hm', hne⟩
    · simp only [Prod.mk.injEq] at he
      exact Or.inl ⟨he.1, he.2.2⟩
    · by_cases hj' : j' = lay.j
      · subst hj'
        exact absurd (except_mem_wal hX') (hexcl1 _ hm' hne rfl _ walNameP_wal)
      · exact Or.inr ⟨hj', X', hX', hm', hcoh''⟩
  have hwdc' : ∀ (j' : Ino) (hj'' : NamesH), j' ≠ lay.j → WalDirClaim j' hj'' cl →
      WalDirClaim j' hj'' cl' := by
    intro j' hj'' hj' ⟨X', hX', hm, hcoh''⟩
    refine ⟨X', hX', mem_replClaim_of_ne hm (fun he => hj' ?_), hcoh''⟩
    simp only [Prod.mk.injEq] at he; exact he.1
  have hljr : ∀ dir' d' lay', s.wal !! dir' = some d' → Ls !! dir' = some lay' → lay'.jr ≠ lay.j := by
    intro dir' d' lay' hd' hl'
    obtain ⟨la, -, -, hla, -, hjr', -⟩ := hW.1 dir' d' hd'
    rw [hl'] at hla; cases hla
    rw [hjr']; exact Ne.symm hjjr
  refine ⟨⟨fun dir' d' hd' => ?_, hW.2.1, hW.2.2.1, hW.2.2.2.1,
      absentOk_nonwal hW.2.2.2.2.1 hjjr H, dirsOk_cut hW.2.2.2.2.2 hcl hcoh1 hs hbt hcur hothers⟩,
    walsCreateOk_cut hjjr hWC,
    creatingOk_cut hCO hjjr hcl ⟨_, walNameP_wal, except_mem_wal hX⟩,
    absentNone_cut hAN hjjr hcl hcoh1 hs hbt hcur hothers, fun dir' lay' hl' => ?_, ?_, ?_⟩
  · -- `WalsOk`'s layouts
    obtain ⟨la, nm, hj2, hla, hin, hjr', hnm, hwd, habs, hcr⟩ := hW.1 dir' d' hd'
    have hcr' := crashOkW_nonwal hcr (hljr dir' d' la hd' hla) H
    by_cases hlaj : la.j = lay.j
    · obtain ⟨X2, hX2, hm2, -⟩ := hwd
      rw [hlaj] at hm2
      have e2 := walClaim_eq hexcl1 hX2 hm2
      simp only [Prod.mk.injEq, NameSet.except.injEq, true_and] at e2
      rw [e2.2] at habs
      refine ⟨la, nm, hj.log x e c, hla, hin, hjr', hnm, ?_, ?_, hcr'⟩
      · rw [hlaj]; exact ⟨X, hX, mem_replClaim_new hcl, hcoh'⟩
      · exact { habs with names := ⟨by rw [← habs.names.1]; exact walInos_congr hc, habs.names.2⟩ }
    · exact ⟨la, nm, hj2, hla, hin, hjr', hnm, hwdc' _ _ hlaj hwd, habs, hcr'⟩
  · -- `WalsNamed`
    obtain ⟨h1, h2⟩ := hNm dir' lay' hl'
    refine ⟨fun hj'' hWc => ?_, fun m' hr => ?_⟩
    · rcases hwdc _ _ hWc with ⟨hj', rfl⟩ | ⟨hj', hWc'⟩
      · rw [hj'] at h1
        exact segsNamed_congr_wal (fun b hb => (hc b hb).symm) (h1 hj ⟨X, hX, hcl, hcoh1⟩)
      · exact h1 hj'' hWc'
    · obtain ⟨m'', hr', hnear⟩ := H.crash hr
      exact segsNamedC_congr_ents (fun b hb => hnear.ents_wal _ b hb) (h2 m'' hr')
  · -- `DirKeysOk`
    refine ⟨fun dir' j' X' hk' => ?_, fun dir' d' lay' hd' hl' hcd => ?_, fun dir' l hl' => ?_⟩
    · obtain ⟨lay2, hj2, hl2, hlj2, hj2jr, hX2, honce2, hcoh2, hex2⟩ := hDK.1 dir' j' X' hk'
      by_cases hj' : j' = lay.j
      · subst hj'
        obtain ⟨hXe, -⟩ := DirClaimOk.eq_of_mem hD hX2 (claimOnce_mem honce2)
        subst hXe
        obtain ⟨-, -, honce', -, hex'⟩ := hD'
        exact ⟨lay2, hj.log x e c, hl2, hlj2, hj2jr, hX2, honce', hcoh', hex'⟩
      · obtain ⟨-, -, honce', -, hex'⟩ :=
          dirClaimOk_nonwal_other (x := x) (e := e) (c := c) (X := X) (hj := hj) hj'
            ⟨hj2jr, hX2, honce2, hcoh2, hex2⟩
        exact ⟨lay2, hj2, hl2, hlj2, hj2jr, hX2, honce', hcoh2, hex'⟩
    · exact crashOkA_nonwal (hDK.2.1 dir' d' lay' hd' hl' hcd) (fun _ h0 => by cases h0)
        (hljr dir' d' lay' hd' hl') H
    · obtain ⟨X', hj1, hk3, hx3⟩ := hDK.2.2 dir' l hl'
      by_cases hj' : l.j = lay.j
      · rw [hj'] at hk3 hx3 ⊢
        obtain ⟨hXe, hje⟩ := hD.eq_of_mem hk3.2.1 (claimOnce_mem hk3.2.2.1)
        rw [hXe, hje] at hx3
        refine ⟨X, hj.log x e c, hD', hx3.repl fun c' hc' hne _ => ?_⟩
        rcases mem_replClaim_cases hc' with he | ⟨hc'', hne0⟩
        · exact absurd he hne
        · exact ⟨hc'', hne0⟩
      · refine ⟨X', hj1, dirClaimOk_nonwal_other hj' hk3, hx3.mono fun c' hc' hcj _ => ?_⟩
        rcases mem_replClaim_cases hc' with he | ⟨hc'', -⟩
        · rw [he] at hcj; exact absurd hcj.symm hj'
        · exact hc''
  · -- `WalsAt`: the area's claims unchanged
    intro dir' lay' hl'
    refine ⟨hAt.ne hl', fun N h hm hN => ?_⟩
    rcases mem_replClaim_cases hm with he | ⟨hm', -⟩
    · simp only [Prod.mk.injEq] at he; exact absurd he.1 (Ne.symm hjjr)
    · exact (hAt dir' lay' hl').2 N h hm' hN

end pure

end WalFs
end EtcdGrove
end Perennial

end
