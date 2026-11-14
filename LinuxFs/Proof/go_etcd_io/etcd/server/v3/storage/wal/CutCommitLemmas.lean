/- Lean-first (no Rocq counterpart).

# The invariant's framed conjuncts across a cut's rename commit (W2, `CutCommit.lean`)

Pure. Each of `walInvBody`'s conjuncts but `WalsOk` after the WAL directory's claim
`(j, except X, hj)` is replaced by its logged successor (`replClaim`): `CreatingOk`, `AbsentNone`,
`DirsOk` (claims of the area directory unchanged, `j` not it), `WalsNamed` (the new segment at its
name, or, the rename dropped by a crash, at no `.wal` name), `DirKeysOk` (the cut pending in
`dir`). `walsOk_dir_ne`: another WAL's directory is not `j`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCommitPure

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

theorem namesH_log_ne (h : NamesH) (x : Nat) (e : LogEntry) (c : Ents) : h.log x e c ≠ h := by
  intro he
  have := congrArg (fun h : NamesH => h.ents.length) he
  simp [NamesH.log] at this

/-- **Two WALs, two directories**: another layout's directory is not the keyed WAL's `j` (its claim
would be `j`'s claim on its `.wal` names, so both would list the same segments, whose inodes are
distinct across layouts). -/
theorem walsOk_dir_ne {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString} {d : WalDur}
    {lay : WalLay} {j : Ino} {X : List GoString} {hj : NamesH}
    (hW : WalsOk C Mr R jr s Ls cl n)
    (hexcl : ∀ c' ∈ cl, c' ≠ (j, NameSet.except X, hj) → c'.1 = j → ∀ b, walNameP b = true →
      ¬ c'.2.1.Mem b)
    (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay) (hlj : lay.j = j)
    {dir' : GoString} {lay' : WalLay} (hne : dir' ≠ dir) (hl' : Ls !! dir' = some lay') :
    lay'.j ≠ j := by
  intro hj'
  obtain ⟨d', hd'⟩ : ∃ d', s.wal !! dir' = some d' := by
    cases e : s.wal !! dir' with
    | none => rw [hW.2.1 dir' e] at hl'; cases hl'
    | some d' => exact ⟨d', rfl⟩
  obtain ⟨la, -, h1, hla, -, -, -, ⟨X1, hX1, hm1, -⟩, habs1, -⟩ := hW.1 dir d hd
  rw [hl] at hla; cases hla
  obtain ⟨lb, -, h2, hlb, -, -, -, ⟨X2, hX2, hm2, -⟩, habs2, -⟩ := hW.1 dir' d' hd'
  rw [hl'] at hlb; cases hlb
  rw [hlj] at hm1
  rw [hj'] at hm2
  have e1 := walClaim_eq hexcl hX1 hm1
  have e2 := walClaim_eq hexcl hX2 hm2
  simp only [Prod.mk.injEq] at e1 e2
  have hn1 := habs1.names.1
  have hn2 := habs2.names.1
  rw [e1.2.2] at hn1
  rw [e2.2.2] at hn2
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ habs1.nonempty
  have : g.ino ∈ lay'.segs.map (·.ino) := by
    rw [← hn2, hn1]; exact List.mem_map_of_mem hg
  obtain ⟨g', hg', e⟩ := List.mem_map.1 this
  exact ((segsAll_nodup_iff Ls).1 hW.2.2.1).2 dir dir' lay lay' (Ne.symm hne) hl hl' g hg g' hg' e.symm

/-- The segments named below the last one's name. -/
theorem pairwise_last_name {segs : List SegG} {g0 : SegG}
    (hp : (segs.map (·.name)).Pairwise (fun a b => go.GoStringLt a b))
    (hg0 : segs.getLast? = some g0) : ∀ g' ∈ segs, g' = g0 ∨ go.GoStringLt g'.name g0.name := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hg0
  intro g' hg'
  rcases List.mem_append.1 hg' with hg' | hg'
  · right
    rw [List.map_append] at hp
    exact (List.pairwise_append.1 hp).2.2 _ (List.mem_map_of_mem hg') _ (by simp)
  · left; simpa using hg'

/-- **`Create`'s claims after the commit** (the replaced claim not of the area directory). -/
theorem creatingOk_cut {jr : Ino} {cl : List Claim} {CR : GMap GoString (NameSet × NamesH × Ino)}
    {j : Ino} {N : NameSet} {h h' : NamesH} (hCO : CreatingOk jr cl CR) (hjjr : j ≠ jr)
    (hcl : (j, N, h) ∈ cl) (hN : ∃ b, walNameP b = true ∧ N.Mem b) :
    CreatingOk jr (replClaim (j, N, h) (j, N, h') cl) CR := by
  intro dir N' h'' J hcr
  obtain ⟨hm, hcoh, hex, honce, hdist, hJr, hJc, hJd, hb⟩ := hCO dir N' h'' J hcr
  have hne0 : (jr, N', h'') ≠ (j, N, h) := fun e => hjjr (by simp only [Prod.mk.injEq] at e; exact e.1.symm)
  have hne1 : (jr, N', h'') ≠ (j, N, h') := fun e => hjjr (by simp only [Prod.mk.injEq] at e; exact e.1.symm)
  have hJj : J ≠ j := fun e => by
    obtain ⟨b, hbw, hbN⟩ := hN
    exact hJc _ hcl e.symm b (not_walTmps_of_wal hbw) hbN
  refine ⟨mem_replClaim_of_ne hm hne0, hcoh, fun c hc hne hc1 b hb' => ?_,
    claimOnce_repl_other honce hne0 hne1, hdist, hJr, fun c hc hc1 => ?_, hJd, hb⟩
  · rcases mem_replClaim_cases hc with rfl | ⟨hc', -⟩
    · exact absurd hc1 hjjr
    · exact hex c hc' hne hc1 b hb'
  · rcases mem_replClaim_cases hc with rfl | ⟨hc', -⟩
    · exact absurd hc1.symm hJj
    · exact hJc c hc' hc1

/-- **Strong absence after the commit** (the replaced claim not of the area directory). -/
theorem absentNone_cut {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat} {j : Ino}
    {N : NameSet} {h : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (han : AbsentNone s jr cl n) (hjjr : j ≠ jr)
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt) (hcur : h.cur !! bt = none)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    AbsentNone s jr (replClaim (j, N, h) (j, N, h.log x e c) cl) n := by
  intro dir nm hin hnone
  obtain ⟨h1, h2⟩ := han dir nm hin hnone
  refine ⟨fun N' h' hm hN => ?_, fun m' hr => ?_⟩
  · rcases mem_replClaim_cases hm with he | ⟨hm', -⟩
    · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm hjjr
    · exact h1 N' h' hm' hN
  · rcases regionCrashed_cut hr hcl hcoh hs hbt hcur hothers with hr' | hr'
    · have := h2 _ hr'
      rw [treeDel_entry] at this
      simpa [Ne.symm hjjr] using this
    · exact h2 m' hr'

/-- **The durable directories after the commit** (a lookup succeeding without `bt` is one with
it). -/
theorem dirsOk_cut {R : Roots} {s : AbsDiskState} {cl : List Claim} {n : Nat} {j : Ino}
    {N : NameSet} {h : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hdo : DirsOk R s cl n)
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt) (hcur : h.cur !! bt = none)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    DirsOk R s (replClaim (j, N, h) (j, N, h.log x e c) cl) n := by
  intro dd hdd m' hr
  rcases regionCrashed_cut hr hcl hcoh hs hbt hcur hothers with hr' | hr'
  · obtain ⟨J, hJ⟩ := hdo dd hdd _ hr'
    exact ⟨J, lookupH_treeDel hJ⟩
  · exact hdo dd hdd m' hr'

/-- **The segments at their names after the commit**: the cut WAL's, its new segment at `bt` in the
new claim, and after a crash either as the new claim has them (the rename kept) or as before, the
new segment's file at no `.wal` name (dropped: `SegsNamedC`'s last clause); the others' as before
(their directories not `j`). -/
theorem walsNamed_cut {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString} {d : WalDur}
    {lay : WalLay} {g : SegG} {X : List GoString} {hj : NamesH} {x : Nat} {e : LogEntry}
    {bt : GoString} {b0 wr : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hNm : WalsNamed Ls cl n)
    (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hcl : (lay.j, NameSet.except X, hj) ∈ cl) (hX : ∀ b ∈ X, walNameP b = false)
    (hcoh : ClaimCoh hj lay.j (.except X))
    (hcoh' : ClaimCoh (hj.log x e (<[bt := Node.file g.ino]> hj.cur)) lay.j (.except X))
    (hexcl : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j → ∀ b,
      walNameP b = true → ¬ c'.2.1.Mem b)
    (hs : hj.next ≤ e.start) (hbt : ∀ b, (NameSet.except X).Mem b → e.op.Writes lay.j b → b = bt)
    (hcur : hj.cur !! bt = none) (hbtw : walNameP bt = true) (hgname : g.name = bt)
    (hino : ∀ g' ∈ segsAll Ls, g'.ino ≠ g.ino)
    (hents : walInos (<[bt := Node.file g.ino]> hj.cur) = lay.segs.map (·.ino) ++ [g.ino]) :
    WalsNamed (<[dir := cutLay lay b0 g wr]> Ls)
      (replClaim (lay.j, NameSet.except X, hj)
        (lay.j, NameSet.except X, hj.log x e (<[bt := Node.file g.ino]> hj.cur)) cl) n := by
  classical
  have hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j →
      ¬ c'.2.1.Mem bt := fun c' hc hne hcj => hexcl c' hc hne hcj bt hbtw
  intro dir' lay' hl'
  by_cases hdd : dir' = dir
  · subst hdd
    rw [GMap.lookup_insert_eq] at hl'
    simp only [Option.some.injEq] at hl'
    subst hl'
    have hsn : SegsNamed lay.segs hj.cur := (hNm dir' lay hl).1 hj ⟨X, hX, hcl, hcoh⟩
    have hsn' : SegsNamed (lay.segs ++ [g]) (<[bt := Node.file g.ino]> hj.cur) := by
      refine ⟨fun g' hg' => ?_, fun b e' hb he => ?_⟩
      · rcases List.mem_append.1 hg' with hg' | hg'
        · obtain ⟨hw, he⟩ := hsn.1 g' hg'
          have hne : bt ≠ g'.name := by
            intro hbe; rw [← hbe, hcur] at he; cases he
          exact ⟨hw, by rw [GMap.lookup_insert_ne _ _ hne]; exact he⟩
        · simp only [List.mem_singleton] at hg'
          rw [hg']
          exact ⟨hgname ▸ hbtw, by rw [hgname, GMap.lookup_insert_eq]⟩
      · by_cases hbe : bt = b
        · rw [← hbe, GMap.lookup_insert_eq] at he
          exact ⟨g.ino, (Option.some.inj he).symm⟩
        · rw [GMap.lookup_insert_ne _ _ hbe] at he
          exact hsn.2 b e' hb he
    refine ⟨fun hj'' hWc => ?_, fun m' hr => ?_⟩
    · obtain ⟨X', hX', hm, -⟩ := hWc
      rcases mem_replClaim_cases hm with he | ⟨hm', hne⟩
      · simp only [Prod.mk.injEq] at he
        rw [he.2.2]; exact hsn'
      · exact absurd (except_mem_wal hX') (hexcl _ hm' hne rfl _ walNameP_wal)
    · obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
      show SegsNamedC (lay.segs ++ [g]) (entsOf m' lay.j)
      by_cases hx : K x
      · obtain ⟨hold, -⟩ := regionCrashedK_kept cl n m' K lay.j _ hj x e _ bt hK hx hcl hcoh hs hbt
          hcur hothers
        refine segsNamedC_congr_ents (fun b hb => ?_) (hsn'.crash (fun i hi => ?_))
        · have hbX : (NameSet.except X).Mem b := fun h => by rw [hX b h] at hb; cases hb
          rw [entsOf_entry, hK.2.2 _ (mem_replClaim_new hcl) b hbX]
          refine (hcoh'.2 K (fun xe hxe => ?_) b hbX).symm
          simp only [NamesH.log, List.mem_append, List.mem_singleton] at hxe
          rcases hxe with hxe | hxe
          · exact hold xe hxe
          · rw [hxe]; exact hx
        · rw [hents] at hi
          simpa using hi
      · have hr' : RegionCrashed cl n m' :=
          (regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_unlog cl n m' K lay.j _ hj x e _ hK hx⟩
        obtain ⟨h1, h2, h3⟩ := (hNm dir' lay hl).2 m' hr'
        refine ⟨fun g' hg' => ?_, h2, fun i hi => ?_⟩
        · rcases List.mem_append.1 hg' with hg' | hg'
          · exact h1 g' hg'
          · simp only [List.mem_singleton] at hg'
            rw [hg']
            refine ⟨hgname ▸ hbtw, fun hi => ?_⟩
            obtain ⟨g'', hg'', e''⟩ := List.mem_map.1 (h3 _ hi)
            exact absurd e'' (hino g'' (mem_segsAll hl hg''))
        · obtain ⟨g'', hg'', rfl⟩ := List.mem_map.1 (h3 i hi)
          exact List.mem_map.2 ⟨g'', List.mem_append_left _ hg'', rfl⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl'
    have hjne : lay'.j ≠ lay.j := walsOk_dir_ne hW hexcl hd hl rfl hdd hl'
    obtain ⟨h1, h2⟩ := hNm dir' lay' hl'
    refine ⟨fun hj'' hWc => ?_, fun m' hr => ?_⟩
    · obtain ⟨X', hX', hm, hcoh''⟩ := hWc
      rcases mem_replClaim_cases hm with he | ⟨hm', -⟩
      · simp only [Prod.mk.injEq] at he; exact absurd he.1 hjne
      · exact h1 hj'' ⟨X', hX', hm', hcoh''⟩
    · rcases regionCrashed_cut hr hcl hcoh hs hbt hcur hothers with hr' | hr'
      · rw [← entsOf_treeDel_ne m' bt hjne]; exact h2 _ hr'
      · exact h2 m' hr'

/-- **The directory keys after the commit**: the cut WAL's claim replaced once (the replacement in
no other place: it is `j`'s on `.wal` names), the other keys as before (their directories not `j`);
every WAL but the cut one with no alternative layout. -/
theorem dirKeysOk_cut {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {dir : GoString} {d : WalDur} {lay lay' : WalLay}
    {X : List GoString} {hj : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hW : WalsOk C Mr R jr s Ls cl n) (hDK : DirKeysOk C Mr jr s Ls cl n K none)
    (hK : K !! dir = some (lay.j, X)) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hlj' : lay'.j = lay.j) (hjjr : lay.j ≠ jr) (hX : ∀ b ∈ X, walNameP b = false)
    (hc0 : ClaimOnce (lay.j, NameSet.except X, hj) cl)
    (hcoh : ClaimCoh hj lay.j (.except X)) (hcoh' : ClaimCoh (hj.log x e c) lay.j (.except X))
    (hexcl : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j → ∀ b,
      walNameP b = true → ¬ c'.2.1.Mem b)
    (hs : hj.next ≤ e.start) (hbt : ∀ b, (NameSet.except X).Mem b → e.op.Writes lay.j b → b = bt)
    (hcur : hj.cur !! bt = none) (hbtw : walNameP bt = true) :
    DirKeysOk C Mr jr s (<[dir := lay']> Ls)
      (replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x e c) cl) n K
      (some dir) := by
  classical
  have hcl := claimOnce_mem hc0
  have hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, hj) → c'.1 = lay.j →
      ¬ c'.2.1.Mem bt := fun c' hc hne hcj => hexcl c' hc hne hcj bt hbtw
  have hne10 : (lay.j, NameSet.except X, hj.log x e c) ≠ (lay.j, NameSet.except X, hj) := by
    intro h; simp only [Prod.mk.injEq] at h; exact namesH_log_ne _ _ _ _ h.2.2
  -- the cut WAL's claim, replaced
  have hcutOnce : ClaimOnce (lay.j, NameSet.except X, hj.log x e c)
      (replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x e c) cl) := by
    obtain ⟨l1, l2, hcl', hrep⟩ :=
      claimOnce_repl (c' := (lay.j, NameSet.except X, hj.log x e c)) hc0
    have hnot : ∀ l : List Claim, (∀ y ∈ l, y ∈ cl) →
        (lay.j, NameSet.except X, hj.log x e c) ∉ l := fun l hsub hm =>
      hexcl _ (hsub _ hm) hne10 rfl _ walNameP_wal (except_mem_wal hX)
    exact ⟨l1, l2, hrep, hnot l1 (fun y hy => by rw [hcl']; exact List.mem_append_left _ hy),
      hnot l2 (fun y hy => by rw [hcl']; simp [hy])⟩
  have hcutEx : ∀ c' ∈ replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x e c) cl,
      c' ≠ (lay.j, NameSet.except X, hj.log x e c) → c'.1 = lay.j → ∀ b, walNameP b = true →
        ¬ c'.2.1.Mem b := by
    intro c' hc' hne hcj b hb
    rcases mem_replClaim_cases hc' with he | ⟨hc'', hne0⟩
    · exact absurd he hne
    · exact hexcl c' hc'' hne0 hcj b hb
  -- another WAL's directory claim (its directory not `lay.j`), unchanged
  have hother : ∀ (j' : Ino) (X' : List GoString) (hj1 : NamesH), j' ≠ lay.j → DirClaimOk jr cl j' X' hj1 →
      DirClaimOk jr (replClaim (lay.j, NameSet.except X, hj) (lay.j, NameSet.except X, hj.log x e c) cl)
        j' X' hj1 := by
    intro j' X' hj1 hj'j ⟨hj1jr, hX1, honce1, hcoh1, hex1⟩
    have hne0 : (j', NameSet.except X', hj1) ≠ (lay.j, NameSet.except X, hj) := fun e => hj'j
      (by simp only [Prod.mk.injEq] at e; exact e.1)
    have hne1 : (j', NameSet.except X', hj1) ≠ (lay.j, NameSet.except X, hj.log x e c) := fun e =>
      hj'j (by simp only [Prod.mk.injEq] at e; exact e.1)
    refine ⟨hj1jr, hX1, claimOnce_repl_other honce1 hne0 hne1, hcoh1, fun c' hc' hne hc1 b hb => ?_⟩
    rcases mem_replClaim_cases hc' with he | ⟨hc'', -⟩
    · rw [he] at hc1; exact absurd hc1.symm hj'j
    · exact hex1 c' hc'' hne hc1 b hb
  refine ⟨fun dir' j' X' hk' => ?_, fun dir' d' lay'' hd' hl'' hcd => ?_, fun dir' l hl' => ?_⟩
  · by_cases hdd : dir' = dir
    · subst hdd
      rw [hK] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq] at hk'
      obtain ⟨rfl, rfl⟩ := hk'
      exact ⟨lay', hj.log x e c, GMap.lookup_insert_eq .., hlj', hjjr, hX, hcutOnce, hcoh', hcutEx⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)]
      obtain ⟨lay1, hj1, hl1, hlj1, hj1jr, hX1, honce1, hcoh1, hex1⟩ := hDK.1 dir' j' X' hk'
      have hj'j : j' ≠ lay.j := hlj1 ▸ walsOk_dir_ne hW hexcl hd hl rfl hdd hl1
      obtain ⟨-, -, honce', -, hex'⟩ := hother j' X' hj1 hj'j ⟨hj1jr, hX1, honce1, hcoh1, hex1⟩
      exact ⟨lay1, hj1, hl1, hlj1, hj1jr, hX1, honce', hcoh1, hex'⟩
  rotate_left
  · by_cases hdd : dir' = dir
    · subst hdd
      rw [GMap.lookup_insert_eq] at hl'
      cases hl'
      rw [hlj']
      obtain ⟨X2, hj2, hD2, hx2⟩ := hDK.2.2 _ lay hl
      obtain ⟨hXe, hje⟩ := hD2.eq_of_mem hX hcl
      subst hXe hje
      refine ⟨X, hj.log x e c, ⟨hjjr, hX, hcutOnce, hcoh', hcutEx⟩, hx2.repl fun c' hc' hne _ => ?_⟩
      rcases mem_replClaim_cases hc' with he | ⟨hc'', hne0⟩
      · exact absurd he hne
      · exact ⟨hc'', hne0⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl'
      obtain ⟨X', hj1, hk3, hx3⟩ := hDK.2.2 dir' l hl'
      have hj'j := walsOk_dir_ne hW hexcl hd hl rfl hdd hl'
      refine ⟨X', hj1, hother _ X' hj1 hj'j hk3, hx3.mono fun c' hc' hcj _ => ?_⟩
      rcases mem_replClaim_cases hc' with he | ⟨hc'', -⟩
      · rw [he] at hcj; exact absurd hcj.symm hj'j
      · exact hc''
  · have hdd : dir' ≠ dir := fun h => hcd (by rw [h])
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at hl''
    obtain ⟨la, -, -, hla, -, hjr', -, -, -, -⟩ := hW.1 dir' d' hd'
    rw [hl''] at hla; cases hla
    exact crashOkA_cut_other (hDK.2.1 dir' d' lay'' hd' hl'' (fun h => by cases h))
      (fun _ h => by cases h) (walsOk_dir_ne hW hexcl hd hl rfl hdd hl'')
      (by rw [hjr']; exact Ne.symm hjjr) hcl hcoh hs hbt hcur hothers

end pure

end WalFs
end EtcdGrove
end Perennial

end
