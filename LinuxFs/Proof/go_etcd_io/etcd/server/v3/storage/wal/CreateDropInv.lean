/- Lean-first (no Rocq counterpart).

# The invariant's pure facts across the drop of a name off the area claim (W4,
`notes/wal-fsext-plan.md`, "W4 implementation log", ninth session)

`Create` takes the whole claim on `nm.tmp` (and `cleanupWAL` on `nm.broken.<time>`): the invariant's
half of the area claim `(jr, N, h)` is replaced by its part off the name `b` (`dropClaims`), the
program keeping the part on `b` whole. Fewer claims allow more crashed trees; each crash `m'` of
the remaining claims is, with `b` set to what the area claim says of it (`regionCrashedK_drop1` over
the claims split at `b`, `regionCrashedK_cover` back to `cl`), a crash of `cl` (`DropOk.crash`: needs
the claims' entries to be one log's with `Starts`, the file system's `osClaims_log`). Every fact of
the invariant reads of a crashed tree only names other than `b` of `jr` (a WAL's name in the area,
`.wal` names, the durable directories' lookups, `DirsAvoid`), so it carries over (`walsOk_drop`,
`absentNone_drop`, `walsNamed_drop`, `dirKeysOk_drop`, `walsCreateOk_drop`). The area claim is no WAL
directory's claim (`WalDirClaimOf`; the step shows it from `walParked`), so neither is its part.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDrop

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- The claims after the drop of the name `b` off the area claim `(jr, N, h)`: its part off `b`. -/
def dropClaims (cl : List Claim) (jr : Ino) (N : NameSet) (h : NamesH) (b : GoString) : List Claim :=
  replClaim (jr, N, h) (jr, N.diff [b], h.restrict jr (N.diff [b])) cl

theorem mem_dropClaims {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {b : GoString}
    {c : Claim} (hc : c ∈ dropClaims cl jr N h b) :
    c = (jr, N.diff [b], h.restrict jr (N.diff [b])) ∨ (c ∈ cl ∧ c ≠ (jr, N, h)) := by
  classical
  unfold dropClaims replClaim at hc
  obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
  by_cases he : c0 = (jr, N, h)
  · left; rw [if_pos he]
  · right; rw [if_neg he]; exact ⟨hc0, he⟩

theorem mem_dropClaims_of {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {b : GoString}
    {c : Claim} (hc : c ∈ cl) (hne : c ≠ (jr, N, h)) : c ∈ dropClaims cl jr N h b := by
  classical
  have := mem_replClaim (c0 := (jr, N, h)) (c1 := (jr, N.diff [b], h.restrict jr (N.diff [b]))) hc
  rw [if_neg hne] at this
  exact this

theorem mem_dropClaims_new {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {b : GoString}
    (hc : (jr, N, h) ∈ cl) : (jr, N.diff [b], h.restrict jr (N.diff [b])) ∈ dropClaims cl jr N h b := by
  classical
  have := mem_replClaim (c0 := (jr, N, h)) (c1 := (jr, N.diff [b], h.restrict jr (N.diff [b]))) hc
  rw [if_pos rfl] at this
  exact this

/-- **What the drop of `b` off the area claim `(jr, N, h)` needs of the invariant's claims `cl`**:
their entries are one log's, which `Starts` (the file system's `osClaims_log`); the area claim is
among them, its history its own restriction (`namesOf_restrict_self`), holding `b`, which no other
claim of `jr` holds (`NamesCoh.disj`). -/
structure DropOk (cl : List Claim) (jr : Ino) (N : NameSet) (h : NamesH) (b : GoString) : Prop where
  log : ∃ log, Starts log ∧ ClaimsLog log cl
  mem : (jr, N, h) ∈ cl
  self : h.restrict jr N = h
  memb : N.Mem b
  others : ∀ c ∈ cl, c ≠ (jr, N, h) → c.1 = jr → ¬ c.2.1.Mem b

/-- **A crash of the claims after the drop is, with `b` of `jr` set to some value, one of the
claims before it.** -/
theorem DropOk.crashK {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {b : GoString}
    (hd : DropOk cl jr N h b) {n : Nat} {m' : Tree} {K : Nat → Prop}
    (hK : RegionCrashedK (dropClaims cl jr N h b) n m' K) :
    ∃ v K', RegionCrashedK cl n (treeSetE m' jr b v) K' := by
  classical
  obtain ⟨log, hst, hlog⟩ := hd.log
  have hc := hd.mem
  have hself := hd.self
  have hbI : (N.inter [b]).Mem b := (N.mem_inter [b] b).2 ⟨hd.memb, List.mem_singleton_self _⟩
  have hlog'' : ClaimsLog log ((jr, .only [b], h.restrict jr (N.inter [b])) ::
      dropClaims cl jr N h b) := by
    intro c hc' x e E hx
    rcases List.mem_cons.1 hc' with rfl | hc'
    · obtain ⟨E', hE'⟩ := restrict_ents_mem hx
      exact hlog _ hc x e E' hE'
    · rcases mem_dropClaims hc' with rfl | ⟨hc', -⟩
      · obtain ⟨E', hE'⟩ := restrict_ents_mem hx
        exact hlog _ hc x e E' hE'
      · exact hlog c hc' x e E hx
  have hdisj : ∀ c ∈ dropClaims cl jr N h b, c.1 = jr → ¬ c.2.1.Mem b := by
    intro c hc' hj
    rcases mem_dropClaims hc' with rfl | ⟨hc', hne⟩
    · intro hm
      exact ((N.mem_diff [b] b).1 hm).2 (List.mem_singleton_self _)
    · exact hd.others c hc' hne hj
  have h1 := regionCrashedK_drop1 hst hlog'' hdisj hK
  refine ⟨_, _, regionCrashedK_cover (fun c hc' x e E hx => ?_) (fun c hc' b' hb' => ?_) h1⟩
  · by_cases hce : c = (jr, N, h)
    · subst hce
      simp only at hx
      rw [← hself] at hx
      obtain ⟨b', hbN, hw⟩ := restrict_ents_writes hx
      rw [hself] at hx
      by_cases hbb : b' = b
      · subst hbb
        exact ⟨_, List.mem_cons_self .., _, mem_restrict_ents hx hbI hw⟩
      · have hbD : (N.diff [b]).Mem b' := (N.mem_diff [b] b').2 ⟨hbN, by simpa using hbb⟩
        exact ⟨_, List.mem_cons_of_mem _ (mem_dropClaims_new hc), _, mem_restrict_ents hx hbD hw⟩
    · exact ⟨c, List.mem_cons_of_mem _ (mem_dropClaims_of hc' hce), E, hx⟩
  · by_cases hce : c = (jr, N, h)
    · subst hce
      simp only at hb' ⊢
      by_cases hbb : b' = b
      · subst hbb
        refine ⟨_, List.mem_cons_self .., rfl, by simp [NameSet.Mem], fun K' => ?_⟩
        exact valAfter_restrict h jr _ K' _ hbI
      · have hbD : (N.diff [b]).Mem b' := (N.mem_diff [b] b').2 ⟨hb', by simpa using hbb⟩
        exact ⟨_, List.mem_cons_of_mem _ (mem_dropClaims_new hc), rfl, hbD,
          fun K' => valAfter_restrict h jr _ K' b' hbD⟩
    · exact ⟨c, List.mem_cons_of_mem _ (mem_dropClaims_of hc' hce), rfl, hb', fun _ => rfl⟩

theorem DropOk.crash {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {b : GoString}
    (hd : DropOk cl jr N h b) {n : Nat} {m' : Tree}
    (hr : RegionCrashed (dropClaims cl jr N h b) n m') :
    ∃ v, RegionCrashed cl n (treeSetE m' jr b v) := by
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  obtain ⟨v, K', hK'⟩ := hd.crashK hK
  exact ⟨v, (regionCrashed_iff _ _ _).2 ⟨K', hK'⟩⟩

/-! ## The facts carry over -/

theorem treeSetE_entry_ne {m : Tree} {jr : Ino} {b : GoString} {v : Option Node} {j : Ino}
    {b' : GoString} (h : ¬ (j = jr ∧ b' = b)) : (treeSetE m jr b v).entry j b' = m.entry j b' := by
  rw [treeSetE_entry, if_neg h]

theorem walInos_treeSetE {m : Tree} {jr : Ino} {b : GoString} {v : Option Node} (j : Ino)
    (hbw : walNameP b = false) : walInos (entsOf (treeSetE m jr b v) j) = walInos (entsOf m j) := by
  apply walInos_congr
  intro b' hb'
  rw [entsOf_entry, entsOf_entry, treeSetE_entry_ne]
  rintro ⟨-, rfl⟩
  rw [hbw] at hb'; cases hb'

/-- **A WAL's crash condition carries over** (its name in the area not `b`). -/
theorem crashOkA_drop {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {alt : Option WalLay} {cl : List Claim} {n : Nat} {jr : Ino} {N : NameSet} {h : NamesH}
    {b : GoString} (hd : DropOk cl jr N h b) (hbw : walNameP b = false)
    (hnm : ¬ (lay.jr = jr ∧ lay.nm = b))
    (halt : ∀ lay0, alt = some lay0 → lay0.jr = lay.jr ∧ lay0.nm = lay.nm ∧ lay0.j = lay.j)
    (hok : CrashOkA C Mr d lay alt cl n) : CrashOkA C Mr d lay alt (dropClaims cl jr N h b) n := by
  intro m' fo hr hf hn hw
  obtain ⟨v, hr1⟩ := hd.crash hr
  have hwi := walInos_treeSetE (m := m') (jr := jr) (v := v) lay.j hbw
  have hent : (treeSetE m' jr b v).entry lay.jr lay.nm = m'.entry lay.jr lay.nm :=
    treeSetE_entry_ne hnm
  rcases hok _ fo hr1 hf (fun g hg hin => hn g hg (by rw [← hwi]; exact hin)) (by rw [hwi]; exact hw)
    with hct | ⟨lay0, h0, hct⟩
  · exact Or.inl (crashTo_congr hent hwi hct)
  · obtain ⟨h1, h2, h3⟩ := halt lay0 h0
    refine Or.inr ⟨lay0, h0, crashTo_congr ?_ (by rw [h3]; exact hwi) hct⟩
    rw [h1, h2]; exact hent

theorem crashOkW_drop {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} {jr : Ino} {N : NameSet} {h : NamesH} {b : GoString}
    (hd : DropOk cl jr N h b) (hbw : walNameP b = false) (hnm : ¬ (lay.jr = jr ∧ lay.nm = b))
    (hok : CrashOkW C Mr d lay cl n) : CrashOkW C Mr d lay (dropClaims cl jr N h b) n := by
  obtain ⟨alt, halt, hcr⟩ := hok
  refine ⟨alt, halt, crashOkA_drop hd hbw hnm (fun lay0 h0 => ?_) hcr⟩
  obtain ⟨-, h1, h2, h3, -⟩ := halt lay0 h0
  exact ⟨h1, h2, h3⟩

/-- The part off `b` of a claim that is no WAL directory's is none either. -/
theorem not_walDirClaimOf_diff {Ls : GMap GoString WalLay} {jr : Ino} {N : NameSet} {h h' : NamesH}
    {b : GoString} (hbw : walNameP b = false) (hn : ¬ WalDirClaimOf Ls (jr, N, h)) :
    ¬ WalDirClaimOf Ls (jr, N.diff [b], h') := by
  rintro ⟨dir, lay, hl, hj, X, hX, hXw⟩
  apply hn
  cases N with
  | only bs => simp [NameSet.diff] at hX
  | except bs =>
    simp only [NameSet.diff, NameSet.except.injEq] at hX
    exact ⟨dir, lay, hl, hj, bs, rfl, fun b' hb' => hXw b' (by rw [← hX]; simp [hb'])⟩

/-- A WAL directory's claim among `cl` is one after the drop. -/
theorem walDirClaim_drop {Ls : GMap GoString WalLay} {cl : List Claim} {jr : Ino} {N : NameSet}
    {h : NamesH} {b : GoString} (hn : ¬ WalDirClaimOf Ls (jr, N, h)) {dir : GoString} {lay : WalLay}
    (hl : Ls !! dir = some lay) {hj : NamesH} (hw : WalDirClaim lay.j hj cl) :
    WalDirClaim lay.j hj (dropClaims cl jr N h b) := by
  obtain ⟨X, hX, hm, hco⟩ := hw
  refine ⟨X, hX, mem_dropClaims_of hm ?_, hco⟩
  intro he
  apply hn
  rw [← he]
  exact ⟨dir, lay, hl, rfl, X, rfl, hX⟩

/-- A WAL directory's claim after the drop is one before it. -/
theorem walDirClaim_of_drop {Ls : GMap GoString WalLay} {cl : List Claim} {jr : Ino} {N : NameSet}
    {h : NamesH} {b : GoString} (hbw : walNameP b = false) (hn : ¬ WalDirClaimOf Ls (jr, N, h))
    {dir : GoString} {lay : WalLay} (hl : Ls !! dir = some lay) {hj : NamesH}
    (hw : WalDirClaim lay.j hj (dropClaims cl jr N h b)) : WalDirClaim lay.j hj cl := by
  obtain ⟨X, hX, hm, hco⟩ := hw
  rcases mem_dropClaims hm with he | ⟨hm, -⟩
  · exfalso
    apply not_walDirClaimOf_diff (h' := h.restrict jr (N.diff [b])) hbw hn
    rw [← he]
    exact ⟨dir, lay, hl, rfl, X, rfl, hX⟩
  · exact ⟨X, hX, hm, hco⟩

/-- **`WalsOk` carries over** (`b` no WAL name, nor a `.wal` name; an area slot, which the durable
directories' lookups avoid). -/
theorem walsOk_drop {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {N : NameSet} {h : NamesH}
    {b : GoString} (hd : DropOk cl jr N h b) (hbw : walNameP b = false) (hbn : ¬ walNameOk b)
    (hbs : AreaSlot b) (hav : DirsAvoid R jr s) (hnW : ¬ WalDirClaimOf Ls (jr, N, h))
    (hok : WalsOk C Mr R jr s Ls cl n) : WalsOk C Mr R jr s Ls (dropClaims cl jr N h b) n := by
  obtain ⟨hw, hnone, hnd, hcut, habs, hdirs⟩ := hok
  refine ⟨fun dir d hd' => ?_, hnone, hnd, hcut, ?_, ?_⟩
  · obtain ⟨lay, nm, hj, hl, hia, hjr, hnm, hwd, hab, hco⟩ := hw dir d hd'
    refine ⟨lay, nm, hj, hl, hia, hjr, hnm, walDirClaim_drop hnW hl hwd, hab,
      crashOkW_drop hd hbw ?_ hco⟩
    rintro ⟨-, h2⟩
    exact hbn (h2 ▸ hnm ▸ hia.1)
  · intro dir nm hia hn m' hr J hJ
    obtain ⟨v, hr1⟩ := hd.crash hr
    have hne : ¬ (jr = jr ∧ nm = b) := fun ⟨_, h2⟩ => hbn (h2 ▸ hia.1)
    have := habs dir nm hia hn _ hr1 J (by rw [treeSetE_entry_ne hne]; exact hJ)
    rw [walInos_treeSetE (jr := jr) J hbw] at this
    exact this
  · intro dd hdd m' hr
    obtain ⟨v, hr1⟩ := hd.crash hr
    obtain ⟨J, hJ⟩ := hdirs dd hdd _ hr1
    refine ⟨J, ?_⟩
    rw [← hav dd hdd (treeSetE m' jr b v) m' (fun j b' hn => ?_)]
    · exact hJ
    · apply treeSetE_entry_ne
      rintro ⟨rfl, rfl⟩
      exact hn ⟨rfl, hbs⟩

/-- **`AbsentNone` carries over.** -/
theorem absentNone_drop {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat} {N : NameSet}
    {h : NamesH} {b : GoString} (hd : DropOk cl jr N h b) (hbn : ¬ walNameOk b)
    (hok : AbsentNone s jr cl n) : AbsentNone s jr (dropClaims cl jr N h b) n := by
  intro dir nm hia hn
  obtain ⟨h1, h2⟩ := hok dir nm hia hn
  refine ⟨fun N' h' hm hN' => ?_, fun m' hr => ?_⟩
  · rcases mem_dropClaims hm with he | ⟨hm, -⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl, rfl⟩ := he
      have hnN : N.Mem nm := ((N.mem_diff [b] nm).1 hN').1
      simp only [NamesH.restrict]
      rw [restrictN_lookup _ _ _ hN']
      exact h1 N h hd.mem hnN
    · exact h1 N' h' hm hN'
  · obtain ⟨v, hr1⟩ := hd.crash hr
    have hne : ¬ (jr = jr ∧ nm = b) := fun ⟨_, h2⟩ => hbn (h2 ▸ hia.1)
    rw [← treeSetE_entry_ne (v := v) hne]
    exact h2 _ hr1

/-- `SegsNamedC` reads only `.wal` names. -/
theorem segsNamedC_congr {segs : List SegG} {E1 E2 : Ents}
    (he : ∀ b, walNameP b = true → E1 !! b = E2 !! b) (h : SegsNamedC segs E1) :
    SegsNamedC segs E2 := by
  have hw := walInos_congr he
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun g hg => ?_, fun b' e hb he' => h2 b' e hb (by rw [he b' hb]; exact he'),
    fun i hi => h3 i (by rw [hw]; exact hi)⟩
  obtain ⟨ha, hb⟩ := h1 g hg
  exact ⟨ha, fun hi => by rw [← he _ ha]; exact hb (by rw [hw]; exact hi)⟩

/-- **`WalsNamed` carries over.** -/
theorem walsNamed_drop {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {jr : Ino}
    {N : NameSet} {h : NamesH} {b : GoString} (hd : DropOk cl jr N h b) (hbw : walNameP b = false)
    (hnW : ¬ WalDirClaimOf Ls (jr, N, h)) (hok : WalsNamed Ls cl n) :
    WalsNamed Ls (dropClaims cl jr N h b) n := by
  intro dir lay hl
  obtain ⟨h1, h2⟩ := hok dir lay hl
  refine ⟨fun hj hw => h1 hj (walDirClaim_of_drop hbw hnW hl hw), fun m' hr => ?_⟩
  obtain ⟨v, hr1⟩ := hd.crash hr
  refine segsNamedC_congr (fun b' hb' => ?_) (h2 _ hr1)
  rw [entsOf_entry, entsOf_entry, treeSetE_entry_ne]
  rintro ⟨-, rfl⟩
  rw [hbw] at hb'; cases hb'

/-- **`WalsCreateOk` carries over** (`b` no WAL name). -/
theorem walsCreateOk_drop {jr : Ino} {cl : List Claim} {N : NameSet} {h : NamesH} {b : GoString}
    (hc : (jr, N, h) ∈ cl) (hbn : ¬ walNameOk b) (hok : WalsCreateOk jr cl) :
    WalsCreateOk jr (dropClaims cl jr N h b) := by
  intro nm hnm
  obtain ⟨N', h', hm, hN'⟩ := hok nm hnm
  by_cases he : (jr, N', h') = (jr, N, h)
  · simp only [Prod.mk.injEq, true_and] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨_, _, mem_dropClaims_new hc, (N'.mem_diff [b] nm).2 ⟨hN', ?_⟩⟩
    simp only [List.mem_singleton]
    rintro rfl; exact hbn hnm
  · exact ⟨N', h', mem_dropClaims_of hm he, hN'⟩

/-- `ClaimOnce` of a claim of another directory carries over. -/
theorem claimOnce_drop {cl : List Claim} {jr : Ino} {N : NameSet} {h : NamesH} {b : GoString}
    {c : Claim} (hj : c.1 ≠ jr) (hok : ClaimOnce c cl) : ClaimOnce c (dropClaims cl jr N h b) := by
  classical
  obtain ⟨l1, l2, rfl, h1, h2⟩ := hok
  have hne : c ≠ (jr, N, h) := fun he => hj (by rw [he])
  refine ⟨replClaim (jr, N, h) (jr, N.diff [b], h.restrict jr (N.diff [b])) l1,
    replClaim (jr, N, h) (jr, N.diff [b], h.restrict jr (N.diff [b])) l2, ?_, ?_, ?_⟩
  · simp [dropClaims, replClaim, hne]
  · intro hm
    rcases mem_dropClaims (cl := l1) hm with he | ⟨hm, -⟩
    · exact hj (by rw [he])
    · exact h1 hm
  · intro hm
    rcases mem_dropClaims (cl := l2) hm with he | ⟨hm, -⟩
    · exact hj (by rw [he])
    · exact h2 hm

/-- **`DirKeysOk` carries over** (the keyed claims are of directories other than `jr`). -/
theorem dirKeysOk_drop {C : WalCodec} {Mr : WalMarshal} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {c : Option GoString} {N : NameSet} {h : NamesH}
    {b : GoString} (hd : DropOk cl jr N h b) (hbw : walNameP b = false) (hbn : ¬ walNameOk b)
    (hw : ∀ dir d, s.wal !! dir = some d → ∃ lay nm, Ls !! dir = some lay ∧ InArea s.area dir nm ∧
      lay.jr = jr ∧ lay.nm = nm)
    (hok : DirKeysOk C Mr jr s Ls cl n K c) : DirKeysOk C Mr jr s Ls (dropClaims cl jr N h b) n K c := by
  obtain ⟨h1, h2⟩ := hok
  refine ⟨fun dir j X hk => ?_, fun dir d lay hd' hl hc => ?_⟩
  · obtain ⟨lay, hj, hl, hlj, hjr, hX, ho, hco, hoth⟩ := h1 dir j X hk
    refine ⟨lay, hj, hl, hlj, hjr, hX, claimOnce_drop hjr ho, hco, fun c' hc' hne hj' => ?_⟩
    rcases mem_dropClaims hc' with he | ⟨hc', -⟩
    · exact absurd (by rw [← hj', he]) hjr
    · exact hoth c' hc' hne hj'
  · refine crashOkA_drop hd hbw ?_ (fun _ h0 => by cases h0) (h2 dir d lay hd' hl hc)
    obtain ⟨lay', nm, hl', hia, -, hnm⟩ := hw dir d hd'
    rw [hl] at hl'
    cases hl'
    rintro ⟨-, h2⟩
    exact hbn (h2 ▸ hnm ▸ hia.1)

end pure

end WalFs
end EtcdGrove
end Perennial

end
