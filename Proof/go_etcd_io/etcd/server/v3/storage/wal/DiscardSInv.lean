/- Lean-first (no Rocq counterpart).

# `Discard`'s step S: the invariant's pure facts (P6b state C, mit-pdos/etcd-grove#50;
`notes/wal-p6-handoff.md`, sessions 18-19)

At S (the area's fsync after `Discard`'s rename) the discarded WAL at `dir` leaves the real state
(`discS`), its layout leaves `Ls`, and its directory's claim `(J, N, hj)` (`J = lay.j`) leaves the
invariant's claims (`dropC`). A crash of the remaining claims is, with `J`'s names of `N` changed,
one of all of them (`DropDirOk.crash`, over `regionCrashedK_dropDir`); every fact the invariant keeps
of the other WALs reads `J` nowhere: their directories are other inodes (`lay'.j ≠ J`: two layouts
never share a directory, `walTmpParked0_inj`, from the parked pipeline claims) and the area is not `J`.
Of `dir` itself the invariant then says it is absent (`AbsentNone`): its name holds nothing in the area
claim and after every crash (the rename, the name's last write, is below the raised commit bound; the
step shows it). The commit bound is raised first (`walsOk_mono`, ...), the drop is then at a fixed bound.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DiscardSPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DiscardR
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDropInv
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BootPure

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

open Classical in
/-- The claims `cl` without the claim `c` (once among them where it is used: `ClaimOnce`). -/
def dropC (cl : List Claim) (c : Claim) : List Claim := cl.filter (fun c' => decide (c' ≠ c))

theorem mem_dropC {cl : List Claim} {c c' : Claim} : c' ∈ dropC cl c ↔ c' ∈ cl ∧ c' ≠ c := by
  classical
  unfold dropC; simp [List.mem_filter]

theorem mem_of_mem_dropC {cl : List Claim} {c c' : Claim} (h : c' ∈ dropC cl c) : c' ∈ cl :=
  (mem_dropC.1 h).1

/-- **What dropping a WAL directory's claim `(j, N, h)` needs**: the claims one log's, the claim
among them, and no other claim of `j` on a name of `N`. -/
structure DropDirOk (cl : List Claim) (j : Ino) (N : NameSet) (h : NamesH) : Prop where
  log : ∃ log, Starts log ∧ ClaimsLog log cl
  mem : (j, N, h) ∈ cl
  others : ∀ c ∈ cl, c ≠ (j, N, h) → c.1 = j → ∀ b, N.Mem b → ¬ c.2.1.Mem b

theorem mem_cons_dropC {c c' : Claim} {cl : List Claim} (h : c' ∈ cl) : c' ∈ c :: dropC cl c := by
  by_cases e : c' = c
  · subst e; exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (mem_dropC.2 ⟨h, e⟩)

/-- **A crash of the claims after the drop is, with `j`'s names of `N` changed, one before it.** -/
theorem DropDirOk.crash {cl : List Claim} {j : Ino} {N : NameSet} {h : NamesH}
    (hd : DropDirOk cl j N h) {n : Nat} {m' : Tree} (hr : RegionCrashed (dropC cl (j, N, h)) n m') :
    ∃ m'', RegionCrashed cl n m'' ∧ ∀ j' b, ¬ (j' = j ∧ N.Mem b) → m''.entry j' b = m'.entry j' b := by
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  obtain ⟨log, hst, hlog⟩ := hd.log
  have hlog' : ClaimsLog log ((j, N, h) :: dropC cl (j, N, h)) := fun c hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hlog _ hd.mem
    · exact hlog c (mem_of_mem_dropC hc)
  obtain ⟨m'', h1, h2⟩ := regionCrashedK_dropDir hst hlog'
    (fun c hc => hd.others c (mem_of_mem_dropC hc) (mem_dropC.1 hc).2) hK
  exact ⟨m'', (regionCrashed_iff _ _ _).2 ⟨_, regionCrashedK_cover
    (fun c hc x e E hx => ⟨c, mem_cons_dropC hc, E, hx⟩)
    (fun c hc b hb => ⟨c, mem_cons_dropC hc, rfl, hb, fun _ => rfl⟩) h1⟩, h2⟩

/-- A directory other than `j` has the same entries in two trees equal off `j`'s names of `N`. -/
theorem entsOf_off {m1 m2 : Tree} {j j' : Ino} {N : NameSet} (hne : j' ≠ j)
    (he : ∀ j'' b, ¬ (j'' = j ∧ N.Mem b) → m1.entry j'' b = m2.entry j'' b) :
    entsOf m1 j' = entsOf m2 j' := by
  apply GMap.ext; intro b
  rw [entsOf_entry, entsOf_entry]
  exact he _ _ (fun ⟨e, _⟩ => hne e)

/-- **The discard's step**: the WAL in `dir` gone. -/
def discS (s : AbsDiskState) (dir : GoString) : AbsDiskState := { s with wal := GMap.delete dir s.wal }

theorem discS_wal_ne {s : AbsDiskState} {dir dir' : GoString} (h : dir' ≠ dir) :
    (discS s dir).wal !! dir' = s.wal !! dir' :=
  GMap.lookup_delete_ne _ (Ne.symm h)

theorem discS_wal_eq (s : AbsDiskState) (dir : GoString) : (discS s dir).wal !! dir = none :=
  GMap.lookup_delete_eq _ _

/-- The crash condition of a WAL of another directory carries over the drop. -/
theorem crashOkA_dropDir {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {alt : Option WalLay} {cl : List Claim} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    (hd : DropDirOk cl j N h) (hj : lay.j ≠ j) (hjr : lay.jr ≠ j)
    (halt : ∀ lay0, alt = some lay0 → lay0.jr = lay.jr ∧ lay0.nm = lay.nm ∧ lay0.j = lay.j)
    (hok : CrashOkA C Mr d lay alt cl n) : CrashOkA C Mr d lay alt (dropC cl (j, N, h)) n := by
  intro m' fo hr hf hn hw
  obtain ⟨m'', hr1, he⟩ := hd.crash hr
  have hents := entsOf_off hj he
  have hent : m''.entry lay.jr lay.nm = m'.entry lay.jr lay.nm :=
    he _ _ (fun ⟨e, _⟩ => hjr e)
  have hwi : walInos (entsOf m'' lay.j) = walInos (entsOf m' lay.j) := by rw [hents]
  rcases hok _ fo hr1 hf (fun g hg hin => hn g hg (by rw [← hwi]; exact hin)) (by rw [hwi]; exact hw)
    with hct | ⟨lay0, h0, hct⟩
  · exact Or.inl (crashTo_congr hent hwi hct)
  · obtain ⟨h1, h2, h3⟩ := halt lay0 h0
    refine Or.inr ⟨lay0, h0, crashTo_congr ?_ (by rw [h3]; exact hwi) hct⟩
    rw [h1, h2]; exact hent

theorem crashOkW_dropDir {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    (hd : DropDirOk cl j N h) (hj : lay.j ≠ j) (hjr : lay.jr ≠ j)
    (hok : CrashOkW C Mr d lay cl n) : CrashOkW C Mr d lay (dropC cl (j, N, h)) n := by
  obtain ⟨alt, halt, hcr⟩ := hok
  refine ⟨alt, halt, crashOkA_dropDir hd hj hjr (fun lay0 h0 => ?_) hcr⟩
  obtain ⟨-, h1, h2, h3, -⟩ := halt lay0 h0
  exact ⟨h1, h2, h3⟩

/-- A claim of another directory stays among the claims. -/
theorem mem_dropC_of_fst {cl : List Claim} {c c' : Claim} (hm : c' ∈ cl) (hne : c'.1 ≠ c.1) :
    c' ∈ dropC cl c :=
  mem_dropC.2 ⟨hm, fun e => hne (by rw [e])⟩

theorem walDirClaim_dropDir {cl : List Claim} {j j' : Ino} {N : NameSet} {h hj : NamesH}
    (hne : j' ≠ j) (hw : WalDirClaim j' hj cl) : WalDirClaim j' hj (dropC cl (j, N, h)) := by
  obtain ⟨X, hX, hm, hco⟩ := hw
  exact ⟨X, hX, mem_dropC_of_fst (c := (j, N, h)) hm hne, hco⟩

/-- **The setting of the drop** (the facts every lemma below needs): the discarded WAL's layout `lay`
at `dir`, its directory claim's drop allowed, every other layout of another directory, and its
directory not the area's. -/
structure DiscSet (Ls : GMap GoString WalLay) (cl : List Claim) (jr : Ino) (dir : GoString)
    (lay : WalLay) (N : NameSet) (hj : NamesH) : Prop where
  hl : Ls !! dir = some lay
  drop : DropDirOk cl lay.j N hj
  dist : ∀ dir' lay', Ls !! dir' = some lay' → dir' ≠ dir → lay'.j ≠ lay.j
  jr : lay.j ≠ jr

/-- **`AbsentNone` after the discard**: of the other absent WALs as before (the area is not `J`); of
`dir`, from `hnone` (its name holds nothing in the area's claims, nor after a crash). -/
theorem absentNone_discard {s : AbsDiskState} {jr : Ino} {Ls : GMap GoString WalLay} {cl : List Claim}
    {n : Nat} {dir : GoString} {lay : WalLay} {N : NameSet} {hj : NamesH}
    (hs : DiscSet Ls cl jr dir lay N hj)
    (hnone : ∀ nm, InArea s.area dir nm →
      (∀ N' h', (jr, N', h') ∈ cl → N'.Mem nm → h'.cur !! nm = none) ∧
      ∀ m', RegionCrashed cl n m' → m'.entry jr nm = none)
    (hok : AbsentNone s jr cl n) : AbsentNone (discS s dir) jr (dropC cl (lay.j, N, hj)) n := by
  intro dir' nm hia hn
  have hia' : InArea s.area dir' nm := hia
  have key : (∀ N' h', (jr, N', h') ∈ cl → N'.Mem nm → h'.cur !! nm = none) ∧
      ∀ m', RegionCrashed cl n m' → m'.entry jr nm = none := by
    by_cases e : dir' = dir
    · subst e; exact hnone nm hia'
    · rw [discS_wal_ne e] at hn
      exact hok dir' nm hia' hn
  refine ⟨fun N' h' hm hN' => key.1 N' h' (mem_of_mem_dropC hm) hN', fun m' hr => ?_⟩
  obtain ⟨m'', hr1, he⟩ := hs.drop.crash hr
  rw [← he _ _ (fun ⟨e, _⟩ => hs.jr e.symm)]
  exact key.2 _ hr1

/-- **`WalsOk` after the discard** (`hab`: `AbsentNone` after it, which gives `AbsentOk`). -/
theorem walsOk_discard {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString} {lay : WalLay}
    {N : NameSet} {hj : NamesH} (hs : DiscSet Ls cl jr dir lay N hj) (hR : RootsOk R) (hdr : DirsRoots R s)
    (hab : AbsentNone (discS s dir) jr (dropC cl (lay.j, N, hj)) n)
    (hok : WalsOk C Mr R jr s Ls cl n) :
    WalsOk C Mr R jr (discS s dir) (GMap.delete dir Ls) (dropC cl (lay.j, N, hj)) n := by
  obtain ⟨hw, hnone, hnd, hcut, -, -⟩ := hok
  have hLd : ∀ dir', dir' ≠ dir → (GMap.delete dir Ls) !! dir' = Ls !! dir' :=
    fun dir' e => GMap.lookup_delete_ne _ (Ne.symm e)
  have hsub : ∀ g ∈ segsAll (GMap.delete dir Ls), g ∈ segsAll Ls := fun g hg => by
    obtain ⟨dir', lay', hl', hg'⟩ := segsAll_mem hg
    by_cases e : dir' = dir
    · subst e; rw [GMap.lookup_delete_eq] at hl'; cases hl'
    · rw [hLd _ e] at hl'; exact mem_segsAll_all hl' hg'
  refine ⟨fun dir' d hd' => ?_, fun dir' hn' => ?_, ?_, fun g hg => hcut g (hsub g hg),
    absentOk_of_absentNone hab, dirsOk_roots hR (hdr.congr rfl) _ _⟩
  · have e : dir' ≠ dir := fun e => by rw [e, discS_wal_eq] at hd'; cases hd'
    rw [discS_wal_ne e] at hd'
    obtain ⟨lay', nm, hj', hl', hia, hjr, hnm, hwd, habs, hco⟩ := hw dir' d hd'
    have hne := hs.dist dir' lay' hl' e
    have hjr' : lay'.jr ≠ lay.j := fun h => hs.jr (by rw [← h, hjr])
    refine ⟨lay', nm, hj', by rw [hLd _ e]; exact hl', hia, hjr, hnm, walDirClaim_dropDir hne hwd,
      habs, hco.1, ?_, hco.2.2⟩
    exact crashOkW_dropDir hs.drop (by exact hne) hjr' hco.2.1
  · by_cases e : dir' = dir
    · subst e; exact GMap.lookup_delete_eq _ _
    · rw [discS_wal_ne e] at hn'; rw [hLd _ e]; exact hnone dir' hn'
  · exact segsAll_nodup_sub hnd (fun dir' lay' hl' => by
      by_cases e : dir' = dir
      · subst e; rw [GMap.lookup_delete_eq] at hl'; cases hl'
      · rw [hLd _ e] at hl'; exact ⟨lay', hl', List.Sublist.refl _⟩)


/-- **`WalsNamed` after the discard.** -/
theorem walsNamed_discard {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {jr : Ino}
    {dir : GoString} {lay : WalLay} {N : NameSet} {hj : NamesH} (hs : DiscSet Ls cl jr dir lay N hj)
    (hok : WalsNamed Ls cl n) : WalsNamed (GMap.delete dir Ls) (dropC cl (lay.j, N, hj)) n := by
  intro dir' lay' hl'
  have e : dir' ≠ dir := fun e => by rw [e, GMap.lookup_delete_eq] at hl'; cases hl'
  rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hl'
  have hne := hs.dist dir' lay' hl' e
  obtain ⟨h1, h2, h3⟩ := hok dir' lay' hl'
  refine ⟨fun hj' hw => h1 hj' ?_, fun m' hr => ?_, fun N' hj' hm => h3 N' hj' (mem_of_mem_dropC hm)⟩
  · obtain ⟨X, hX, hm, hco⟩ := hw
    exact ⟨X, hX, mem_of_mem_dropC hm, hco⟩
  · obtain ⟨m'', hr1, he⟩ := hs.drop.crash hr
    rw [← entsOf_off hne he]
    exact h2 _ hr1

/-- **`WalsCreateOk` after the discard** (the area's claims stay). -/
theorem walsCreateOk_discard {jr : Ino} {cl : List Claim} {j : Ino} {N : NameSet} {hj : NamesH}
    (hjr : j ≠ jr) (hok : WalsCreateOk jr cl) : WalsCreateOk jr (dropC cl (j, N, hj)) := by
  intro nm hnm
  obtain ⟨N', h', hm, hN'⟩ := hok nm hnm
  exact ⟨N', h', mem_dropC_of_fst (c := (j, N, hj)) hm (Ne.symm hjr), hN'⟩

/-- **`WalsAt` after the discard.** -/
theorem walsAt_discard {jr : Ino} {Ls : GMap GoString WalLay} {cl : List Claim} {dir : GoString}
    {c : Claim} (hA : WalsAt jr Ls cl) : WalsAt jr (GMap.delete dir Ls) (dropC cl c) := by
  intro dir' lay' hl'
  have e : dir' ≠ dir := fun e => by rw [e, GMap.lookup_delete_eq] at hl'; cases hl'
  rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hl'
  exact ⟨(hA dir' lay' hl').1, fun N h hm hN => (hA dir' lay' hl').2 N h (mem_of_mem_dropC hm) hN⟩

/-- `ClaimOnce` of another claim carries over the drop. -/
theorem claimOnce_dropC {cl : List Claim} {c c' : Claim} (hne : c' ≠ c) (h : ClaimOnce c' cl) :
    ClaimOnce c' (dropC cl c) := by
  classical
  obtain ⟨l1, l2, rfl, h1, h2⟩ := h
  refine ⟨dropC l1 c, dropC l2 c, ?_, fun hm => h1 (mem_of_mem_dropC hm),
    fun hm => h2 (mem_of_mem_dropC hm)⟩
  unfold dropC
  rw [List.filter_append, List.filter_cons_of_pos (by simpa using hne)]

/-- A WAL directory's claim facts of another directory carry over the drop. -/
theorem dirClaimOk_dropC {jr : Ino} {cl : List Claim} {j j' : Ino} {X : List GoString} {hj : NamesH}
    {c : Claim} (hc : c.1 = j') (hne : j ≠ j') (h : DirClaimOk jr cl j X hj) :
    DirClaimOk jr (dropC cl c) j X hj := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, claimOnce_dropC (fun e => hne (by rw [← hc, ← e])) h3, h4,
    fun c'' hc'' => h5 c'' (mem_of_mem_dropC hc'')⟩

/-- **`DirKeysOk` after the discard**, its keys less `dir`'s. -/
theorem dirKeysOk_discard {C : WalCodec} {Mr : WalMarshal} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {cu : Option GoString} {dir : GoString} {lay : WalLay}
    {N : NameSet} {hj : NamesH} (hs : DiscSet Ls cl jr dir lay N hj)
    (hw : ∀ dir' d, s.wal !! dir' = some d → ∃ lay', Ls !! dir' = some lay' ∧ lay'.jr = jr)
    (hok : DirKeysOk C Mr jr s Ls cl n K cu) :
    DirKeysOk C Mr jr (discS s dir) (GMap.delete dir Ls) (dropC cl (lay.j, N, hj)) n
      (GMap.delete dir K) cu := by
  obtain ⟨h1, h2, h3⟩ := hok
  have hL : ∀ dir' lay', (GMap.delete dir Ls) !! dir' = some lay' → dir' ≠ dir ∧ Ls !! dir' = some lay' :=
    fun dir' lay' hl' => by
      have e : dir' ≠ dir := fun e => by rw [e, GMap.lookup_delete_eq] at hl'; cases hl'
      rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hl'
      exact ⟨e, hl'⟩
  refine ⟨fun dir' j X hk => ?_, fun dir' d lay' hd' hl' hcd => ?_, fun dir' lay' hl' => ?_⟩
  · have e : dir' ≠ dir := fun e => by rw [e, GMap.lookup_delete_eq] at hk; cases hk
    rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hk
    obtain ⟨lay', hj', hl', hlj, hjr, hX, ho, hco, hoth⟩ := h1 dir' j X hk
    have hne : j ≠ lay.j := hlj ▸ hs.dist dir' lay' hl' e
    obtain ⟨-, -, ho', -, hoth'⟩ := dirClaimOk_dropC (c := (lay.j, N, hj)) rfl hne
      ⟨hjr, hX, ho, hco, hoth⟩
    refine ⟨lay', hj', by rw [GMap.lookup_delete_ne _ (Ne.symm e)]; exact hl', hlj, hjr, hX, ho', hco,
      hoth'⟩
  · obtain ⟨e, hl'⟩ := hL dir' lay' hl'
    rw [discS_wal_ne e] at hd'
    have hne := hs.dist dir' lay' hl' e
    have hjr' : lay'.jr ≠ lay.j := by
      obtain ⟨lay2, hl2, hjr2⟩ := hw dir' d hd'
      rw [hl'] at hl2; cases hl2
      rw [hjr2]; exact Ne.symm hs.jr
    exact crashOkA_dropDir hs.drop (by simpa using hne) (by simpa using hjr')
      (fun _ h0 => by cases h0) (h2 dir' d lay' hd' hl' hcd)
  · obtain ⟨e, hl'⟩ := hL dir' lay' hl'
    have hne := hs.dist dir' lay' hl' e
    obtain ⟨X, hj', hok', ⟨hXe, hex⟩⟩ := h3 dir' lay' hl'
    exact ⟨X, hj', dirClaimOk_dropC (c := (lay.j, N, hj)) rfl hne hok', hXe,
      fun c'' hc'' => hex c'' (mem_of_mem_dropC hc'')⟩


/-- **The setting of the drop, from the invariant**: the discarded WAL's directory claim is
`(lay.j, .except walTmps, hj)` (`DirClaimsOk`), its drop allowed (`DirClaimExcl`), given the claims'
log (`osClaims_log`) and that two layouts never share a directory (`walTmpParked0_inj`). -/
theorem discSet_of {C : WalCodec} {Mr : WalMarshal} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {K : GMap GoString (Ino × List GoString)}
    {cu : Option GoString} {dir : GoString} {lay : WalLay} (hl : Ls !! dir = some lay)
    (hlog : ∃ log, Starts log ∧ ClaimsLog log cl)
    (hdist : ∀ (dir1 dir2 : GoString) (l1 l2 : WalLay), Ls !! dir1 = some l1 → Ls !! dir2 = some l2 →
      dir1 ≠ dir2 → l1.j ≠ l2.j)
    (hk : DirKeysOk C Mr jr s Ls cl n K cu) :
    ∃ hj, DiscSet Ls cl jr dir lay (.except walTmps) hj := by
  obtain ⟨X, hj, hok, hXe, hex⟩ := hk.2.2 dir lay hl
  subst hXe
  obtain ⟨hjr, -, ⟨l1, l2, hcl, -, -⟩, -, -⟩ := hok
  exact ⟨hj, ⟨hl, ⟨hlog, by rw [hcl]; simp, hex⟩,
    fun d' l' hl' hne => hdist d' dir l' lay hl' hl hne, hjr⟩⟩

/-- **`dir`'s name holds nothing, in the claims and after a crash** (`absentNone_discard`'s `hnone`):
the one claim of the area on `nm` (`honly`, the shared invariant's disjointness) holds nothing there,
and its last write of `nm` (the rename) is below the commit bound. -/
theorem discNone_of {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat} {dir nm : GoString}
    (hia : InArea s.area dir nm) {N0 : NameSet} {hC : NamesH} (hc : (jr, N0, hC) ∈ cl)
    (hN : N0.Mem nm) (honly : ∀ N' h', (jr, N', h') ∈ cl → N'.Mem nm → h' = hC)
    (hcur : hC.cur !! nm = none) {x : Nat} {e : LogEntry} {Es : Ents}
    (hlw : LastWrite hC jr nm x e Es) (hx : x < n) (hEs : Es !! nm = none) :
    ∀ nm', InArea s.area dir nm' →
      (∀ N' h', (jr, N', h') ∈ cl → N'.Mem nm' → h'.cur !! nm' = none) ∧
      ∀ m', RegionCrashed cl n m' → m'.entry jr nm' = none := by
  intro nm' hia'
  have e := inArea_nm_inj hia hia'
  subst e
  refine ⟨fun N' h' hm hN' => by rw [honly N' h' hm hN']; exact hcur, fun m' hr => ?_⟩
  rw [regionCrashed_lastWrite hc hN hlw hx hr]; exact hEs

/-- **S's pure facts** (the invariant's at the raised commit bound `n`, past the rename): the WAL in
`dir` gone, its layout and its directory claim dropped, its keys out. -/
theorem discS_pure {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n0 n : Nat}
    {K : GMap GoString (Ino × List GoString)} {cu : Option GoString} {dir : GoString} {lay : WalLay}
    {N : NameSet} {hj : NamesH} (hn : n0 ≤ n) (hs : DiscSet Ls cl jr dir lay N hj) (hR : RootsOk R)
    (hnone : ∀ nm, InArea s.area dir nm →
      (∀ N' h', (jr, N', h') ∈ cl → N'.Mem nm → h'.cur !! nm = none) ∧
      ∀ m', RegionCrashed cl n m' → m'.entry jr nm = none)
    (hwo : WalsOk C Mr R jr s Ls cl n0) (hwc : WalsCreateOk jr cl)
    (hab : AbsentNone s jr cl n0 ∧ DirsAvoid R jr s) (hwn : WalsNamed Ls cl n0)
    (hk : DirKeysOk C Mr jr s Ls cl n0 K cu) (hA : WalsAt jr Ls cl)
    (hbd : WalsBounded s ∧ DirsRoots R s) :
    WalsOk C Mr R jr (discS s dir) (GMap.delete dir Ls) (dropC cl (lay.j, N, hj)) n ∧
      WalsCreateOk jr (dropC cl (lay.j, N, hj)) ∧
      (AbsentNone (discS s dir) jr (dropC cl (lay.j, N, hj)) n ∧ DirsAvoid R jr (discS s dir)) ∧
      WalsNamed (GMap.delete dir Ls) (dropC cl (lay.j, N, hj)) n ∧
      DirKeysOk C Mr jr (discS s dir) (GMap.delete dir Ls) (dropC cl (lay.j, N, hj)) n
        (GMap.delete dir K) cu ∧
      WalsAt jr (GMap.delete dir Ls) (dropC cl (lay.j, N, hj)) ∧
      (WalsBounded (discS s dir) ∧ DirsRoots R (discS s dir)) := by
  have hwo := walsOk_mono hn hwo
  have hab1 := absentNone_discard hs hnone (absentNone_mono hn hab.1)
  have hw : ∀ dir' d, s.wal !! dir' = some d → ∃ lay', Ls !! dir' = some lay' ∧ lay'.jr = jr :=
    fun dir' d hd => let ⟨lay', _, _, hl', _, hjr, _⟩ := hwo.1 dir' d hd; ⟨lay', hl', hjr⟩
  refine ⟨walsOk_discard hs hR hbd.2 hab1 hwo, walsCreateOk_discard hs.jr hwc, ⟨hab1, hab.2⟩,
    walsNamed_discard hs (walsNamed_mono hn hwn), dirKeysOk_discard hs hw (dirKeysOk_mono hn hk),
    walsAt_discard hA, ⟨hbd.1.mono fun dir' d' hd' => ?_, hbd.2.congr rfl⟩⟩
  by_cases e : dir' = dir
  · subst e; rw [discS_wal_eq] at hd'; cases hd'
  · rw [discS_wal_ne e] at hd'; exact ⟨d', hd', rfl, rfl⟩

end pure


section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A resource per segment, a layout removed** (S: the discarded WAL's segments' halves dropped from
`laysResF` and `walParked`'s `segResP`s). -/
theorem segsAll_sep_delete (Φ : SegG → IProp GF) (Ls : GMap GoString WalLay) (dir : GoString)
    (lay : WalLay) (hl : Ls !! dir = some lay) :
    ([∗list] x ∈ segsAll Ls, Φ x) ⊢
      ([∗list] x ∈ lay.pg ++ lay.segs, Φ x) ∗ [∗list] x ∈ segsAll (GMap.delete dir Ls), Φ x := by
  refine (segsAll_sep_map Φ Ls).1.trans ?_
  refine (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] x ∈ lay.pg ++ lay.segs, Φ x)) hl).1.trans ?_
  exact sep_mono .rfl (segsAll_sep_map Φ _).2

/-- **The tails with the discarded WAL removed** (S): with no tail registered (the free lock token's
`walTailsFrag ∅`) every WAL is idle, so its record goes with its layout; nothing is lent either. -/
theorem walTailsRes_discard {Lk : GMap GoString Nat} (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (F : GMap Ino SegFl) (dir : GoString) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailsFrag (W := W) ∅ Lk -∗
      walTailsRes (W := W) C Mr (discS s dir) (GMap.delete dir Ls) F ∗ walTailsFrag (W := W) ∅ Lk := by
  unfold walTailsRes
  letI := walAllG (W := W)
  iintro ⟨%T, Ha, %Ho, %Hi, -, HL⟩ Hf
  icases walTails_agree (W := W) T ∅ $$ Ha Hf with %hT
  subst hT
  iframe Hf
  iexists ∅
  iframe Ha
  isplitr
  · ipureintro
    intro i hi
    exact absurd (Ho.none_of_empty i) hi
  isplitr
  · ipureintro
    intro k d la hk hd hla
    by_cases e : k = dir
    · subst e; rw [GMap.lookup_delete_eq] at hla; cases hla
    · rw [discS_wal_ne e] at hd
      rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hla
      exact Hi k d la hk hd hla
  isplitr
  · iapply BigSepM.bigSepM_empty.2; itrivial
  unfold walLentRes
  icases HL with ⟨%M, Hla, %HZ, %HI, Hm⟩
  iexists M
  iframe Hla
  isplitr
  · ipureintro
    intro k la hk
    exact absurd (GMap.lookup_empty k) hk
  isplitr
  · ipureintro
    intro k la hk hla
    by_cases e : k = dir
    · subst e; rw [GMap.lookup_delete_eq] at hla; cases hla
    · rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hla
      exact HI k la hk hla
  iapply BigSepM.bigSepM_mono_of_forall _ $$ Hm
  intro k x
  iintro ⟨%h, Hk⟩
  iframe Hk
  ipureintro
  exact absurd h.1 (by simp)

/-- Both pipeline names of one directory, twice: impossible (two `qTmp`s of `0.tmp`'s claim). -/
theorem walTmpsRes_excl (j : Ino) :
    walTmpsRes (hG := ⟨G, L⟩) j ∗ walTmpsRes (hG := ⟨G, L⟩) j ⊢ iprop(False) := by
  unfold walTmpsRes walTmps
  iintro ⟨H1, H2⟩
  icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨H1, -⟩
  icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨H2, -⟩
  unfold tmpClaim
  icases H1 with ⟨%h1, H1, -⟩
  icases H2 with ⟨%h2, H2, -⟩
  rw [osNames_of_ne _ _ (by simp : NameSet.only [go!"0.tmp"] ≠ .only []),
    osNames_of_ne _ _ (by simp : NameSet.only [go!"0.tmp"] ≠ .only [])]
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %hv
  exact (qTmp_two hv.1).elim

/-- **Two layouts never share a directory** (the coordinator's route, session 19): with no write-mode
handle out (`T = []`), the parked pipeline names hold, for each layout's directory, both its names'
claims (`walTmpsRes`), at three quarters each; two layouts on one directory would hold two. -/
theorem walTmpParked0_inj (Ls : GMap GoString WalLay) :
    walTmpParked0 (G := G) (L := L) Ls [] ⊢
      ⌜∀ dir1 dir2 (l1 l2 : WalLay), Ls !! dir1 = some l1 → Ls !! dir2 = some l2 → dir1 ≠ dir2 →
        l1.j ≠ l2.j⌝ ∗ walTmpParked0 (G := G) (L := L) Ls [] := by
  classical
  by_cases hP : ∃ (d1 d2 : GoString) (l1 l2 : WalLay), Ls !! d1 = some l1 ∧ Ls !! d2 = some l2 ∧ d1 ≠ d2 ∧
      l1.j = l2.j
  rotate_left
  · iintro H; iframe H; ipureintro
    intro d1 d2 l1 l2 h1 h2 hne hj
    exact hP ⟨d1, d2, l1, l2, h1, h2, hne, hj⟩
  · obtain ⟨d1, d2, l1, l2, h1, h2, hne, hj⟩ := hP
    unfold walTmpParked0
    iintro ⟨%Jt, %hp, Hm⟩
    iexfalso
    have e1 : Jt !! d1 = some l2.j := by rw [← hj]; exact hp d1 l1 h1
    have e2 : (GMap.delete d1 Jt) !! d2 = some l2.j := by
      rw [GMap.lookup_delete_ne _ hne]; exact hp d2 l2 h2
    ihave Hm := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (J : Ino) =>
      iprop(if dir ∈ ([] : List GoString) then emp else walTmpsRes (hG := ⟨G, L⟩) J)) e1).1 $$ Hm
    icases Hm with ⟨H1, Hm⟩
    ihave Hm := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (J : Ino) =>
      iprop(if dir ∈ ([] : List GoString) then emp else walTmpsRes (hG := ⟨G, L⟩) J)) e2).1 $$ Hm
    icases Hm with ⟨H2, -⟩
    simp only [List.not_mem_nil, ite_false]
    iapply walTmpsRes_excl (G := G) (L := L) l2.j
    iframe H1 H2

/-- **The discarded WAL's pipeline names out of the parked ones** (S, the lock free: `T = []`): both
names' whole claims (`walTmpsRes lay.j`) to the program. -/
theorem walTmpParked0_delete (Ls : GMap GoString WalLay) (dir : GoString) (lay : WalLay)
    (hl : Ls !! dir = some lay) :
    walTmpParked0 (G := G) (L := L) Ls [] ⊢
      walTmpsRes (hG := ⟨G, L⟩) lay.j ∗ walTmpParked0 (G := G) (L := L) (GMap.delete dir Ls) [] := by
  unfold walTmpParked0
  iintro ⟨%Jt, %hp, Hm⟩
  ihave Hm := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (J : Ino) =>
    iprop(if dir ∈ ([] : List GoString) then emp else walTmpsRes (hG := ⟨G, L⟩) J)) (hp dir lay hl)).1 $$ Hm
  icases Hm with ⟨H1, Hm⟩
  simp only [List.not_mem_nil, ite_false]
  iframe H1
  iexists GMap.delete dir Jt
  iframe Hm
  ipureintro
  intro k la hk
  by_cases e : k = dir
  · subst e; rw [GMap.lookup_delete_eq] at hk; cases hk
  · rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hk ⊢
    exact hp k la hk

/-- **The discarded WAL's pipeline names' invariant halves out** (S). -/
theorem walTmpHalves_delete (Ls : GMap GoString WalLay) (dir : GoString) (lay : WalLay)
    (hl : Ls !! dir = some lay) :
    walTmpHalves (G := G) (L := L) Ls ⊢
      walTmpsHalf (hG := ⟨G, L⟩) lay.j ∗ walTmpHalves (G := G) (L := L) (GMap.delete dir Ls) := by
  unfold walTmpHalves
  iintro ⟨%Jh, %hp, Hm⟩
  ihave Hm := (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (J : Ino) =>
    walTmpsHalf (hG := ⟨G, L⟩) J) (hp dir lay hl)).1 $$ Hm
  icases Hm with ⟨H1, Hm⟩
  iframe H1
  iexists GMap.delete dir Jh
  iframe Hm
  ipureintro
  intro k la hk
  by_cases e : k = dir
  · subst e; rw [GMap.lookup_delete_eq] at hk; cases hk
  · rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hk ⊢
    exact hp k la hk

/-- A layout removed: a claim no WAL directory's of the remaining layouts was one before. -/
theorem walDirClaimOf_delete {Ls : GMap GoString WalLay} {dir : GoString} {c : Claim}
    (h : WalDirClaimOf (GMap.delete dir Ls) c) : WalDirClaimOf Ls c := by
  obtain ⟨d, l, hl, rest⟩ := h
  by_cases e : d = dir
  · subst e; rw [GMap.lookup_delete_eq] at hl; cases hl
  · rw [GMap.lookup_delete_ne _ (Ne.symm e)] at hl; exact ⟨d, l, hl, rest⟩

/-- A parked claim's half, a layout removed (parked then, or dropped). -/
theorem claimP_deleteL {Ls : GMap GoString WalLay} {D : List (Ino × NameSet)} (dir : GoString) (c : Claim) :
    (if ParkedClaim Ls D c then osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp :
        IProp GF) ⊢
      if ParkedClaim (GMap.delete dir Ls) D c then
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp := by
  by_cases h' : ParkedClaim (GMap.delete dir Ls) D c
  · have h0 : ParkedClaim Ls D c := ⟨walDirClaimOf_delete h'.1, h'.2⟩
    simp only [h', h0, ↓reduceIte]; exact .rfl
  · simp only [h', ↓reduceIte]; iintro -; iempintro

/-- A claim's others, a layout removed (kept, or dropped). -/
theorem othersP_deleteL {Ls : GMap GoString WalLay} {D : List (Ino × NameSet)} (dir : GoString) (c : Claim) :
    (if WalDirClaimOf Ls c then walOthers (L := L) D c.1 c.2.2.cur else emp : IProp GF) ⊢
      if WalDirClaimOf (GMap.delete dir Ls) c then walOthers (L := L) D c.1 c.2.2.cur else emp := by
  by_cases h' : WalDirClaimOf (GMap.delete dir Ls) c
  · simp only [h', walDirClaimOf_delete h', ↓reduceIte]; exact .rfl
  · simp only [h', ↓reduceIte]; iintro -; iempintro

/-- **The discarded WAL out of the parked state** (S, the lock free: the record of what is out empty):
its directory claim's parked half, its pipeline names' claims (`walTmpsRes`) and invariant halves
(`walTmpsHalf`), and its directory's others; its segments' program halves dropped. -/
theorem walParked_discard (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (dir : GoString) (lay : WalLay) (c : Claim) (hl : Ls !! dir = some lay)
    (hW : WalDirClaimOf Ls c) (honce : ClaimOnce c cl) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walOutFrag (W := W) WalOut.empty -∗
      walParked (L := L) (W := W) (GMap.delete dir Ls) (dropC cl c) F ∗ walOutFrag (W := W) WalOut.empty ∗
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 ∗
        walTmpsRes (hG := ⟨G, L⟩) lay.j ∗ walTmpsHalf (hG := ⟨G, L⟩) lay.j ∗
        walOthers (L := L) [] c.1 c.2.2.cur := by
  classical
  obtain ⟨l1, l2, hcl, -, -, hf⟩ := filter_ne_once honce
  have hd : dropC cl c = l1 ++ l2 := hf
  rw [hd]
  subst hcl
  unfold walParked
  iintro ⟨%b, %o, Hpa, Hoa, %hp, Hs, Hc, Ht, Hw⟩ Ho
  icases walOut_agree (W := W) o _ $$ Hoa Ho with %ho
  subst ho
  have hT : WalOut.empty.T = [] := rfl
  have hD : WalOut.empty.D = [] := rfl
  simp only [hT, hD]
  ihave Hs := segsAll_sep_delete
    (fun g => iprop(if g.ino ∈ WalOut.empty.O then emp else segResP (L := L) g)) Ls dir lay hl $$ Hs
  icases Hs with ⟨-, Hs⟩
  unfold walTmpParked
  icases Ht with ⟨Ht0, Hth⟩
  ihave Ht0 := walTmpParked0_delete Ls dir lay hl $$ Ht0
  icases Ht0 with ⟨Htr, Ht0⟩
  ihave Hth := walTmpHalves_delete Ls dir lay hl $$ Hth
  icases Hth with ⟨Hhf, Hth⟩
  icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hc with ⟨Hc1, Hc2⟩
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hc2 with ⟨Hcc, Hc2⟩
  unfold walOthersL
  icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hw with ⟨Hw1, Hw2⟩
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hw2 with ⟨Hwc, Hw2⟩
  have hP : ParkedClaim Ls [] c := ⟨hW, by simp⟩
  simp only [hP, hW, ↓reduceIte]
  iframe Ho Hcc Htr Hhf Hwc
  iexists b, WalOut.empty
  simp only [hT, hD]
  iframe Hpa Hoa Hs Ht0 Hth
  isplitr
  · ipureintro; exact hp
  isplitl [Hc1 Hc2]
  · iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
    isplitl [Hc1]
    · iapply BigSepL.bigSepL_mono (fun {k x} _ => claimP_deleteL (L := L) dir x) $$ Hc1
    · iapply BigSepL.bigSepL_mono (fun {k x} _ => claimP_deleteL (L := L) dir x) $$ Hc2
  iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
  isplitl [Hw1]
  · iapply BigSepL.bigSepL_mono (fun {k x} _ => othersP_deleteL (L := L) dir x) $$ Hw1
  · iapply BigSepL.bigSepL_mono (fun {k x} _ => othersP_deleteL (L := L) dir x) $$ Hw2

end iris

end WalFs
end EtcdGrove
end Perennial

end
