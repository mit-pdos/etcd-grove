/- Lean-first (no Rocq counterpart).

# `Discard`'s step S: the invariant's pure facts (P6b state C, mit-pdos/etcd-grove#50;
`notes/wal-p6-handoff.md`, sessions 18-19)

At S (the area's fsync after `Discard`'s rename) the discarded WAL at `dir` leaves the real state
(`discS`), its layout leaves `Ls`, and its directory's claim `(J, N, hj)` (`J = lay.j`) leaves the
invariant's claims (`cl.erase`). A crash of the remaining claims is, with `J`'s names of `N` changed,
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

/-- **What dropping a WAL directory's claim `(j, N, h)` needs**: the claims one log's, the claim
among them, and no other claim of `j` on a name of `N`. -/
structure DropDirOk (cl : List Claim) (j : Ino) (N : NameSet) (h : NamesH) : Prop where
  log : ∃ log, Starts log ∧ ClaimsLog log cl
  mem : (j, N, h) ∈ cl
  others : ∀ c ∈ cl.erase (j, N, h), c.1 = j → ∀ b, N.Mem b → ¬ c.2.1.Mem b

theorem mem_cons_erase {c c' : Claim} {cl : List Claim} (h : c' ∈ cl) : c' ∈ c :: cl.erase c := by
  by_cases e : c' = c
  · subst e; exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne e).2 h)

/-- **A crash of the claims after the drop is, with `j`'s names of `N` changed, one before it.** -/
theorem DropDirOk.crash {cl : List Claim} {j : Ino} {N : NameSet} {h : NamesH}
    (hd : DropDirOk cl j N h) {n : Nat} {m' : Tree} (hr : RegionCrashed (cl.erase (j, N, h)) n m') :
    ∃ m'', RegionCrashed cl n m'' ∧ ∀ j' b, ¬ (j' = j ∧ N.Mem b) → m''.entry j' b = m'.entry j' b := by
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  obtain ⟨log, hst, hlog⟩ := hd.log
  have hlog' : ClaimsLog log ((j, N, h) :: cl.erase (j, N, h)) := fun c hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hlog _ hd.mem
    · exact hlog c (List.mem_of_mem_erase hc)
  obtain ⟨m'', h1, h2⟩ := regionCrashedK_dropDir hst hlog' hd.others hK
  exact ⟨m'', (regionCrashed_iff _ _ _).2 ⟨_, regionCrashedK_cover
    (fun c hc x e E hx => ⟨c, mem_cons_erase hc, E, hx⟩)
    (fun c hc b hb => ⟨c, mem_cons_erase hc, rfl, hb, fun _ => rfl⟩) h1⟩, h2⟩

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
    (hok : CrashOkA C Mr d lay alt cl n) : CrashOkA C Mr d lay alt (cl.erase (j, N, h)) n := by
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
    (hok : CrashOkW C Mr d lay cl n) : CrashOkW C Mr d lay (cl.erase (j, N, h)) n := by
  obtain ⟨alt, halt, hcr⟩ := hok
  refine ⟨alt, halt, crashOkA_dropDir hd hj hjr (fun lay0 h0 => ?_) hcr⟩
  obtain ⟨-, h1, h2, h3, -⟩ := halt lay0 h0
  exact ⟨h1, h2, h3⟩

/-- A claim of another directory stays among the claims. -/
theorem mem_erase_of_fst {cl : List Claim} {c c' : Claim} (hm : c' ∈ cl) (hne : c'.1 ≠ c.1) :
    c' ∈ cl.erase c :=
  (List.mem_erase_of_ne (fun e => hne (by rw [e]))).2 hm

theorem walDirClaim_dropDir {cl : List Claim} {j j' : Ino} {N : NameSet} {h hj : NamesH}
    (hne : j' ≠ j) (hw : WalDirClaim j' hj cl) : WalDirClaim j' hj (cl.erase (j, N, h)) := by
  obtain ⟨X, hX, hm, hco⟩ := hw
  exact ⟨X, hX, mem_erase_of_fst hm hne, hco⟩

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
    (hok : AbsentNone s jr cl n) : AbsentNone (discS s dir) jr (cl.erase (lay.j, N, hj)) n := by
  intro dir' nm hia hn
  have hia' : InArea s.area dir' nm := hia
  have key : (∀ N' h', (jr, N', h') ∈ cl → N'.Mem nm → h'.cur !! nm = none) ∧
      ∀ m', RegionCrashed cl n m' → m'.entry jr nm = none := by
    by_cases e : dir' = dir
    · subst e; exact hnone nm hia'
    · rw [discS_wal_ne e] at hn
      exact hok dir' nm hia' hn
  refine ⟨fun N' h' hm hN' => key.1 N' h' (List.mem_of_mem_erase hm) hN', fun m' hr => ?_⟩
  obtain ⟨m'', hr1, he⟩ := hs.drop.crash hr
  rw [← he _ _ (fun ⟨e, _⟩ => hs.jr e.symm)]
  exact key.2 _ hr1

/-- **`WalsOk` after the discard** (`hab`: `AbsentNone` after it, which gives `AbsentOk`). -/
theorem walsOk_discard {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString} {lay : WalLay}
    {N : NameSet} {hj : NamesH} (hs : DiscSet Ls cl jr dir lay N hj) (hR : RootsOk R) (hdr : DirsRoots R s)
    (hab : AbsentNone (discS s dir) jr (cl.erase (lay.j, N, hj)) n)
    (hok : WalsOk C Mr R jr s Ls cl n) :
    WalsOk C Mr R jr (discS s dir) (GMap.delete dir Ls) (cl.erase (lay.j, N, hj)) n := by
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

end pure

end WalFs
end EtcdGrove
end Perennial

end
