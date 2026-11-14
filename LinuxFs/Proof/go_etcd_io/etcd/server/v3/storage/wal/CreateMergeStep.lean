/- Lean-first (no Rocq counterpart).

# `Create`'s steps on the area claims (W4, `notes/wal-fsext-plan.md`, "W4 implementation log", tenth
session)

Ghost steps with the WAL invariant's contents and the file system's shared invariant open:

* `walInvBody_merge2`: the program's halves of two area claims (each the invariant's other half, found
  through a WAL name it holds, `WalsCreateOk`) merged into one, the invariant's halves too: after the
  commit (the area claim off `nm` and the renamed creating claim) and after an abort past the minting.
* `walInvBody_mergeIn`: the program's half of an area claim and a whole claim of the area holding no
  WAL name (`nm.tmp`'s, the invariant holding none of it) merged: an abort before the minting.
* `walInvBody_mint`: the creating token (`walCreating`), `nm` split off the area claim and merged with
  `nm.tmp`'s into the creating claim `.only [nm, nm.tmp]` (`CreatingOk`'s facts: the shared
  invariant's, `osClaims_keys`, `osNames_coh`).
* `walInvBody_unmint`: the creating entry deleted, the free lock token back (an abort).

The invariant's claims change by covering (`CreateMerge.lean`); the creating map is empty at the
merges (the program holds a lock token, which a non-empty map holds the free one of).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateMerge
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateCoh
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDropStep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

theorem filter_replClaim (q : Claim → Bool) {c0 c1 : Claim} (h0 : q c0 = false) (h1 : q c1 = false)
    (l : List Claim) : (replClaim c0 c1 l).filter q = l.filter q := by
  classical
  unfold replClaim
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons, ih]
    by_cases hx : x = c0
    · subst hx; simp [h0, h1]
    · simp [hx]

theorem filter_mergeClaims (q : Claim → Bool) {c1 c2 c : Claim} (h1 : q c1 = false)
    (h2 : q c2 = false) (hc : q c = false) (cl : List Claim) :
    (mergeClaims cl c1 c2 c).filter q = cl.filter q := by
  classical
  unfold mergeClaims
  rw [filter_replClaim q h1 hc, List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases hx : x = c2
  · subst hx; simp [h2]
  · simp [hx]

theorem filter_mintClaims (q : Claim → Bool) {jr : Ino} {N : NameSet} {h : NamesH}
    {nm tmp : GoString} {hC : NamesH} (hq : ∀ N' h', q (jr, N', h') = false) (cl : List Claim) :
    (mintClaims cl jr N h nm tmp hC).filter q = cl.filter q := by
  unfold mintClaims
  rw [List.filter_append, filter_replClaim q (hq _ _) (hq _ _)]
  simp [hq]

open Classical in
/-- A claim found once, the list without it. -/
theorem filter_ne_once {c : Claim} {cl : List Claim} (h : ClaimOnce c cl) :
    ∃ l1 l2, cl = l1 ++ c :: l2 ∧ c ∉ l1 ∧ c ∉ l2 ∧
      cl.filter (fun x => decide (x ≠ c)) = l1 ++ l2 := by
  classical
  obtain ⟨l1, l2, rfl, h1, h2⟩ := h
  refine ⟨l1, l2, rfl, h1, h2, ?_⟩
  have e : ∀ l : List Claim, c ∉ l → l.filter (fun x => decide (x ≠ c)) = l := fun l hl =>
    List.filter_eq_self.2 (fun x hx => by
      have : x ≠ c := fun he => hl (he ▸ hx)
      simpa using this)
  rw [List.filter_append, List.filter_cons, e l1 h1, e l2 h2]
  simp

open Classical in
theorem claimOnce_filter {c c' : Claim} {cl : List Claim} (h : ClaimOnce c cl) (hne : c ≠ c') :
    ClaimOnce c (cl.filter (fun x => decide (x ≠ c'))) := by
  classical
  obtain ⟨l1, l2, rfl, h1, h2⟩ := h
  refine ⟨l1.filter (fun x => decide (x ≠ c')), l2.filter (fun x => decide (x ≠ c')), ?_,
    fun hm => h1 (List.mem_filter.1 hm).1, fun hm => h2 (List.mem_filter.1 hm).1⟩
  rw [List.filter_append, List.filter_cons]
  simp [hne]

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- A big separating conjunction over a list, its elements outside `q` contributing nothing. -/
theorem bigSepL_filter_emp {A : Type} (g : A → IProp GF) (q : A → Bool)
    (hg : ∀ x, q x = false → g x = iprop(emp)) :
    ∀ l : List A, ([∗list] x ∈ l, g x) ⊣⊢ [∗list] x ∈ l.filter q, g x
  | [] => .rfl
  | x :: l => by
    cases hx : q x
    · rw [List.filter_cons_of_neg (by simp [hx])]
      refine BigSepL.bigSepL_cons.trans ?_
      rw [hg x hx]
      exact emp_sep.trans (bigSepL_filter_emp g q hg l)
    · rw [List.filter_cons_of_pos hx]
      exact BigSepL.bigSepL_cons.trans
        ((sep_congr .rfl (bigSepL_filter_emp g q hg l)).trans
          (BigSepL.bigSepL_cons (Φ := fun _ y => g y)).symm)

/-- **The parked claims across a change of the area claims** (no claim of the area directory is a
WAL directory's, so none is parked). -/
theorem parked_cover (Ls : GMap GoString WalLay) (D : List (Ino × NameSet)) (jr : Ino) (cl cl' : List Claim)
    (hA : ∀ c : Claim, c.1 = jr → ¬ WalDirClaimOf Ls c)
    (hf : cl'.filter (fun c => decide (c.1 ≠ jr)) = cl.filter (fun c => decide (c.1 ≠ jr))) :
    ([∗list] c ∈ cl, if ParkedClaim Ls D c then
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp) ⊢
      [∗list] c ∈ cl', if ParkedClaim Ls D c then
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp := by
  classical
  have hg : ∀ c : Claim, decide (c.1 ≠ jr) = false →
      (if ParkedClaim Ls D c then osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2
        else emp) = iprop(emp) := by
    intro c hc
    have : c.1 = jr := by simpa using hc
    rw [if_neg (fun hp => hA c this hp.1)]
  refine (bigSepL_filter_emp _ _ hg cl).1.trans ?_
  rw [← hf]
  exact (bigSepL_filter_emp _ _ hg cl').2

open Classical in
/-- The claims with one found once taken out. -/
theorem osClaims_filter_once (c : Claim) (cl : List Claim) (dq : DFrac) (h : ClaimOnce c cl) :
    osClaims L (cl.map (fun c => (c, dq))) ⊣⊢
      osNames (L := L) c.1 c.2.1 dq c.2.2 ∗
        osClaims L ((cl.filter (fun x => decide (x ≠ c))).map (fun c => (c, dq))) := by
  obtain ⟨l1, l2, rfl, -, -, hf⟩ := filter_ne_once h
  rw [hf, List.map_append (l₁ := l1) (l₂ := l2)]
  refine (osClaims_split (L := L) l1 l2 c dq).trans ?_
  constructor
  · iintro ⟨H1, Hc, H2⟩
    iframe Hc
    iapply (osClaims_append (L := L) _ _).2
    iframe
  · iintro ⟨Hc, H⟩
    icases (osClaims_append (L := L) _ _).1 $$ H with ⟨H1, H2⟩
    iframe

/-- **A claim the program holds half of occurs once among the invariant's** (a second occurrence
makes three halves). -/
theorem osClaims_once (cl : List Claim) (c : Claim) (hN : c.2.1 ≠ .only []) (hc : c ∈ cl) :
    ⊢ osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 -∗
      osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) -∗
      ⌜ClaimOnce c cl⌝ ∗ osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 ∗
        osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) := by
  classical
  obtain ⟨l1, l2, rfl, hl1⟩ := List.split_first hc
  iintro H Hcl
  by_cases hl2 : c ∈ l2
  · obtain ⟨m1, m2, rfl, -⟩ := List.split_first hl2
    icases (osClaims_split (L := L) l1 _ c _).1 $$ Hcl with ⟨-, Hc0, H2⟩
    icases (osClaims_split (L := L) m1 m2 c _).1 $$ H2 with ⟨-, Hc1, -⟩
    iexfalso
    iapply osNames_three_halves c.1 c.2.1 _ _ _ hN $$ H Hc0 Hc1
  · iframe H Hcl
    ipureintro; exact ⟨l1, l2, rfl, hl1, hl2⟩

/-- A whole claim and a half of it are invalid. -/
theorem osNames_whole_half (j : Ino) (N : NameSet) (h h' : NamesH) (hN : N ≠ .only []) :
    ⊢ osNames (L := L) j N (DFrac.own 1) h -∗ osNames (L := L) j N (DFrac.own (1 : Qp).half) h' -∗
      False := by
  iintro H H'
  icases osNames_halve j N h hN $$ H with ⟨H1, H2⟩
  iapply osNames_three_halves j N h h h' hN $$ H1 H2 H'

/-- **A whole claim held is none of the invariant's** (it would hold half of it too). -/
theorem osClaims_not_mem (cl : List Claim) (j : Ino) (N : NameSet) (h : NamesH) (hN : N ≠ .only []) :
    ⊢ osNames (L := L) j N (DFrac.own 1) h -∗
      osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) -∗
      ⌜(j, N, h) ∉ cl⌝ ∗ osNames (L := L) j N (DFrac.own 1) h ∗
        osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) := by
  classical
  iintro H Hcl
  by_cases hm : (j, N, h) ∈ cl
  · obtain ⟨l1, l2, rfl, -⟩ := List.split_first hm
    icases (osClaims_split (L := L) l1 l2 (j, N, h) _).1 $$ Hcl with ⟨-, Hc, -⟩
    iexfalso
    iapply osNames_whole_half j N h h hN $$ H Hc
  · iframe H Hcl
    ipureintro; exact hm

/-- **A whole claim held shares no name with any of the invariant's** (on the same directory: the
shared invariant's disjointness, `osClaims_keys`, then `osClaims_not_mem`). -/
theorem osClaims_excl (R : Roots) (cl : List Claim) (j : Ino) (N : NameSet) (h : NamesH)
    (hN : N ≠ .only []) {Em : CoPset} (hE : ↑osShN ⊆ Em) :
    ⊢ osSharedInv (L := L) R -∗ osNames (L := L) j N (DFrac.own 1) h -∗
      osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) ={Em}=∗
      ⌜∀ c ∈ cl, c.1 = j → ∀ b, N.Mem b → ¬ c.2.1.Mem b⌝ ∗ osNames (L := L) j N (DFrac.own 1) h ∗
        osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) := by
  iintro #Hsi H Hcl
  imod osClaims_keys R j N _ h _ hN hE $$ Hsi H Hcl with ⟨H, Hcl, %hk⟩
  icases osClaims_not_mem cl j N h hN $$ H Hcl with ⟨%hnm, H, Hcl⟩
  imodintro
  iframe H Hcl
  ipureintro
  intro c hc hj b hb hcb
  obtain ⟨e1, e2⟩ := hk (c, _) (List.mem_map_of_mem hc) hj b hb hcb
  apply hnm
  obtain ⟨c1, c2, c3⟩ := c
  simp only at hj e1 e2
  rw [← hj, ← e1, ← e2]
  exact hc

/-- **The creating map is empty where the program holds a lock token** (free or taken: a non-empty
map holds the free one). -/
theorem walCreating_empty (CR : GMap GoString (NameSet × NamesH × Ino)) (T : IProp GF)
    (hT : ⊢ T -∗ walUnlockedTok (W := W) -∗ False) :
    ⊢ walCreatingAuth (W := W) CR -∗ T -∗ ⌜CR = ∅⌝ ∗ walCreatingAuth (W := W) CR ∗ T := by
  unfold walCreatingAuth
  iintro ⟨Ha, Hor⟩ Hk
  icases Hor with (%hCR | ⟨-, Hu⟩)
  · iframe Ha Hk
    isplitr
    · ipureintro; exact hCR
    · ileft; ipureintro; exact hCR
  · iexfalso
    ihave Hx := hT $$ Hk Hu
    iexact Hx

/-- The parked claims and segments after a covering change of the area claims. -/
theorem walParked_cover (Ls : GMap GoString WalLay) (jr : Ino) (cl cl' : List Claim)
    {F : GMap Ino SegFl}
    (hA : ∀ c : Claim, c.1 = jr → ¬ WalDirClaimOf Ls c)
    (hf : cl'.filter (fun c => decide (c.1 ≠ jr)) = cl.filter (fun c => decide (c.1 ≠ jr))) :
    walParked (L := L) (W := W) Ls cl F ⊢ walParked (L := L) (W := W) Ls cl' F := by
  unfold walParked
  iintro ⟨%bp, %o, Hpa, Hoa, %hOD, Hsegs, Hpc, Htp⟩
  iexists bp, o
  iframe Hpa Hoa Hsegs Htp
  isplitr
  · ipureintro; exact hOD
  iapply parked_cover Ls o.D jr cl cl' hA hf $$ Hpc

/-- **Merging the program's halves of two area claims** (see the file header): each holds a WAL
name (`b1`, `b2`, the second not the first's), so each is the invariant's other half (`WalsCreateOk`,
`osClaims_keys`); the program holds a lock token (`T`), so the creating map is empty. -/
theorem walInvBody_merge2 (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (N1 N2 N : NameSet) (h1 h2 : NamesH) (b1 b2 : GoString) (T : IProp GF)
    (hT : ⊢ T -∗ walUnlockedTok (W := W) -∗ False) {Em : CoPset}
    (hb1 : walNameOk b1) (hN1 : N1.Mem b1) (hb2 : walNameOk b2) (hN2 : N2.Mem b2)
    (hb21 : ¬ N1.Mem b2) (hN : ∀ b, N.Mem b ↔ N1.Mem b ∨ N2.Mem b) (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗ T -∗
      osNames (L := L) jr N1 (DFrac.own (1 : Qp).half) h1 -∗
      osNames (L := L) jr N2 (DFrac.own (1 : Qp).half) h2 ={Em}=∗
      ∃ h, walInvBody (L := L) (W := W) C Mr R jr r s ∗ T ∗
        osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗
        ⌜h.restrict jr N1 = h1.restrict jr N1 ∧ h.restrict jr N2 = h2.restrict jr N2 ∧
          h.next = max h1.next h2.next⌝ := by
  classical
  have hN1e : N1 ≠ .only [] := nameSet_ne_empty hN1
  have hN2e : N2 ≠ .only [] := nameSet_ne_empty hN2
  have hNe : N ≠ .only [] := nameSet_ne_empty ((hN b1).2 (Or.inl hN1))
  have hne : ((jr, N1, h1) : Claim) ≠ (jr, N2, h2) := fun he => hb21 (by
    simp only [Prod.mk.injEq] at he; rw [he.2.1]; exact hN2)
  unfold walInvBody
  iintro Hb #Hsi Ht H1 H2
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, ⟨%CR, HCRa, %hCR⟩, Htl, %hab,
    %hwn, Hpk, ⟨%K, %cc, HK, Hcc, %hdk⟩, %hAt, Hnms⟩
  icases walCreating_empty CR T hT $$ HCRa Ht with ⟨%hCR0, HCRa, Ht⟩
  subst hCR0
  imod osClaims_keys R jr N1 _ h1 _ hN1e hE $$ Hsi H1 Hcl with ⟨H1, Hcl, %hk1⟩
  imod osClaims_keys R jr N2 _ h2 _ hN2e hE $$ Hsi H2 Hcl with ⟨H2, Hcl, %hk2⟩
  have hm1 : ((jr, N1, h1) : Claim) ∈ cl := by
    obtain ⟨M, g, hm, hM⟩ := hwc b1 hb1
    obtain ⟨e1, e2⟩ := hk1 ((jr, M, g), _) (List.mem_map_of_mem hm) rfl b1 hN1 hM
    simp only at e1 e2
    rw [e1, e2] at hm; exact hm
  have hm2 : ((jr, N2, h2) : Claim) ∈ cl := by
    obtain ⟨M, g, hm, hM⟩ := hwc b2 hb2
    obtain ⟨e1, e2⟩ := hk2 ((jr, M, g), _) (List.mem_map_of_mem hm) rfl b2 hN2 hM
    simp only at e1 e2
    rw [e1, e2] at hm; exact hm
  icases osClaims_once (L := L) cl (jr, N1, h1) hN1e hm1 $$ H1 Hcl with ⟨%ho1, H1, Hcl⟩
  icases osClaims_once (L := L) cl (jr, N2, h2) hN2e hm2 $$ H2 Hcl with ⟨%ho2, H2, Hcl⟩
  icases (osClaims_filter_once (L := L) (jr, N2, h2) cl _ ho2).1 $$ Hcl with ⟨Hc2, Hcl⟩
  obtain ⟨l1, l2, hl, hl1, hl2⟩ := claimOnce_filter ho1 hne
  ihave Hcl := (show osClaims L ((cl.filter (fun x => decide (x ≠ ((jr, N2, h2) : Claim)))).map
      (fun c => (c, DFrac.own (1 : Qp).half))) ⊢
      osClaims L (l1.map (fun c => (c, DFrac.own (1 : Qp).half))) ∗
        osNames (L := L) jr N1 (DFrac.own (1 : Qp).half) h1 ∗
        osClaims L (l2.map (fun c => (c, DFrac.own (1 : Qp).half))) from by
    rw [hl]; exact (osClaims_split (L := L) l1 l2 _ _).1) $$ Hcl
  icases Hcl with ⟨Hl1, Hc1, Hl2⟩
  icases osNames_halves jr N1 h1 h1 hN1e $$ H1 Hc1 with ⟨-, Hw1⟩
  icases osNames_halves jr N2 h2 h2 hN2e $$ H2 Hc2 with ⟨-, Hw2⟩
  imod osNames_self R jr N1 _ h1 hE $$ Hsi Hw1 with ⟨Hw1, %hs1⟩
  imod osNames_self R jr N2 _ h2 hE $$ Hsi Hw2 with ⟨Hw2, %hs2⟩
  imod osNames_merge (L := L) R jr N1 N2 N h1 h2 hN hE $$ Hsi Hw1 Hw2 with ⟨%h, Hw, %hmr⟩
  icases osNames_halve jr N h hNe $$ Hw with ⟨Hh1, Hh2⟩
  have hmo : MergeOk cl jr N1 N2 N h1 h2 h := ⟨hm1, Or.inl hm2, hne, hs1, hs2, hmr.1, hmr.2.1, hN⟩
  have hcov : CoverOk jr cl (mergeClaims cl (jr, N1, h1) (jr, N2, h2) (jr, N, h)) n :=
    coverOk_merge hmo
  have hcl' : mergeClaims cl (jr, N1, h1) (jr, N2, h2) (jr, N, h) = l1 ++ (jr, N, h) :: l2 := by
    unfold mergeClaims; rw [hl, replClaim_split hl1 hl2]
  have hnW : ∀ c : Claim, c.1 = jr → ¬ WalDirClaimOf Ls c := fun c hc => hAt.not_walDirClaimOf c hc
  have hf := filter_mergeClaims (fun c : Claim => decide (c.1 ≠ jr)) (c1 := (jr, N1, h1))
    (c2 := (jr, N2, h2)) (c := (jr, N, h)) (by simp) (by simp) (by simp) cl
  ihave Hpk := walParked_cover Ls jr cl _ hnW hf $$ Hpk
  imodintro
  iexists h
  iframe Ht Hh2
  isplitl [Hg Hl1 Hh1 Hl2 Hn HF HCRa Htl Hpk HK Hcc Hnms]
  · iexists Ls, mergeClaims cl (jr, N1, h1) (jr, N2, h2) (jr, N, h), n, F
    iframe Hg Hn HF Htl Hpk
    isplitr
    · ipureintro; exact hr
    isplitl [Hl1 Hh1 Hl2]
    · rw [hcl']
      iapply (osClaims_split (L := L) l1 l2 _ _).2
      iframe
    isplitr
    · ipureintro; exact walsOk_cover hcov hAt hwo
    isplitr
    · ipureintro; exact walsCreateOk_cover hcov hwc
    isplitl [HCRa]
    · iexists ∅
      iframe HCRa
      ipureintro; intro dir N' h' J' hl'; simp at hl'
    isplitr
    · ipureintro; exact ⟨absentNone_cover hcov hab.1, hab.2⟩
    isplitr
    · ipureintro; exact walsNamed_cover hcov hAt hwn
    isplitl [HK Hcc]
    · iexists K, cc
      iframe HK Hcc
      ipureintro; exact dirKeysOk_cover hcov hdk
    iframe Hnms; ipureintro; exact walsAt_cover hcov hwo hAt
  ipureintro; exact hmr

/-- **Merging a whole claim of the area holding no WAL name into the program's half of an area
claim** (see the file header): the area claim holds the WAL name `b1`, so it is the invariant's other
half; the whole claim is none of the invariant's. -/
theorem walInvBody_mergeIn (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (N1 N2 N : NameSet) (h1 h2 : NamesH) (b1 b2 : GoString) (T : IProp GF)
    (hT : ⊢ T -∗ walUnlockedTok (W := W) -∗ False) {Em : CoPset}
    (hb1 : walNameOk b1) (hN1 : N1.Mem b1) (hN2 : N2.Mem b2)
    (hno : ∀ b, N2.Mem b → ¬ walNameOk b) (hN : ∀ b, N.Mem b ↔ N1.Mem b ∨ N2.Mem b)
    (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗ T -∗
      osNames (L := L) jr N1 (DFrac.own (1 : Qp).half) h1 -∗
      osNames (L := L) jr N2 (DFrac.own 1) h2 ={Em}=∗
      ∃ h, walInvBody (L := L) (W := W) C Mr R jr r s ∗ T ∗
        osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗
        ⌜h.restrict jr N1 = h1.restrict jr N1 ∧ h.restrict jr N2 = h2.restrict jr N2 ∧
          h.next = max h1.next h2.next⌝ := by
  classical
  have hN1e : N1 ≠ .only [] := nameSet_ne_empty hN1
  have hN2e : N2 ≠ .only [] := nameSet_ne_empty hN2
  have hNe : N ≠ .only [] := nameSet_ne_empty ((hN b1).2 (Or.inl hN1))
  unfold walInvBody
  iintro Hb #Hsi Ht H1 H2
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, ⟨%CR, HCRa, %hCR⟩, Htl, %hab,
    %hwn, Hpk, ⟨%K, %cc, HK, Hcc, %hdk⟩, %hAt, Hnms⟩
  icases walCreating_empty CR T hT $$ HCRa Ht with ⟨%hCR0, HCRa, Ht⟩
  subst hCR0
  imod osClaims_keys R jr N1 _ h1 _ hN1e hE $$ Hsi H1 Hcl with ⟨H1, Hcl, %hk1⟩
  have hm1 : ((jr, N1, h1) : Claim) ∈ cl := by
    obtain ⟨M, g, hm, hM⟩ := hwc b1 hb1
    obtain ⟨e1, e2⟩ := hk1 ((jr, M, g), _) (List.mem_map_of_mem hm) rfl b1 hN1 hM
    simp only at e1 e2
    rw [e1, e2] at hm; exact hm
  icases osClaims_not_mem (L := L) cl jr N2 h2 hN2e $$ H2 Hcl with ⟨%hm2, H2, Hcl⟩
  have hne : ((jr, N1, h1) : Claim) ≠ (jr, N2, h2) := fun he => hm2 (he ▸ hm1)
  icases osClaims_once (L := L) cl (jr, N1, h1) hN1e hm1 $$ H1 Hcl with ⟨%ho1, H1, Hcl⟩
  obtain ⟨l1, l2, hl, hl1, hl2⟩ := ho1
  have hfe : cl.filter (fun x => decide (x ≠ ((jr, N2, h2) : Claim))) = cl :=
    List.filter_eq_self.2 (fun x hx => by
      have : x ≠ ((jr, N2, h2) : Claim) := fun he => hm2 (he ▸ hx)
      simpa using this)
  subst hl
  icases (osClaims_split (L := L) l1 l2 _ _).1 $$ Hcl with ⟨Hl1, Hc1, Hl2⟩
  icases osNames_halves jr N1 h1 h1 hN1e $$ H1 Hc1 with ⟨-, Hw1⟩
  imod osNames_self R jr N1 _ h1 hE $$ Hsi Hw1 with ⟨Hw1, %hs1⟩
  imod osNames_self R jr N2 _ h2 hE $$ Hsi H2 with ⟨H2, %hs2⟩
  imod osNames_merge (L := L) R jr N1 N2 N h1 h2 hN hE $$ Hsi Hw1 H2 with ⟨%h, Hw, %hmr⟩
  icases osNames_halve jr N h hNe $$ Hw with ⟨Hh1, Hh2⟩
  have hmo : MergeOk (l1 ++ (jr, N1, h1) :: l2) jr N1 N2 N h1 h2 h :=
    ⟨hm1, Or.inr hno, hne, hs1, hs2, hmr.1, hmr.2.1, hN⟩
  have hcov := coverOk_merge (n := n) hmo
  have hcl' : mergeClaims (l1 ++ (jr, N1, h1) :: l2) (jr, N1, h1) (jr, N2, h2) (jr, N, h) =
      l1 ++ (jr, N, h) :: l2 := by
    unfold mergeClaims; rw [hfe, replClaim_split hl1 hl2]
  have hnW : ∀ c : Claim, c.1 = jr → ¬ WalDirClaimOf Ls c := fun c hc => hAt.not_walDirClaimOf c hc
  have hf := filter_mergeClaims (fun c : Claim => decide (c.1 ≠ jr)) (c1 := (jr, N1, h1))
    (c2 := (jr, N2, h2)) (c := (jr, N, h)) (by simp) (by simp) (by simp) (l1 ++ (jr, N1, h1) :: l2)
  ihave Hpk := walParked_cover Ls jr _ _ hnW hf $$ Hpk
  imodintro
  iexists h
  iframe Ht Hh2
  isplitl [Hg Hl1 Hh1 Hl2 Hn HF HCRa Htl Hpk HK Hcc Hnms]
  · iexists Ls, mergeClaims (l1 ++ (jr, N1, h1) :: l2) (jr, N1, h1) (jr, N2, h2) (jr, N, h), n, F
    iframe Hg Hn HF Htl Hpk
    isplitr
    · ipureintro; exact hr
    isplitl [Hl1 Hh1 Hl2]
    · rw [hcl']
      iapply (osClaims_split (L := L) l1 l2 _ _).2
      iframe
    isplitr
    · ipureintro; exact walsOk_cover hcov hAt hwo
    isplitr
    · ipureintro; exact walsCreateOk_cover hcov hwc
    isplitl [HCRa]
    · iexists ∅
      iframe HCRa
      ipureintro; intro dir N' h' J' hl'; simp at hl'
    isplitr
    · ipureintro; exact ⟨absentNone_cover hcov hab.1, hab.2⟩
    isplitr
    · ipureintro; exact walsNamed_cover hcov hAt hwn
    isplitl [HK Hcc]
    · iexists K, cc
      iframe HK Hcc
      ipureintro; exact dirKeysOk_cover hcov hdk
    iframe Hnms; ipureintro; exact walsAt_cover hcov hwo hAt
  ipureintro; exact hmr

/-- **The unminting** (an abort past the minting): the creating entry deleted, the free lock token
back; the claims unchanged (the caller merges them back, `walInvBody_merge2`). -/
theorem walInvBody_unmint (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (N : NameSet) (h : NamesH) (J : Ino) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walCreating (W := W) dir N h J ==∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walUnlockedTok (W := W) := by
  unfold walInvBody
  iintro Hb Htok
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, ⟨%CR, HCRa, %hCR⟩, Htl, %hab,
    %hwn, Hpk, ⟨%K, %cc, HK, Hcc, %hdk⟩, %hAt, Hnms⟩
  imod walCreating_delete CR dir N h J $$ HCRa Htok with ⟨%hdel, HCRa, Hu⟩
  imodintro
  iframe Hu
  iexists Ls, cl, n, F
  iframe Hg Hcl Hn HF Htl Hpk
  isplitr
  · ipureintro; exact hr
  isplitr
  · ipureintro; exact hwo
  isplitr
  · ipureintro; exact hwc
  isplitl [HCRa]
  · iexists GMap.delete dir CR
    iframe HCRa
    ipureintro; rw [hdel]; intro dir' N' h' J' hl'; simp at hl'
  isplitr
  · ipureintro; exact hab
  isplitr
  · ipureintro; exact hwn
  isplitl [HK Hcc]
  · iexists K, cc
    iframe HK Hcc
    ipureintro; exact hdk
  iframe Hnms; ipureintro; exact hAt

end iris

end WalFs
end EtcdGrove
end Perennial

end
