/- Lean-first (no Rocq counterpart).

# The drop of a name off the area claim, as a step (W4, `notes/wal-fsext-plan.md`, "W4 implementation
log", ninth session)

`Create` needs the whole claim on `nm.tmp` (`RemoveAll`, `CreateDirAll`, the segment's creation), and
`cleanupWAL` the one on `nm.broken.<time>`; the program holds half of the area claim `(jr, N, h)`
(`walAreaRes`), the invariant the other half. `walInvBody_drop` (a ghost step, the file system's shared
invariant and the WAL invariant's contents open, the lock free) takes the invariant's half of the
area claim and gives it back off the name `b`: the program gets the whole claim on `.only [b]` and keeps
its half of the rest. The invariant's facts carry over by `CreateDropInv.lean`; what they need of the
step: the area claim is the invariant's claim on the WAL name `nm` (`WalsCreateOk`, and two claims of
one directory sharing a name are one, `osClaims_keys`), it occurs once (a third half would be invalid),
it is no WAL directory's claim (the lock free, `walParked` holds the program's half of every such claim:
three halves again), the claims are one log's (`osClaims_log`), and the creating map is empty (a
non-empty one holds the lock token).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDropInv
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAu
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamed

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- The first occurrence of a member. -/
theorem List.split_first {α : Type} [DecidableEq α] {c : α} :
    ∀ {l : List α}, c ∈ l → ∃ l1 l2, l = l1 ++ c :: l2 ∧ c ∉ l1
  | [], h => absurd h (List.not_mem_nil)
  | a :: l, h => by
    by_cases ha : a = c
    · subst ha; exact ⟨[], l, rfl, List.not_mem_nil⟩
    · obtain ⟨l1, l2, rfl, h1⟩ := List.split_first (List.mem_of_ne_of_mem (Ne.symm ha) h)
      refine ⟨a :: l1, l2, rfl, ?_⟩
      rintro (_ | ⟨_, hm⟩)
      · exact ha rfl
      · exact h1 hm

section walsAt
variable [GooseExts]

/-- **`WalsAt` after the drop** (W3/W5's gap 1): the area claim loses `b` (no WAL's name is
affected: the claim's remaining names keep their entries). -/
theorem walsAt_drop {jr : Ino} {Ls : GMap GoString WalLay} {cl : List Claim} {N : NameSet}
    {h : NamesH} {b : GoString} (hA : WalsAt jr Ls cl) (hm : (jr, N, h) ∈ cl) :
    WalsAt jr Ls (dropClaims cl jr N h b) := by
  intro dir lay hl
  refine ⟨hA.ne hl, fun N' h' hc hN' => ?_⟩
  rcases mem_dropClaims hc with he | ⟨hc', -⟩
  · cases he
    show restrictN (N.diff [b]) h.cur !! lay.nm = _
    rw [restrictN_lookup _ _ _ hN']
    exact hA.at hl hm ((NameSet.mem_diff N [b] lay.nm).1 hN').1
  · exact hA.at hl hc' hN'

end walsAt

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- The claims held are keys of the claims' authority. -/
theorem claims_keys (Γn : GMap (Ino × NameSet) NamesH) :
    ∀ cl : List (Claim × DFrac),
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ osClaims L cl -∗
      ⌜∀ c ∈ cl, c.1.2.1 ≠ .only [] → Γn !! (c.1.1, c.1.2.1) = some c.1.2.2⌝ ∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ∗ osClaims L cl
  | [] => by
    iintro HA Hc
    iframe
    ipureintro; intro c hc; cases hc
  | c :: cl => by
    iintro HA Hc
    icases (osClaims_cons L c cl).1 $$ Hc with ⟨H1, Hc⟩
    icases claims_keys Γn cl $$ HA Hc with ⟨%hcl, HA, Hc⟩
    by_cases hN : c.1.2.1 = .only []
    · iframe HA
      isplitr
      · ipureintro
        intro c' hc' hne
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact absurd hN hne
        · exact hcl c' hc' hne
      iapply (osClaims_cons L c cl).2
      iframe
    · rw [osNames_of_ne _ _ hN]
      icases gAuth_lookup _ _ _ _ _ _ $$ HA H1 with %h1
      iframe HA
      isplitr
      · ipureintro
        intro c' hc' hne
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact h1
        · exact hcl c' hc' hne
      iapply (osClaims_cons L c cl).2
      rw [osNames_of_ne _ _ hN]
      iframe

/-- **A claim held and a list of claims**: each claim of the list on the same directory sharing a
name with it is it (same names, same history; `NamesCoh.disj`). -/
theorem osClaims_keys (R : Roots) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH)
    (cl : List (Claim × DFrac)) (hN : N ≠ .only []) {Em : CoPset} (hE : ↑osShN ⊆ Em) :
    ⊢ osSharedInv (L := L) R -∗ osNames (L := L) j N dq h -∗ osClaims L cl ={Em}=∗
      osNames (L := L) j N dq h ∗ osClaims L cl ∗
      ⌜∀ c ∈ cl, c.1.1 = j → ∀ b, N.Mem b → c.1.2.1.Mem b → c.1.2.1 = N ∧ c.1.2.2 = h⌝ := by
  rw [osNames_of_ne dq h hN]
  unfold osSharedInv
  iintro #Hsi H Hc
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAn H with %h1
  icases claims_keys Γn cl $$ HAn Hc with ⟨%hcl, HAn, Hc⟩
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists Vs, Γn; iframe; ipureintro; exact hcoh
  imodintro
  iframe
  ipureintro
  intro c hc hj b hb hb'
  have hne : c.1.2.1 ≠ .only [] := nameSet_ne_empty hb'
  have h2 := hcl c hc hne
  rw [hj] at h2
  have hNN : c.1.2.1 = N := Classical.byContradiction fun hn =>
    hcoh.2.disj j N c.1.2.1 h c.1.2.2 b h1 h2 (Ne.symm hn) hb hb'
  refine ⟨hNN, ?_⟩
  rw [hNN, h1] at h2
  cases h2; rfl

/-- **A claim's history is its own restriction** (every entry writes one of its names). -/
theorem osNames_self (R : Roots) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) {Em : CoPset}
    (hE : ↑osShN ⊆ Em) :
    ⊢ osSharedInv (L := L) R -∗ osNames (L := L) j N dq h ={Em}=∗
      osNames (L := L) j N dq h ∗ ⌜h.restrict j N = h⌝ := by
  unfold osSharedInv
  iintro #Hsi H
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases osNames_auth L hcoh.2 _ _ _ _ $$ HAn H with %hh
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists Vs, Γn; iframe; ipureintro; exact hcoh
  imodintro
  iframe H
  ipureintro
  rw [hh]; exact namesOf_restrict_self Vs j N

/-- Two halves of a claim make it whole. -/
theorem osNames_halves (j : Ino) (N : NameSet) (h h' : NamesH) (hN : N ≠ .only []) :
    ⊢ osNames (L := L) j N (DFrac.own (1 : Qp).half) h -∗
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h' -∗
      ⌜h = h'⌝ ∗ osNames (L := L) j N (DFrac.own 1) h := by
  rw [osNames_of_ne _ h hN, osNames_of_ne _ h' hN, osNames_of_ne _ h hN]
  iintro H1 H2
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %hv
  obtain ⟨-, rfl⟩ := hv
  isplitr
  · ipureintro; rfl
  have hs := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn (j, N) (1 : Qp).half
    (1 : Qp).half h
  rw [Qp.half_add_half] at hs
  iapply hs.2
  iframe

/-- A whole claim in halves. -/
theorem osNames_halve (j : Ino) (N : NameSet) (h : NamesH) (hN : N ≠ .only []) :
    ⊢ osNames (L := L) j N (DFrac.own 1) h -∗
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h ∗
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h := by
  rw [osNames_of_ne (DFrac.own 1) h hN, osNames_of_ne (DFrac.own (1 : Qp).half) h hN]
  iintro H
  have hs := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn (j, N) (1 : Qp).half
    (1 : Qp).half h
  rw [Qp.half_add_half] at hs
  iapply hs.1
  iexact H

/-- **Three halves of a claim are invalid.** -/
theorem osNames_three_halves (j : Ino) (N : NameSet) (h1 h2 h3 : NamesH) (hN : N ≠ .only []) :
    ⊢ osNames (L := L) j N (DFrac.own (1 : Qp).half) h1 -∗
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h2 -∗
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h3 -∗ False := by
  iintro H1 H2 H3
  icases osNames_halves (L := L) j N h1 h2 hN $$ H1 H2 with ⟨-, H⟩
  rw [osNames_of_ne (DFrac.own 1) h1 hN, osNames_of_ne (DFrac.own (1 : Qp).half) h3 hN]
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H H3 with %hv
  exfalso
  have := DFrac.valid_own_op hv.1
  simp at this

/-- The lock free: nothing is out of the parked state (the lock token's record is empty). -/
theorem walUnlocked_out (o : WalOut) :
    ⊢@{IProp GF} walOutAuth (W := W) o -∗ walUnlockedTok (W := W) -∗
      ⌜o = WalOut.empty⌝ ∗ walOutAuth (W := W) o ∗ walUnlockedTok (W := W) := by
  unfold walUnlockedTok
  iintro Ha ⟨Ht, Hf, Hc, Ho, Htf⟩
  icases walOut_agree (W := W) o _ $$ Ha Ho with %ho
  iframe
  ipureintro; exact ho

/-- The parked halves after the drop (neither the area claim nor its part is a WAL directory's). -/
theorem parked_drop (Ls : GMap GoString WalLay) (cl : List Claim) (jr : Ino) (N : NameSet)
    (h : NamesH) {D : List (Ino × NameSet)} (b : GoString) (hbw : walNameP b = false) (hW : ¬ WalDirClaimOf Ls (jr, N, h)) :
    ([∗list] c ∈ cl, if ParkedClaim Ls D c then
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp) ⊢
      [∗list] c ∈ dropClaims cl jr N h b, if ParkedClaim Ls D c then
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) c.2.2 else emp := by
  classical
  unfold dropClaims replClaim
  rw [BigSepL.bigSepL_map]
  refine BigSepL.bigSepL_mono (fun {k x} _ => ?_)
  by_cases hx : x = (jr, N, h)
  · subst hx
    simp only [if_true]
    rw [if_neg (fun hp => hW hp.1), if_neg (fun hp => not_walDirClaimOf_diff hbw hW hp.1)]
  · rw [if_neg hx]

/-- **The drop of the name `b` off the area claim** (see the file header): the program's half of
the area claim `(jr, N, h)` (holding the WAL name `nm` and `b`, no WAL name nor `.wal` name, an area
slot), the lock free; the invariant's contents keep the claim's part off `b`, the program gets the
whole claim on `b` and keeps its half of the rest. -/
theorem walInvBody_drop (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (N : NameSet) (h : NamesH) (nm b : GoString) {Em : CoPset}
    (hnm : walNameOk nm) (hNnm : N.Mem nm) (hb : N.Mem b) (hbw : walNameP b = false)
    (hbn : ¬ walNameOk b) (hbs : AreaSlot b) (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗
      walUnlockedTok (W := W) -∗ osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ={Em}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walUnlockedTok (W := W) ∗
      osNames (L := L) jr (N.diff [b]) (DFrac.own (1 : Qp).half) (h.restrict jr (N.diff [b])) ∗
      osNames (L := L) jr (.only [b]) (DFrac.own 1) (h.restrict jr (N.inter [b])) := by
  classical
  have hNe : N ≠ .only [] := nameSet_ne_empty hb
  have hbnm : nm ≠ b := fun he => hbn (he ▸ hnm)
  have hDe : N.diff [b] ≠ .only [] :=
    nameSet_ne_empty ((N.mem_diff [b] nm).2 ⟨hNnm, by simpa using hbnm⟩)
  have hSame : (N.inter [b]).Same (.only [b]) := fun b' => by
    rw [N.mem_inter]
    simp only [NameSet.Mem, List.mem_singleton]
    constructor
    · exact fun h' => h'.2
    · rintro rfl; exact ⟨hb, rfl⟩
  unfold walInvBody
  iintro Hb #Hsi Hu H
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, ⟨%CR, HCRa, %hCR⟩, Ht, %hab,
    %hwn, Hpk, ⟨%K, %cc, HK, Hcc, %hdk⟩, %hAt⟩
  unfold walCreatingAuth
  icases HCRa with ⟨HCRa, Hor⟩
  icases Hor with (%hCR0 | ⟨-, Hl⟩)
  rotate_left
  · iexfalso; iapply walUnlockedTok_excl $$ Hl Hu
  subst hCR0
  unfold walParked
  icases Hpk with ⟨%bp, %o, Hpa, Hoa, %hOD, Hsegs, Hpc, Htp⟩
  icases walUnlocked_out o $$ Hoa Hu with ⟨%ho, Hoa, Hu⟩
  subst ho
  imod osClaims_log (L := L) R _ hE $$ Hsi Hcl with ⟨Hcl, %hlog⟩
  imod osClaims_keys R jr N _ h _ hNe hE $$ Hsi H Hcl with ⟨H, Hcl, %hkeys⟩
  imod osNames_self R jr N _ h hE $$ Hsi H with ⟨H, %hself⟩
  obtain ⟨N1, h1, hm1, hN1⟩ := hwc nm hnm
  obtain ⟨rfl, rfl⟩ := hkeys ((jr, N1, h1), _) (List.mem_map_of_mem hm1) rfl nm hNnm hN1
  have hd : DropOk cl jr N1 h1 b := by
    obtain ⟨log, hst, hl⟩ := hlog
    refine ⟨⟨log, hst, fun c hc x e Es hx => hl (c, _) (List.mem_map_of_mem hc) x e Es hx⟩, hm1,
      hself, hb, fun c hc hne hj hcb => hne ?_⟩
    obtain ⟨e1, e2⟩ := hkeys (c, _) (List.mem_map_of_mem hc) hj b hb hcb
    obtain ⟨c1, c2, c3⟩ := c
    simp only at hj e1 e2
    rw [hj, e1, e2]
  obtain ⟨l1, l2, rfl, hl1⟩ := List.split_first hm1
  icases (osClaims_split (L := L) l1 l2 (jr, N1, h1) _).1 $$ Hcl with ⟨H1, Hc0, H2⟩
  by_cases hl2 : (jr, N1, h1) ∈ l2
  · obtain ⟨m1, m2, rfl, -⟩ := List.split_first hl2
    icases (osClaims_split (L := L) m1 m2 (jr, N1, h1) _).1 $$ H2 with ⟨-, Hc1, -⟩
    iexfalso
    iapply osNames_three_halves jr N1 h1 h1 h1 hNe $$ H Hc0 Hc1
  by_cases hW : WalDirClaimOf Ls (jr, N1, h1)
  · icases (BigSepL.bigSepL_append).1 $$ Hpc with ⟨-, Hpc⟩
    icases (BigSepL.bigSepL_cons).1 $$ Hpc with ⟨Hp0, -⟩
    ihave Hp0 := (show (if ParkedClaim Ls WalOut.empty.D (jr, N1, h1) then
        osNames (L := L) jr N1 (DFrac.own (1 : Qp).half) h1 else emp : IProp GF) ⊢
        osNames (L := L) jr N1 (DFrac.own (1 : Qp).half) h1 from by
      rw [if_pos ⟨hW, List.not_mem_nil⟩]) $$ Hp0
    iexfalso
    iapply osNames_three_halves jr N1 h1 h1 h1 hNe $$ H Hc0 Hp0
  icases osNames_halves jr N1 h1 h1 hNe $$ Hc0 H with ⟨-, Hw⟩
  imod osNames_split (L := L) R jr N1 [b] h1 hE $$ Hsi Hw with ⟨HI, HD⟩
  imod osNames_rekey (L := L) R jr (N1.inter [b]) (.only [b]) _ hSame hE $$ Hsi HI with HI
  icases osNames_halve jr (N1.diff [b]) _ hDe $$ HD with ⟨HD1, HD2⟩
  ihave Hpc := parked_drop (L := L) Ls _ jr N1 h1 b hbw hW $$ Hpc
  have hw : ∀ dir d, s.wal !! dir = some d → ∃ lay nm, Ls !! dir = some lay ∧
      InArea s.area dir nm ∧ lay.jr = jr ∧ lay.nm = nm := fun dir d hd' => by
    obtain ⟨lay, nm', hj, hl, hia, hjr, hnm', -⟩ := hwo.1 dir d hd'
    exact ⟨lay, nm', hl, hia, hjr, hnm'⟩
  imodintro
  iframe Hu HI HD2
  iexists Ls, dropClaims (l1 ++ (jr, N1, h1) :: l2) jr N1 h1 b, n, F
  iframe Hg Hn HF Ht
  isplitr
  · ipureintro; exact hr
  isplitl [H1 HD1 H2]
  · unfold dropClaims
    rw [replClaim_split hl1 hl2]
    iapply (osClaims_split (L := L) l1 l2 _ _).2
    iframe
  isplitr
  · ipureintro; exact walsOk_drop hd hbw hbn hbs hab.2 hW hwo
  isplitr
  · ipureintro; exact walsCreateOk_drop hd.mem hbn hwc
  isplitl [HCRa]
  · iexists ∅
    iframe HCRa
    isplitl
    · ileft; ipureintro; rfl
    · ipureintro; intro dir N' h' J' hl; simp at hl
  isplitr
  · ipureintro; exact ⟨absentNone_drop hd hbn hab.1, hab.2⟩
  isplitr
  · ipureintro; exact walsNamed_drop hd hbw hW hwn
  isplitl [Hpa Hoa Hsegs Hpc Htp]
  · iexists bp, WalOut.empty
    iframe Hpa Hoa Hsegs Hpc Htp
    ipureintro; exact hOD
  isplitl [HK Hcc]
  · iexists K, cc
    iframe HK Hcc
    ipureintro
    exact dirKeysOk_drop hd hbw hbn hw hdk
  ipureintro
  exact walsAt_drop hAt hd.mem

end iris

end WalFs
end EtcdGrove
end Perennial

end
