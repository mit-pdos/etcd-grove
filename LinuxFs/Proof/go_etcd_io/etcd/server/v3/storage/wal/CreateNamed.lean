/- Lean-first (no Rocq counterpart).

# `Create`'s parent fsync: the WAL becomes named (W4, `notes/wal-fsext-plan.md`, "W4 implementation log")

After `Create`'s rename of `nm.tmp` onto `nm` (the entry `x`, the last writer of `nm` in the program's
claim `h` on names `N ∋ nm`, holding the WAL's directory `J`), the parent's fsync gives `osCommitLb n`
with `x < n`. Then every crash keeps the rename, so the WAL's crash condition holds with `named`
raised (`crashOk_named_of_lastWrite`), and the WAL state takes the step to `named = true`, a past state
of which is `walNamed dir`.

* `walsOk_mono`: the invariant's pure facts at a bigger commit bound.
* `walsOk_named`: ... and with the WAL in `dir` named.
* `walInvBody_named`: the step on the invariant's contents, with the program's claim (a fraction) and
  the commit bound; the claim is matched with the invariant's (`WalsCreateOk`: one of its claims
  holds `nm`; two claims of one directory holding a name are one, `NamesCoh.disj`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamedPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashPure

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

theorem crashOk_mono {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {cl : List Claim}
    {n0 n : Nat} (hn : n0 ≤ n) (h : CrashOk C Mr d lay cl n0) : CrashOk C Mr d lay cl n :=
  fun m' fo hr => h m' fo (regionCrashed_mono hn hr)

/-- The static relation does not depend on `named`. -/
theorem walAbsD_named {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (b : Bool) (h : WalAbsD C Mr d lay ents) : WalAbsD C Mr { d with named := b } lay ents := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem crashOkW_mono {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n0 n : Nat} (hn : n0 ≤ n) (h : CrashOkW C Mr d lay cl n0) :
    CrashOkW C Mr d lay cl n := by
  obtain ⟨alt, halt, h⟩ := h
  exact ⟨alt, halt, fun m' fo hr => h m' fo (regionCrashed_mono hn hr)⟩

/-- `CrashTo` with `named` raised, the WAL's name holding a directory in the crashed tree. -/
theorem crashTo_named {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {m' : Tree}
    {fo : Ino → Option Fs.OsFile} (hct : CrashTo C Mr d lay m' fo)
    (hJ : ∃ J, m'.entry lay.jr lay.nm = some (.dir J)) :
    CrashTo C Mr { d with named := true } lay m' fo := by
  rcases hct with ⟨-, hnone⟩ | hright
  · obtain ⟨J, hJ⟩ := hJ; rw [hnone] at hJ; cases hJ
  · exact Or.inr hright

/-- **The crash condition (with a pending cut's alternative) with `named` raised**, the WAL's name
decided as a directory in every crash the claims allow with the bound `n`. -/
theorem crashOkW_named {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n0 n : Nat} (hn : n0 ≤ n) (hok : CrashOkW C Mr d lay cl n0)
    (hname : ∀ m', RegionCrashed cl n m' → ∃ J, m'.entry lay.jr lay.nm = some (.dir J)) :
    CrashOkW C Mr { d with named := true } lay cl n := by
  obtain ⟨alt, halt, h⟩ := hok
  refine ⟨alt, fun lay0 h0 => ?_, fun m' fo hr hf hnm hw1 => ?_⟩
  · obtain ⟨⟨ents0, ha⟩, h1, h2, h3, h4⟩ := halt lay0 h0
    exact ⟨⟨ents0, walAbsD_named true ha⟩, h1, h2, h3, h4⟩
  · rcases h m' fo (regionCrashed_mono hn hr) hf hnm hw1 with hct | ⟨lay0, h0, hct⟩
    · exact Or.inl (crashTo_named hct (hname m' hr))
    · obtain ⟨-, h1, h2, -, -⟩ := halt lay0 h0
      refine Or.inr ⟨lay0, h0, crashTo_named hct ?_⟩
      rw [h1, h2]; exact hname m' hr

/-- **The invariant's pure facts at a bigger commit bound.** -/
theorem walsOk_mono {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n0 n : Nat} (hn : n0 ≤ n)
    (h : WalsOk C Mr R jr s Ls cl n0) : WalsOk C Mr R jr s Ls cl n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun dir d hd => ?_, h2, h3, h4, fun dir nm hin hn' m' hr => h5 dir nm hin hn' m'
    (regionCrashed_mono hn hr), fun dd hdd m' hr => h6 dd hdd m' (regionCrashed_mono hn hr)⟩
  obtain ⟨lay, nm, hj, hl, hin, hjr, hnm, hc, ha, hok⟩ := h1 dir d hd
  exact ⟨lay, nm, hj, hl, hin, hjr, hnm, hc, ha, crashOkW_mono hn hok⟩

/-- The step raising `named` of the WAL in `dir`. -/
def setNamed (s : AbsDiskState) (dir : GoString) : AbsDiskState :=
  absDiskUpd s dir (fun d => { d with named := true })

/-- **The invariant's pure facts with the WAL in `dir` named**, its name's last writer (holding a
directory) committed. -/
theorem walsOk_named {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n0 n : Nat} (hn : n0 ≤ n)
    (hok : WalsOk C Mr R jr s Ls cl n0) {dir nm : GoString} {d : WalDur}
    (hd : s.wal !! dir = some d) (hin : InArea s.area dir nm) {N : NameSet} {h : NamesH} {x : Nat}
    {e : LogEntry} {E : Ents} {J : Ino} (hc : (jr, N, h) ∈ cl) (hN : N.Mem nm)
    (hl : LastWrite h jr nm x e E) (hx : x < n) (hJ : E !! nm = some (.dir J)) :
    WalsOk C Mr R jr (setNamed s dir) Ls cl n := by
  have hok' := walsOk_mono hn hok
  have hw : (setNamed s dir).wal = <[dir := { d with named := true }]> s.wal :=
    absDiskUpd_wal s dir _ d hd
  have harea : (setNamed s dir).area = s.area := absDiskUpd_area s dir _
  have hdirs : (setNamed s dir).dirs = s.dirs := by
    unfold setNamed absDiskUpd; rw [hd]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hok'
  refine ⟨fun dir' d' hd' => ?_, fun dir' hn' => h2 dir' ?_, h3, h4, ?_, ?_⟩
  · rw [hw] at hd'
    by_cases he : dir' = dir
    · subst he
      rw [GMap.lookup_insert_eq] at hd'
      cases hd'
      obtain ⟨lay, nm', hj, hlay, hin', hjr, hnm, hcl, ha, -⟩ := h1 dir' d hd
      have hnmeq : nm' = nm := inArea_name hin' hin
      subst hnmeq
      have hok0 := (hok.1 dir' d hd)
      obtain ⟨lay0, nm0, hj0, hlay0, hin0, hjr0, hnm0, -, -, hco⟩ := hok0
      rw [hlay] at hlay0; cases hlay0
      refine ⟨lay, nm', hj, hlay, by rw [harea]; exact hin', hjr, hnm, hcl, walAbsD_named true ha, ?_⟩
      refine crashOkW_named hn hco fun m' hr => ⟨J, ?_⟩
      rw [hjr, hnm, regionCrashed_lastWrite hc hN hl hx hr, hJ]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hd'
      obtain ⟨lay, nm', hj, hlay, hin', rest⟩ := h1 dir' d' hd'
      exact ⟨lay, nm', hj, hlay, by rw [harea]; exact hin', rest⟩
  · rw [hw] at hn'
    by_cases he : dir' = dir
    · subst he; rw [GMap.lookup_insert_eq] at hn'; cases hn'
    · rwa [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hn'
  · intro dir' nm' hin' hn' m' hr J' hJ'
    rw [harea] at hin'
    rw [hw] at hn'
    by_cases he : dir' = dir
    · subst he; rw [GMap.lookup_insert_eq] at hn'; cases hn'
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hn'
      exact h5 dir' nm' hin' hn' m' hr J' hJ'
  · intro dd hdd m' hr
    rw [hdirs] at hdd
    exact h6 dd hdd m' hr

theorem crashOkA_mono {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {alt : Option WalLay} {cl : List Claim} {n0 n : Nat} (hn : n0 ≤ n)
    (h : CrashOkA C Mr d lay alt cl n0) : CrashOkA C Mr d lay alt cl n :=
  fun m' fo hr => h m' fo (regionCrashed_mono hn hr)

/-- `CrashOk` (no alternative) with `named` raised (as `crashOkW_named`). -/
theorem crashOkA_none_named {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n0 n : Nat} (hn : n0 ≤ n) (hok : CrashOkA C Mr d lay none cl n0)
    (hname : ∀ m', RegionCrashed cl n m' → ∃ J, m'.entry lay.jr lay.nm = some (.dir J)) :
    CrashOkA C Mr { d with named := true } lay none cl n := by
  intro m' fo hr hf hnm hw1
  rcases hok m' fo (regionCrashed_mono hn hr) hf hnm hw1 with hct | ⟨lay0, h0, -⟩
  · exact Or.inl (crashTo_named hct (hname m' hr))
  · cases h0

/-- **The directory keys with the WAL in `dir` named** (as `walsOk_named`). -/
theorem dirKeysOk_named {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n0 n : Nat}
    {K : GMap GoString (Ino × List GoString)} {c : Option GoString} (hn : n0 ≤ n)
    (hok : WalsOk C Mr R jr s Ls cl n0) (hk : DirKeysOk C Mr jr s Ls cl n0 K c)
    {dir nm : GoString} {d : WalDur}
    (hd : s.wal !! dir = some d) (hin : InArea s.area dir nm) {N : NameSet} {h : NamesH} {x : Nat}
    {e : LogEntry} {E : Ents} {J : Ino} (hc : (jr, N, h) ∈ cl) (hN : N.Mem nm)
    (hl : LastWrite h jr nm x e E) (hx : x < n) (hJ : E !! nm = some (.dir J)) :
    DirKeysOk C Mr jr (setNamed s dir) Ls cl n K c := by
  have hw : (setNamed s dir).wal = <[dir := { d with named := true }]> s.wal :=
    absDiskUpd_wal s dir _ d hd
  refine ⟨hk.1, fun dir' d' lay hd' hl' hcd => ?_, hk.2.2⟩
  rw [hw] at hd'
  by_cases he : dir' = dir
  · subst he
    rw [GMap.lookup_insert_eq] at hd'; cases hd'
    obtain ⟨lay1, nm', hj, hlay, hin', hjr, hnm, -, -, -⟩ := hok.1 dir' d hd
    rw [hl'] at hlay; cases hlay
    have hnmeq : nm' = nm := inArea_name hin' hin
    subst hnmeq
    exact crashOkA_none_named hn (hk.2.1 dir' d lay hd hl' hcd) fun m' hr => ⟨J, by
      rw [hjr, hnm, regionCrashed_lastWrite hc hN hl hx hr, hJ]⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hd'
    exact crashOkA_mono hn (hk.2.1 dir' d' lay hd' hl' hcd)

/-- **Strong absence at a bigger commit bound.** -/
theorem absentNone_mono {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n0 n : Nat} (hn : n0 ≤ n)
    (h : AbsentNone s jr cl n0) : AbsentNone s jr cl n := fun dir nm hin hnone =>
  ⟨(h dir nm hin hnone).1, fun m' hr => (h dir nm hin hnone).2 m' (regionCrashed_mono hn hr)⟩

/-- `WalsNamed` under a larger commit bound (fewer crashes). -/
theorem walsNamed_mono {Ls : GMap GoString WalLay} {cl : List Claim} {n0 n : Nat} (hn : n0 ≤ n)
    (h : WalsNamed Ls cl n0) : WalsNamed Ls cl n := fun dir lay hl =>
  ⟨(h dir lay hl).1, fun m' hr => (h dir lay hl).2 m' (regionCrashed_mono hn hr)⟩

/-- **Strong absence with the WAL in `dir` named** (its WAL-less names unchanged). -/
theorem absentNone_named {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat}
    (h : AbsentNone s jr cl n) (dir : GoString) : AbsentNone (setNamed s dir) jr cl n := by
  intro dir' nm hin hnone
  rw [show (setNamed s dir).area = s.area from absDiskUpd_area s dir _] at hin
  refine h dir' nm hin ?_
  unfold setNamed absDiskUpd at hnone
  cases hd : s.wal !! dir with
  | none => rw [hd] at hnone; exact hnone
  | some d =>
    rw [hd] at hnone
    by_cases he : dir' = dir
    · subst he; rw [GMap.lookup_insert_eq] at hnone; cases hnone
    · rwa [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hnone

theorem absLe_setNamed (s : AbsDiskState) (dir : GoString) : absLe s (setNamed s dir) :=
  absLe_upd s dir _ (fun d => ⟨Nat.le_refl _, Nat.le_refl _, fun _ => rfl⟩)

theorem walMapLe_setNamed (G : GMap GoString WalDur) (s : AbsDiskState) (dir : GoString)
    (hG : walMapLe G s.wal) : walMapLe G (setNamed s dir).wal :=
  walMapLe_upd G s dir _ (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, fun _ => rfl⟩) hG

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

theorem nameSet_ne_empty {N : NameSet} {b : GoString} (hb : N.Mem b) : N ≠ .only [] := by
  rintro rfl; simp [NameSet.Mem] at hb

/-- **Two claims of one directory holding one name are one claim** (`NamesCoh.disj`). -/
theorem osNames_same_name (R : Roots) (j : Ino) (N N' : NameSet) (dq dq' : DFrac) (h h' : NamesH)
    (b : GoString) (hb : N.Mem b) (hb' : N'.Mem b) {Em : CoPset} (hE : ↑osShN ⊆ Em) :
    ⊢ osSharedInv (L := L) R -∗ osNames (L := L) j N dq h -∗ osNames (L := L) j N' dq' h' ={Em}=∗
      ⌜N = N' ∧ h = h'⌝ ∗ osNames (L := L) j N dq h ∗ osNames (L := L) j N' dq' h' := by
  rw [osNames_of_ne dq h (nameSet_ne_empty hb), osNames_of_ne dq' h' (nameSet_ne_empty hb')]
  unfold osSharedInv
  iintro #Hsi H H'
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAn H with %h1
  icases gAuth_lookup _ _ _ _ _ _ $$ HAn H' with %h2
  have hN : N = N' := Classical.byContradiction fun hne =>
    hcoh.2.disj j N N' h h' b h1 h2 hne hb hb'
  subst hN
  rw [h1] at h2
  cases h2
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists Vs, Γn; iframe; ipureintro; exact hcoh
  imodintro
  iframe
  ipureintro; exact ⟨rfl, rfl⟩

/-- **The parent's fsync after `Create`'s rename: the WAL becomes named.** The invariant's contents
at `s` (the WAL in `dir = r/nm` present), the program's claim (a fraction) on names `N ∋ nm` whose last
writer of `nm` is the entry `x`, after which `nm` held a directory, and the commit bound `n > x`: the
contents at `setNamed s dir`, and `walNamed dir`. -/
theorem walInvBody_named (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir nm : GoString) (d : WalDur) (N : NameSet) (dq : DFrac) (h : NamesH)
    (x : Nat) (e : LogEntry) (E : Ents) (J : Ino) (n : Nat) {Em : CoPset}
    (hd : s.wal !! dir = some d) (hin : InArea r dir nm) (hN : N.Mem nm)
    (hl : LastWrite h jr nm x e E) (hx : x < n) (hJ : E !! nm = some (.dir J))
    (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗
      osNames (L := L) jr N dq h -∗ osCommitLb (L := L) n ={Em}=∗
      walInvBody (L := L) (W := W) C Mr R jr r (setNamed s dir) ∗ osNames (L := L) jr N dq h ∗
        walNamed (W := W) dir := by
  iintro Hb #Hsh Hn #Hc
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n0, %F, Hg, %Har, Hcl, #Hcm, Hlays, %Hok, %Hco, Hcr, Htl, %Han, %Hnm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  obtain ⟨N', h', hc', hN'⟩ := Hco nm hin.1
  have hmem : ((jr, N', h'), DFrac.own (1 : Qp).half) ∈
      cl.map (fun c => (c, DFrac.own (1 : Qp).half)) := List.mem_map_of_mem hc'
  unfold osClaims
  icases (BigSepL.bigSepL_mem_acc hmem) $$ Hcl with ⟨Hi, Hcl⟩
  imod osNames_same_name R jr N N' dq _ h h' nm hN hN' hE $$ Hsh Hn Hi with ⟨%Hk, Hn, Hi⟩
  obtain ⟨rfl, rfl⟩ := Hk
  ihave Hcl := Hcl $$ Hi
  have hin' : InArea s.area dir nm := by rw [Har]; exact hin
  have hok' := walsOk_named (n := max n0 n) (Nat.le_max_left _ _) Hok hd hin' hc' hN hl
    (Nat.lt_of_lt_of_le hx (Nat.le_max_right _ _)) hJ
  have hdn : (setNamed s dir).wal !! dir = some { d with named := true } := by
    rw [show (setNamed s dir).wal = _ from absDiskUpd_wal s dir _ d hd, GMap.lookup_insert_eq]
  imod walGhost_upd_lag (W := W) s (setNamed s dir) (walMapLe_setNamed · s dir)
    (absLe_setNamed s dir) (walKeysInArea_upd s dir _) $$ Hg with ⟨Hg, #Hp⟩
  imodintro
  isplitl [Hg Hcl Hlays Hcr Htl Hpk Hdk Hcp Hnms]
  · iexists Ls, cl, max n0 n, F
    iframe Hg Hcl Hlays
    isplitr
    · ipureintro; rw [show (setNamed s dir).area = s.area from absDiskUpd_area s dir _]; exact Har
    isplitr
    · rcases Nat.le_total n0 n with hle | hle
      · rw [Nat.max_eq_right hle]; iexact Hc
      · rw [Nat.max_eq_left hle]; iexact Hcm
    isplitr
    · ipureintro; exact hok'
    isplitr
    · ipureintro; exact Hco
    iframe Hcr
    isplitl [Htl]
    · iapply walTailsRes_mono C Mr s (setNamed s dir) Ls F ?_ $$ Htl
      intro dir' d' hd'
      by_cases hdd : dir' = dir
      · subst hdd; rw [hd] at hd'; cases hd'; exact ⟨_, hdn, rfl, rfl⟩
      · refine ⟨d', ?_, rfl, rfl⟩
        rw [show (setNamed s dir).wal = _ from absDiskUpd_wal s dir _ d hd,
          GMap.lookup_insert_ne _ _ (Ne.symm hdd)]
        exact hd'
    iframe Hpk
    isplitr
    · ipureintro
      refine ⟨absentNone_named (absentNone_mono (Nat.le_max_left _ _) Han.1) dir, fun dd hdd => Han.2 dd ?_⟩
      have hdirs : (setNamed s dir).dirs = s.dirs := by unfold setNamed absDiskUpd; rw [hd]
      rw [← hdirs]; exact hdd
    isplitr
    · ipureintro; exact walsNamed_mono (Nat.le_max_left _ _) Hnm
    isplitl [Hdk Hcp]
    · iexists K, cp
      iframe Hdk Hcp
      ipureintro
      exact dirKeysOk_named (n := max n0 n) (Nat.le_max_left _ _) Hok Hdko hd hin' hc' hN hl
        (Nat.lt_of_lt_of_le hx (Nat.le_max_right _ _)) hJ
    iframe Hnms; ipureintro; exact ⟨HAt, walsBounded_upd Hbd (fun _ => rfl)⟩
  iframe Hn
  unfold walNamed
  iexists (setNamed s dir), { d with named := true }
  iframe Hp
  ipureintro; exact ⟨hdn, rfl⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
