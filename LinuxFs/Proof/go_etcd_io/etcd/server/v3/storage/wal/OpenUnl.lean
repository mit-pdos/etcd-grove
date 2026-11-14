/- Lean-first (no Rocq counterpart).

# `Open`'s commit: `unl` raised (`notes/wal-fsext-plan.md`, W3/W5)

`openAtIndex`'s update (write mode) raises the opened WAL's `unl` to `walOpenPos` (bookkeeping until
the lock model). No part of the invariant reads `unl` (`WalAbsD`, the crash conditions, the tails
read the history, the marks, the metadata, `named`, `cut`, `pur`), so the contents carry over to the
updated state (`walInvBody_unl`), the program's map following it (`walGhost_upd`).

* `unlSt s dir p`: the state with `dir`'s `unl` raised to `p`.
* `walAbsD_unl`, `walsOk_unl`, `dirKeysOk_unl`, ...: the pure parts at a WAL whose `unl` changed.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenPinTake

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- The state with `dir`'s `unl` raised to `p` (`openAtIndex`'s update in write mode). -/
def unlSt (s : AbsDiskState) (dir : GoString) (p : Nat) : AbsDiskState :=
  absDiskUpd s dir (fun d => { d with unl := max d.unl p })

theorem walAbsD_unl {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (u : Nat) (h : WalAbsD C Mr d lay ents) : WalAbsD C Mr { d with unl := u } lay ents :=
  ⟨h.names, h.cuts, h.nameBound, h.cut, h.metas, h.intact, h.last, h.synced, h.lastSynced, h.fit,
    h.tailStop, h.nonempty⟩

theorem crashOkA_unl {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {alt : Option WalLay} {cl : List Claim} {n : Nat} (u : Nat) (h : CrashOkA C Mr d lay alt cl n) :
    CrashOkA C Mr { d with unl := u } lay alt cl n := h

theorem crashOkW_unl {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} (u : Nat) (h : CrashOkW C Mr d lay cl n) :
    CrashOkW C Mr { d with unl := u } lay cl n := by
  obtain ⟨alt, halt, hc⟩ := h
  refine ⟨alt, fun lay0 h0 => ?_, crashOkA_unl u hc⟩
  obtain ⟨⟨ents0, ha⟩, rest⟩ := halt lay0 h0
  exact ⟨⟨ents0, walAbsD_unl u ha⟩, rest⟩

theorem tailBound_unl {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} (u : Nat)
    (h : TailBound C Mr d lay) : TailBound C Mr { d with unl := u } lay := h.congr rfl rfl

/-- The lookups of `unlSt`: `dir`'s WAL with its `unl` raised, the others as before. -/
theorem unlSt_lookup (s : AbsDiskState) (dir : GoString) (p : Nat) (k : GoString) :
    (unlSt s dir p).wal !! k = (s.wal !! k).map (fun d => if k = dir then { d with unl := max d.unl p } else d) := by
  unfold unlSt absDiskUpd
  cases hd : s.wal !! dir with
  | none =>
    simp only
    cases hk : s.wal !! k with
    | none => rfl
    | some d =>
      simp only [Option.map_some]
      by_cases e : k = dir
      · subst e; rw [hd] at hk; cases hk
      · rw [if_neg e]
  | some d0 =>
    simp only
    by_cases e : k = dir
    · subst e; rw [GMap.lookup_insert_eq, hd]; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]
      cases s.wal !! k <;> simp [e]

theorem unlSt_some {s : AbsDiskState} {dir : GoString} {p : Nat} {k : GoString} {d' : WalDur}
    (h : (unlSt s dir p).wal !! k = some d') : ∃ d u, s.wal !! k = some d ∧ d' = { d with unl := u } := by
  rw [unlSt_lookup] at h
  cases hk : s.wal !! k with
  | none => rw [hk] at h; cases h
  | some d =>
    rw [hk, Option.map_some, Option.some.injEq] at h
    by_cases e : k = dir
    · rw [if_pos e] at h; exact ⟨d, _, rfl, h.symm⟩
    · rw [if_neg e] at h; exact ⟨d, d.unl, rfl, by rw [← h]⟩

theorem unlSt_some' {s : AbsDiskState} {dir : GoString} {p : Nat} {k : GoString} {d : WalDur}
    (h : s.wal !! k = some d) : ∃ u, (unlSt s dir p).wal !! k = some { d with unl := u } := by
  rw [unlSt_lookup, h, Option.map_some]
  by_cases e : k = dir
  · rw [if_pos e]; exact ⟨_, rfl⟩
  · rw [if_neg e]; exact ⟨d.unl, rfl⟩

theorem unlSt_none {s : AbsDiskState} {dir : GoString} {p : Nat} {k : GoString} :
    (unlSt s dir p).wal !! k = none ↔ s.wal !! k = none := by
  rw [unlSt_lookup]; cases s.wal !! k <;> simp

theorem unlSt_area (s : AbsDiskState) (dir : GoString) (p : Nat) : (unlSt s dir p).area = s.area :=
  absDiskUpd_area s dir _

theorem unlSt_dirs (s : AbsDiskState) (dir : GoString) (p : Nat) : (unlSt s dir p).dirs = s.dirs := by
  unfold unlSt absDiskUpd; cases s.wal !! dir <;> rfl

theorem walsOk_unl {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} (dir : GoString) (p : Nat)
    (h : WalsOk C Mr R jr s Ls cl n) : WalsOk C Mr R jr (unlSt s dir p) Ls cl n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun dir' d' hd' => ?_, fun dir' hn => h2 dir' (unlSt_none.1 hn), h3, h4,
    fun dir' nm hin hn => h5 dir' nm (by rw [← unlSt_area s dir p]; exact hin) (unlSt_none.1 hn),
    fun dd hdd => h6 dd (by rw [← unlSt_dirs s dir p]; exact hdd)⟩
  obtain ⟨d, u, hd, rfl⟩ := unlSt_some hd'
  obtain ⟨lay, nm, hj, hl, hin, hjr, hnm, hc, habs, hcr⟩ := h1 dir' d hd
  exact ⟨lay, nm, hj, hl, by rw [unlSt_area]; exact hin, hjr, hnm, hc, walAbsD_unl u habs,
    crashOkW_unl u hcr⟩

theorem dirKeysOk_unl {C : WalCodec} {Mr : WalMarshal} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {K : GMap GoString (Ino × List GoString)}
    {c : Option GoString} (dir : GoString) (p : Nat) (h : DirKeysOk C Mr jr s Ls cl n K c) :
    DirKeysOk C Mr jr (unlSt s dir p) Ls cl n K c := by
  refine ⟨h.1, fun dir' d' lay hd' hl hc => ?_, h.2.2⟩
  obtain ⟨d, u, hd, rfl⟩ := unlSt_some hd'
  exact crashOkA_unl u (h.2.1 dir' d lay hd hl hc)

theorem absentNone_unl {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat} (dir : GoString)
    (p : Nat) (h : AbsentNone s jr cl n) : AbsentNone (unlSt s dir p) jr cl n :=
  fun dir' nm hin hn => h dir' nm (by rw [← unlSt_area s dir p]; exact hin) (unlSt_none.1 hn)

theorem dirsAvoid_unl {R : Roots} {jr : Ino} {s : AbsDiskState} (dir : GoString) (p : Nat)
    (h : DirsAvoid R jr s) : DirsAvoid R jr (unlSt s dir p) :=
  fun dd hdd => h dd (by rw [← unlSt_dirs s dir p]; exact hdd)

theorem absLe_unlSt (s : AbsDiskState) (dir : GoString) (p : Nat) : absLe s (unlSt s dir p) :=
  absLe_upd s dir _ (fun _ => ⟨Nat.le_refl _, Nat.le_refl _, id⟩)

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- The tails at `unlSt` (the histories and metadata unchanged). -/
theorem walTailsRes_unl (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) (dir : GoString) (p : Nat) :
    walTailsRes (W := W) C Mr s Ls F ⊢ walTailsRes (W := W) C Mr (unlSt s dir p) Ls F := by
  refine walTailsRes_mono C Mr s _ Ls F (fun dir' d hd => ?_)
  obtain ⟨u, hu⟩ := unlSt_some' (dir := dir) (p := p) hd
  exact ⟨_, hu, rfl, rfl⟩

/-- **`Open`'s commit** (see the file header): the contents at `unlSt s dir p`, the program's map
set to its WAL map. -/
theorem walInvBody_unl (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (p : Nat) (M : GMap GoString WalDur) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walOwn (W := W) M ==∗
      ⌜walMapLe M s.wal⌝ ∗ walInvBody (L := L) (W := W) C Mr R jr r (unlSt s dir p) ∗
        walOwn (W := W) (unlSt s dir p).wal ∗ walPast (W := W) (unlSt s dir p) := by
  iintro Hb HM
  iunfold walInvBody at Hb
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, HKa, Hca, %HDK⟩, %HAt, Hnms⟩
  imod walGhost_upd (W := W) s (unlSt s dir p) M (absLe_unlSt s dir p) (walKeysInArea_upd s dir _)
    $$ Hg HM with ⟨%hM, Hg, HM, #Hp⟩
  ihave Htl := walTailsRes_unl (W := W) C Mr s Ls F dir p $$ Htl
  imodintro
  iframe HM Hp
  isplitr
  · ipureintro; exact hM
  unfold walInvBody
  iexists Ls, cl, n, F
  iframe Hg Hcl Hcm Hlays HCR Htl Hpk HKa Hca Hnms
  ipureintro
  exact ⟨by rw [unlSt_area]; exact Har, walsOk_unl dir p HW, HWC,
    ⟨absentNone_unl dir p Hab.1, dirsAvoid_unl dir p Hab.2⟩, HNm, dirKeysOk_unl dir p HDK, HAt⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
