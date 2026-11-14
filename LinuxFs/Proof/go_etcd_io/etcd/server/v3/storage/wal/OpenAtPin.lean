/- Lean-first (no Rocq counterpart).

# `openAtIndex`'s pin, at its first step (W3/W5 of `notes/wal-fsext-plan.md`, twelfth session)

`openAtIndex` commits its update and pins its WAL at one step (the first call, `startSnap.Clone()`,
`wp_notCrashed_acc`): it opens `walInv`, reads the area at the WAL's name from the program's area
claim (`walInvBody_areaAt`), opens the client's update, and

* if the WAL is absent, commits `Q none` unchanged, keeping the lock token (the area holds nothing at
  `nm`: `selectWALFiles.specAbsent` then fails);
* if it exists, commits (write mode: `unl` raised, `walInvBody_unl`; read mode: unchanged) and takes
  the WAL's halves out of the parked state from the selected position on (`walOpenK`, what
  `selectWALFiles` will compute).

**The pin's hypothesis `WalPinSized`** (an obligation for the invariant's owner; the plan's W3/W5 log,
twelfth session): `walInvBody_pin` (`OpenPinTake.lean`, proved) gives everything but two facts the
invariant does not hold yet: **a path to the WAL directory** (`osPathS R dir (own q) lay.j`, which
`selectWALFiles`, `openWALFiles` and the pipeline need: a spine is made of `.only [c]` claim fractions,
and the area claim holds the WAL's name `nm` among all the area's names, half the program's, so no
fraction of an `.only [nm]` claim is to be had) and **the segments' size bound** (`|g.bs| + 2^12 <
2^62`, `walDecFiles_mk`'s, which the decoder's reads need). `WalPinSized` is `walInvBody_pin`'s statement
with both added.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenUnl
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenPin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.searchIndex

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The position `openAtIndex` opens its WAL from** (`selectWALFiles`' `searchIndex` over the
layout's names; the whole layout dropped if there is none, which `selectWALFiles` then reports). -/
def walOpenK (idx : w64) (lay : WalLay) : Nat :=
  (walSearch ((lay.segs.map (·.name)).map walNameIdx) idx).getD lay.segs.length

theorem walAuMask_sub_top' : walAuMask ⊆ (⊤ : CoPset) \ ↑walN := by
  intro p hp
  unfold walAuMask at hp
  obtain ⟨-, hn⟩ := LawfulSet.mem_diff.1 hp
  exact LawfulSet.mem_diff.2 ⟨CoPset.mem_full, hn⟩

theorem walN_osShN_top' : (↑osShN : CoPset) ⊆ (⊤ : CoPset) \ ↑walN := by
  have h2 : (↑walN : CoPset) ## ↑osShN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  exact LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun hn => h2 p ⟨hn, hp⟩⟩

/-- The real WAL with `unl` raised stays above the program's copy raised the same way. -/
theorem walDurLe_unl {dc ds : WalDur} (p : Nat) (h : walDurLe dc ds) :
    walDurLe { dc with unl := max dc.unl p } { ds with unl := max ds.unl p } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, by simp only [h2], h3, h4, h5, h6, h7, h8⟩

theorem unlSt_lookup_self (s : AbsDiskState) (dir : GoString) (p : Nat) (d : WalDur)
    (hd : s.wal !! dir = some d) :
    (unlSt s dir p).wal !! dir = some { d with unl := max d.unl p } := by
  rw [unlSt_lookup, hd]
  simp

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **What the pin hands the program** (see the file header): `walInvBody_pin`'s outputs and the
segments' size bound. -/
def walPinOut (C : WalCodec) (Mr : WalMarshal) (jr : Ino) (dir : GoString) (d : WalDur)
    (k : WalLay → Nat) (write : Bool) : IProp GF :=
  iprop(∃ (lay : WalLay) (X : List GoString) (hj : NamesH),
    ⌜lay.jr = jr ∧ (∀ b ∈ X, walNameP b = false) ∧
      ClaimCoh hj lay.j (.except X) ∧ WalAbsD C Mr d lay hj.cur ∧
      (lay.segs.map (·.ino)).Nodup ∧ SegsNamed lay.segs hj.cur ∧
      (∀ g ∈ lay.segs, g.bs.length + 2 ^ 12 < 2 ^ 62)⌝ ∗ walDirKey (W := W) dir lay.j X ∗
    walLockedTok (W := W) ∗ walTailsFrag (W := W) ∅ ∗
    walOutFrag (W := W) ⟨(lay.segs.drop (k lay)).map (·.ino), [(lay.j, .except X)],
      if write then [dir] else []⟩ ∗
    ([∗list] g ∈ lay.segs.drop (k lay), segRes (L := L) g) ∗
    osNames (L := L) lay.j (.except X) (DFrac.own (1 : Qp).half) hj ∗
    (if write then walTmpsRes (hG := ⟨G, L⟩) lay.j else emp))

/-- **The pin with the segments' size bound** (hypothesis; see the file header). -/
def WalPinSized (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) : Prop :=
  ∀ (s : AbsDiskState) (dir : GoString) (d : WalDur), s.wal !! dir = some d →
    ∀ (k : WalLay → Nat) (write : Bool),
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walUnlockedTok (W := W) ==∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walPinOut (L := L) (W := W) C Mr jr dir d k write

/-- **A path to a WAL directory** (hypothesis, a stand-in for the law `wal-path13` proves over a
per-WAL-name claim; the coordinator's decision of 2026-11-14): a holder of the WAL's key (`walDirKey dir
j X`: the WAL of `dir` has its directory at `j`) gets, at a program step, a fraction of a path to `j`,
which it may keep; the area's spine framed. Swap: replace `WalDirPathLaw` by the real law's statement
where `openAtIndex`'s proof applies it (one call, in `wp_openAt_pin`'s step). -/
def WalDirPathLaw (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) : Prop :=
  ∀ (dir : GoString) (j : Ino) (X : List GoString) (qp : Qp),
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walDirKey (W := W) dir j X -∗ osPathS (L := L) R r (DFrac.own qp) jr ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ osPathS (L := L) R r (DFrac.own qp) jr ∗
      ∃ q : Qp, osPathS (L := L) R dir (DFrac.own q) j

/-- The program's map is below the invariant's state. -/
theorem walInvBody_mapLe (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (M : GMap GoString WalDur) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walOwn (W := W) M -∗
      ⌜walMapLe M s.wal⌝ ∗ walInvBody (L := L) (W := W) C Mr R jr r s ∗ walOwn (W := W) M := by
  iintro Hb HM
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
  icases walOwn_agree s M $$ Hg HM with %HMs
  iframe HM
  isplitr
  · ipureintro; exact HMs
  iexists Ls, cl, n, F
  iframe

/-- **`openAtIndex`'s update and pin** (see the file header). -/
theorem walInv_openAt (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (hpin : WalPinSized (L := L) (W := W) C Mr R jr r) (dir nm : GoString) (N : NameSet) (dq : DFrac)
    (h : NamesH) (write : Bool) (idx : w64) (Q : Option WalDur → IProp GF)
    (hin : InArea r dir nm) (hN : N.Mem nm) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ walUnlockedTok (W := W) -∗
      (AU <{ ∃∃ o : Option WalDur, walDirIs (W := W) dir o }> @ walAuMask, ∅
        <{ walDirIs (W := W) dir (if write then o.map (fun d =>
            { d with unl := max d.unl (walOpenPos (d.H.map WalOpG.toM) idx) }) else o), COMM Q o }>) -∗
      osNames (L := L) jr N dq h ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ osNames (L := L) jr N dq h ∗ ∃ o : Option WalDur, Q o ∗
        ((⌜o = none ∧ h.cur !! nm = none⌝ ∗ walUnlockedTok (W := W)) ∨
         (⌜o ≠ none⌝ ∗ ∃ d, walPinOut (L := L) (W := W) C Mr jr dir d (walOpenK idx) write)) := by
  iintro #Hinv #Hsi Hnc Hu Hau Hn
  imod walInv_open C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_areaAt C Mr R jr r s dir nm N dq h hin hN walN_osShN_top' $$ Hb Hsi Hn
    with ⟨Hb, Hn, %Hat⟩
  ihave Hau := atomic_update_mask_weaken walAuMask_sub_top' $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%o, Ho, Hucl⟩
  unfold walDirIs
  icases Ho with ⟨%M, HM, %HMd⟩
  icases walInvBody_mapLe C Mr R jr r s M $$ Hb HM with ⟨%HMs, Hb, HM⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  cases o with
  | none =>
    have hMd : M !! dir = none := (walOptLe_none_iff _).1 HMd
    have hsd : s.wal !! dir = none := by
      have := HMs dir; rw [hMd] at this; exact (walOptLe_none_iff _).1 this
    imod Hcommit $$ [HM] with HQ
    · iexists M; iframe HM; ipureintro
      cases write <;> exact HMd
    imod Hcl $$ [Hb] with -
    · iexists s; iexact Hb
    imodintro
    iframe Hnc Hn
    iexists none
    iframe HQ
    ileft
    iframe Hu
    ipureintro; exact ⟨rfl, Hat.1 hsd⟩
  | some dc =>
    obtain ⟨d0, hM0, hle0⟩ := (walOptLe_some_iff _ _).1 HMd
    obtain ⟨ds, hsd, hle⟩ : ∃ ds, s.wal !! dir = some ds ∧ walDurLe dc ds := by
      have h1 := HMs dir
      rw [hM0] at h1
      obtain ⟨ds, hds, hle1⟩ := (walOptLe_some_iff _ _).1 h1
      exact ⟨ds, hds, walDurLe_trans hle0 hle1⟩
    cases write with
    | false =>
      imod Hcommit $$ [HM] with HQ
      · iexists M; iframe HM; ipureintro; exact HMd
      imod hpin s dir ds hsd (walOpenK idx) false $$ Hb Hu with ⟨Hb, Hp⟩
      imod Hcl $$ [Hb] with -
      · iexists s; iexact Hb
      imodintro
      iframe Hnc Hn
      iexists (some dc)
      iframe HQ
      iright
      isplitr
      · ipureintro; simp
      iexists ds; iexact Hp
    | true =>
      imod walInvBody_unl C Mr R jr r s dir (walOpenPos (dc.H.map WalOpG.toM) idx) M $$ Hb HM
        with ⟨-, Hb, HM, -⟩
      have hsd' := unlSt_lookup_self s dir (walOpenPos (dc.H.map WalOpG.toM) idx) ds hsd
      imod Hcommit $$ [HM] with HQ
      · iexists (unlSt s dir (walOpenPos (dc.H.map WalOpG.toM) idx)).wal
        iframe HM
        ipureintro
        simp only [ite_true, Option.map_some, hsd', walOptLe]
        exact walDurLe_unl _ hle
      imod hpin _ dir _ hsd' (walOpenK idx) true $$ Hb Hu with ⟨Hb, Hp⟩
      imod Hcl $$ [Hb] with -
      · iexists _; iexact Hb
      imodintro
      iframe Hnc Hn
      iexists (some dc)
      iframe HQ
      iright
      isplitr
      · ipureintro; simp
      iexists _; iexact Hp

end iris

end WalFs
end EtcdGrove
end Perennial

end
