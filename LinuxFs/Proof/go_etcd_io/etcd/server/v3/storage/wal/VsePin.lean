/- Lean-first (no Rocq counterpart).

# `ValidSnapshotEntries`' pin of every segment (W8 of `notes/wal-fsext-plan.md`)

`validSnapshotEntries` reads the WAL directory's names and opens every segment read-only, from the first.
As `Repair`'s (`RepairPin.lean`, which pins the last segment), the proof commits the client's update
unchanged and pins the WAL at one ghost step, here every segment (`walInvBody_pinIdle` at `k = 0`), in read
mode (no pipeline names): `walInv_openAll`. It does so once, before `ValidSnapshotEntries`' retry loop, so
that every attempt reads the same pinned segments; the put-back after the loop is `walInv_unpin` in read
mode over every segment (`walInv_unpinAll`). Besides the pin, the client's state `o` is below the pinned
one (`walOptLe`): the same history and read position, so the result's `walValidSnaps` is the client's.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairPin

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- The pure facts of the pin of every segment: the layout `lay` of the WAL `d` in the directory
`lay.j` (its claim `(lay.j, .except X, hj)`), its tail idle. -/
def VsePinOk (C : WalCodec) (Mr : WalMarshal) (jr : Ino) (d : WalDur) (lay : WalLay) (X : List GoString)
    (hj : NamesH) : Prop :=
  lay.jr = jr ∧ (∀ b ∈ X, walNameP b = false) ∧ ClaimCoh hj lay.j (.except X) ∧
    WalAbsD C Mr d lay hj.cur ∧ TailIdle C Mr d lay ∧ (lay.segs.map (·.ino)).Nodup ∧
    SegsNamed lay.segs hj.cur

/-- **What the pin of every segment hands the program**: the WAL's key, the lock token, the tails' and
names' program halves, the out record of the segments and of the directory's claim, the program's
halves of every segment and of the claim. -/
def walPinAllRes (dir : GoString) (lay : WalLay) (X : List GoString) (hj : NamesH) : IProp GF :=
  iprop(walDirKey (W := W) dir lay.j X ∗ walLockedTok (W := W) ∗
    (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) ∗
    walOutFrag (W := W) ⟨lay.segs.map (·.ino), [(lay.j, .except X)], []⟩ ∗
    ([∗list] g ∈ lay.segs, segRes (L := L) g) ∗
    osNames (L := L) lay.j (.except X) (DFrac.own (1 : Qp).half) hj)

/-- **The pin of every segment** (`walInvBody_pinIdle` at `k = 0`). -/
theorem walInvBody_pinAll (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (d : WalDur) (hd : s.wal !! dir = some d) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walUnlockedTok (W := W) ==∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ ∃ (lay : WalLay) (X : List GoString) (hj : NamesH),
        ⌜VsePinOk C Mr jr d lay X hj⌝ ∗ walPinAllRes (L := L) (W := W) dir lay X hj := by
  iintro Hb Hu
  imod walInvBody_pinIdle C Mr R jr r s dir d hd (fun _ => 0) $$ Hb Hu with
    ⟨%lay, %X, %hj, %hp, Hkey, Hb, Hl, Htf, Hnf, Ho, HS, Hj⟩
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := hp
  simp only [List.drop_zero]
  imodintro
  iframe Hb
  iexists lay, X, hj
  isplitr
  · ipureintro; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  unfold walPinAllRes
  iframe

/-- **`ValidSnapshotEntries`' update and pin** (see the file header): the update committed unchanged;
the WAL absent (the area holds nothing at `nm`, the token kept), or the pin of every segment of the WAL
`d`, the client's state below it. -/
theorem walInv_openAll (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir nm : GoString) (N : NameSet) (dq : DFrac)
    (h : NamesH) (Wn : List GoString) (Q : Option WalDur → IProp GF)
    (hin : InArea r dir nm) (hN : N.Mem nm ∨ nm ∈ Wn) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ walUnlockedTok (W := W) -∗
      (AU <{ ∃∃ o : Option WalDur, walDirIs (W := W) dir o }> @ walAuMask, ∅
        <{ walDirIs (W := W) dir o, COMM Q o }>) -∗
      osNames (L := L) jr N dq h -∗ walSplitFrag (W := W) Wn ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ osNames (L := L) jr N dq h ∗ walSplitFrag (W := W) Wn ∗
      ∃ o : Option WalDur, Q o ∗
        ((⌜o = none ∧ N.Mem nm ∧ h.cur !! nm = none⌝ ∗ walUnlockedTok (W := W)) ∨
         (∃ (d : WalDur) (lay : WalLay) (X : List GoString) (hj : NamesH),
           ⌜walOptLe o (some d) ∧ VsePinOk C Mr jr d lay X hj⌝ ∗
           walPinAllRes (L := L) (W := W) dir lay X hj)) := by
  iintro #Hinv #Hsi Hnc Hu Hau Hn Hsf
  imod walInv_open C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_areaAt C Mr R jr r s dir nm N dq h Wn hin hN walN_osShN_top' $$ Hb Hsi Hn Hsf
    with ⟨Hb, Hn, Hsf, %Hat⟩
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
  imod Hcommit $$ [HM] with HQ
  · iexists M; iframe HM; ipureintro; exact HMd
  cases o with
  | none =>
    have hMd : M !! dir = none := (walOptLe_none_iff _).1 HMd
    have hsd : s.wal !! dir = none := by
      have := HMs dir; rw [hMd] at this; exact (walOptLe_none_iff _).1 this
    imod Hcl $$ [Hb] with -
    · iexists s; iexact Hb
    imodintro
    iframe Hnc Hn Hsf
    iexists none
    iframe HQ
    ileft
    iframe Hu
    ipureintro; exact ⟨rfl, Hat hsd⟩
  | some dc =>
    obtain ⟨d0, hM0, hle0⟩ := (walOptLe_some_iff _ _).1 HMd
    obtain ⟨ds, hsd, hle1⟩ : ∃ ds, s.wal !! dir = some ds ∧ walDurLe d0 ds := by
      have h1 := HMs dir
      rw [hM0] at h1
      exact (walOptLe_some_iff _ _).1 h1
    imod walInvBody_pinAll C Mr R jr r s dir ds hsd $$ Hb Hu with ⟨Hb, %lay, %X, %hj, %hp, Hp⟩
    imod Hcl $$ [Hb] with -
    · iexists s; iexact Hb
    imodintro
    iframe Hnc Hn Hsf
    iexists (some dc)
    iframe HQ
    iright
    iexists ds, lay, X, hj
    iframe Hp
    ipureintro; exact ⟨walDurLe_trans hle0 hle1, hp⟩

/-- **The put-back of every pinned segment, unchanged** (`walInv_unpin` in read mode). -/
theorem walInv_unpinAll (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (lay : WalLay) (X : List GoString) (hj : NamesH)
    (hS : ∀ g ∈ lay.segs, g.om.size = g.bs.length) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walPinAllRes (L := L) (W := W) dir lay X hj ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walUnlockedTok (W := W) := by
  iintro #Hinv Hnc Hp
  unfold walPinAllRes
  icases Hp with ⟨#Hk, Hl, Htf, Ho, HS, Hn⟩
  iapply walInv_unpin C Mr R jr r dir lay.j X hj lay.segs false hS $$ Hinv Hnc Hl Htf
    [Ho] HS Hn [] Hk
  · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Ho
  · simp only [Bool.false_eq_true, ↓reduceIte]; iempintro

end iris

end WalFs
end EtcdGrove
end Perennial
