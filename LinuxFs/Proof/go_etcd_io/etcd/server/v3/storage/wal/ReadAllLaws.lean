/- Lean-first (no Rocq counterpart).

# The invariant laws `ReadAll` reads its WAL through (W3/W5 of `notes/wal-fsext-plan.md`, fourteenth session)

One statement, `WalReadState` (a hypothesis of `WAL.ReadAll.wp_proof` until the invariant's owner
proves it; no `sorry`), of two parts, both read at a program step, holding the WAL's key and the empty program half of the
tails' authority (`walReadTie`'s: no tail registered, so no change in flight on the WAL's files,
`walTailsRes_none`), and give what `readAll_success` (`ReadAllPure.lean`) takes.

* `WalTailIdle`: a WAL whose tail no handle has registered has its last segment's stream all written
  (`lay.wr` its length) and no resize window open on it (`TailExact`). **In the invariant now**
  (`walTailsRes`'s `WalTailIdle`, `Inv.lean`, fifteenth session) and read by `walInvBody_readIdle` below,
  which proves every part of `WalReadState` but the two that follow: a crash gives it (`WalsStart`), `Create`'s
  commit, and a handle's unregistration must (`Close` after its sync: W10). A `Save` that fails leaves its
  tail registered (the handle is lost with the lock token), so the law does not constrain a WAL with a
  half-written record.
* The cuts positive (`0 < b`; `walCutPos` allows a cut at 0, which `readAllFold_from` cannot read from;
  every real cut follows a `Save`). Not in the invariant: the cut must record it (`CutLay`'s `hcut` gives
  only `walCutPos`; `WAL__Save` knows `0 < |H|`, its history being `H ++ [save]`), through `WAL.cut.spec`,
  `CutAu`, `walTailsRes_cut`, and the crash (`WalsStart`) must keep it.
* `WalPinnedSegs`: the segments a handle pinned (`walReadTie`'s `gs`, the program's halves held) are the
  layout's from some position on (purges remove only earlier, unlocked, segments; nothing appends or cuts
  without the tail registered).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The WAL as `ReadAll` reads it** (hypothesis; see the file header): its state `d`, the invariant's
layout and directory names, the tail idle (`WalTailIdle`), the cuts positive, and the pinned segments the
layout's from `kk` on (`WalPinnedSegs`). -/
def WalReadState (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) : Prop :=
  ∀ (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (gs : List SegG),
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      walTailsFrag (W := W) ∅ -∗
      walOutFrag (W := W) ⟨gs.map (·.ino), [(j, .except X)], [dir]⟩ -∗
      ([∗list] g ∈ gs, osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) -∗
      ∃ (d : WalDur) (lay : WalLay) (hj : NamesH) (kk : Nat),
        ⌜s.wal !! dir = some d ∧ lay.j = j ∧ WalAbsD C Mr d lay hj.cur ∧ TailExact lay ∧
          lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧ (∀ b ∈ lay.cuts, 0 < b) ∧
          lay.segs.drop kk = gs⌝ ∗
        walInvBody (L := L) (W := W) C Mr R jr r s ∗ walTailsFrag (W := W) ∅ ∗
        walOutFrag (W := W) ⟨gs.map (·.ino), [(j, .except X)], [dir]⟩ ∗
        ([∗list] g ∈ gs, osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) g.om ∗
          osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs)

/-- The tails with the program's half empty: every WAL idle (`WalTailIdle` at `T = ∅`). -/
theorem walTailsRes_idle (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailsFrag (W := W) ∅ -∗
      ⌜∀ dir d lay, s.wal !! dir = some d → Ls !! dir = some lay → TailIdle C Mr d lay⌝ ∗
        walTailsRes (W := W) C Mr s Ls F ∗ walTailsFrag (W := W) ∅ := by
  unfold walTailsRes
  iintro ⟨%T, Ha, %Ho, %Hi, Hm⟩ Hf
  icases walTails_agree (W := W) T ∅ $$ Ha Hf with %hT
  subst hT
  iframe Hf
  isplitr
  · ipureintro
    intro dir d lay hd hl
    exact Hi dir d lay (GMap.lookup_empty _) hd hl
  iexists ∅
  iframe Ha Hm
  ipureintro; exact ⟨Ho, Hi⟩

/-- A WAL's key names its layout's directory (`DirKeysOk`). -/
theorem walDirKeys_lay (C : WalCodec) (Mr : WalMarshal) (jr : Ino) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat) (dir : GoString) (j : Ino)
    (X : List GoString) :
    ⊢ (∃ K c, walDirKeysAuth (W := W) K ∗ walCutAuth (W := W) c ∗ ⌜DirKeysOk C Mr jr s Ls cl n K c⌝) -∗
      walDirKey (W := W) dir j X -∗
      ⌜∃ lay, Ls !! dir = some lay ∧ lay.j = j⌝ ∗
        (∃ K c, walDirKeysAuth (W := W) K ∗ walCutAuth (W := W) c ∗ ⌜DirKeysOk C Mr jr s Ls cl n K c⌝) ∗
        walDirKey (W := W) dir j X := by
  iintro ⟨%K, %c, HKa, Hca, %HDK⟩ Hk
  icases walDirKey_lookup K dir j X $$ HKa Hk with %hK
  obtain ⟨lay, -, hl, hlj, -⟩ := HDK.1 dir j X hK
  iframe Hk
  isplitr
  · ipureintro; exact ⟨lay, hl, hlj⟩
  iexists K, c
  iframe HKa Hca
  ipureintro; exact HDK

/-- **The WAL as `ReadAll` reads it, but its pinned segments and its cuts' positivity** (proved; the rest
of `WalReadState`): at a step, the WAL's key and the empty program half of the tails' authority give the
invariant's `d`, layout and names with `WalAbsD`, and the tail idle (`walTailsRes`'s `WalTailIdle`). -/
theorem walInvBody_readIdle (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      walTailsFrag (W := W) ∅ -∗
      ∃ (d : WalDur) (lay : WalLay) (hj : NamesH),
        ⌜s.wal !! dir = some d ∧ lay.j = j ∧ WalAbsD C Mr d lay hj.cur ∧ TailIdle C Mr d lay⌝ ∗
        walInvBody (L := L) (W := W) C Mr R jr r s ∗ walDirKey (W := W) dir j X ∗
        walTailsFrag (W := W) ∅ := by
  iintro Hb Hk Hf
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    HK, %HAt, Hnms, %Hbd⟩
  icases walDirKeys_lay C Mr jr s Ls cl n dir j X $$ HK Hk with ⟨%hlay, HK, Hk⟩
  icases walTailsRes_idle C Mr s Ls F $$ Htl Hf with ⟨%hidle, Htl, Hf⟩
  obtain ⟨lay, hl, hlj⟩ := hlay
  have HW0 := HW
  obtain ⟨hW1, hW2, -⟩ := HW0
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases h : s.wal !! dir with
    | none => rw [hW2 dir h] at hl; cases hl
    | some d => exact ⟨d, rfl⟩
  obtain ⟨lay1, nm, hj, hl1, -, -, -, -, habs, -⟩ := hW1 dir d hd
  rw [hl] at hl1; cases hl1
  iexists d, lay, hj
  isplitr
  · ipureintro; exact ⟨hd, hlj, habs, hidle dir d lay hd hl⟩
  iframe Hk Hf
  iexists Ls, cl, n, F
  iframe
  ipureintro; exact ⟨Har, HW, HWC, Hab, HNm, HAt, Hbd⟩

end laws

end WalFs
end EtcdGrove
end Perennial
