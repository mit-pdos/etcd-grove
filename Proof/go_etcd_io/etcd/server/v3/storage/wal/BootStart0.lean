/- Lean-first (no Rocq counterpart).

# The WAL's start at the first boot (`notes/wal-fsext-w4c-plan.md`, "W4c U3 log")

`walStart_boot0`: the first generation's `walStart` (`walInv_alloc`'s first premise) over the boot
tree `m`, the WAL state `walBoot0St r` (no WAL, the area durable), from the WAL's ghost state's
allocation (`walGhost_init`, the steps' bound from `⧖ 0`). The disk premise: **no entry at any WAL
name of the area** (`hnone`; a WAL found at the first boot is excluded, as `absDiskInitOk` excluded it:
it may hold an index `2^64-1` or be named by an older etcd, the C6 gate), and the area is a root
(`hr`, so that it is durable: `BootPure`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BootPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Crash

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The first boot's `WalsStart`**: no layout; no entry at a WAL name of the area; the area, the
only durable directory, a root. -/
theorem walsStart_boot0 (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (m : Tree) (hR : RootsOk R) (hr : (r, jr) ∈ R)
    (hnone : ∀ nm, walNameOk nm → m.entry jr nm = none) :
    WalsStart C Mr R jr (walBoot0St r) ∅ m := by
  refine ⟨fun dir d hd => by simp [walBoot0St] at hd, fun _ _ => GMap.lookup_empty _,
    fun dir nm hin _ => hnone nm hin.1, fun dd hd => ?_, fun dir lay hl => by simp at hl,
    fun dir lay hl => by simp at hl⟩
  obtain ⟨j, hj⟩ := walBoot0St_dirsRoots hr dd hd
  exact ⟨j, lookupH_root hR hj m⟩

theorem walKeysInArea_boot0 (r : GoString) : walKeysInArea (walBoot0St r) := by
  intro k d hd; simp [walBoot0St] at hd

end pure

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **The first generation's start**: fresh ghost names for the WAL state `walBoot0St r`, its start
over the boot tree `m` (no segment), its past, the lock and crash tokens, and the program's map (empty:
no WAL, `walAbsent` of every directory). -/
theorem walStart_boot0 (hPre : AbsDiskGpreS GF) (L : GooseLocalGS GF) (C : WalCodec)
    (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (m : Tree) (hR : RootsOk R)
    (hr : (r, jr) ∈ R) (hnone : ∀ nm, walNameOk nm → m.entry jr nm = none) :
    ⊢@{IProp GF} |==> ∃ W : WalGS GF, ⌜W.roots = R⌝ ∗ walStart L W C Mr R jr r (walBoot0St r) m ∗
      walPast (W := W) (walBoot0St r) ∗ walUnlockedTok (W := W) ∗ walCrashTok (W := W) ∗
      walOwn (W := W) ∅ ∗ walIncQ (W := W) ∅ := by
  imod preceipt_zero (GF := GF) with #H0
  ihave #Hst : walStepsLb (G := G) (walBoot0St r) $$ [H0]
  · unfold walStepsLb
    iexists 0
    iframe H0
    ipureintro
    intro dir d hd; simp [walBoot0St] at hd
  imod walGhost_init hPre R (walBoot0St r) (walKeysInArea_boot0 r) $$ Hst with
    ⟨%W, %hWR, Hg, Hown, HIq, #Hp, Hu, Hc, Hcr, Ht, Hpk, Hdk, Hcp, Hpo, Hnm, Hnw, Hnwf, Hlt⟩
  imodintro
  iexists W
  isplitr
  · ipureintro; exact hWR
  ihave #Hp' : walPast (W := W) (walBoot0St r) $$ []
  · unfold walPast; iexists ∅; iexact Hp
  iframe Hp' Hu Hc HIq
  isplitr [Hown]
  rotate_left
  · rw [show (∅ : GMap GoString WalDur) = (walBoot0St r).wal from rfl]
    iexact Hown
  unfold walStart
  iexists ∅, [], (fun _ => none)
  iframe Hg Hcr Ht Hpk Hdk Hcp Hpo Hnm Hnw Hnwf Hlt
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  ipureintro
  refine ⟨List.nodup_nil, fun i hi => (by cases hi), ?_, walsStart_boot0 C Mr R jr r m hR hr hnone,
    fun dir lay hl => by simp at hl⟩
  have h0 : (FiniteMap.toList (∅ : GMap GoString WalLay)) = [] := GMap.toList_empty
  simp [segsAll, h0]

end boot

end WalFs
end EtcdGrove
end Perennial

end
