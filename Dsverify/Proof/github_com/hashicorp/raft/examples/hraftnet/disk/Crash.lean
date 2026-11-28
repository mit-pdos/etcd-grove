/-
(hraft_robust R3) **`diskCrash`**, `DISKCRASH.md`'s statement: at a crash, the disk's invariant (opened with
its crash token and closed on its crashed side) and `durable`'s crash lemma (`durInv_crash`, on `g.f`) give
the file's contents for the next generation's boot (`durFound`, `durFoundTmp`, the rest of the crash), and
what they hold: the committed state (`imgHolds v ⟨A, S⟩`), or, a write's window open, the write's result
with its window resource back, or, in the first start's `Fresh` (the `fresh` window), the caller's `Wf` back
(the image unconstrained). `A`/`S` are the client's views, agreed with the invariant's halves and dropped.
(One later credit strips the invariant's contents; `DISKCRASH.md` has none.)
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Inv
public import Dsverify.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Crash

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open Iris Iris.BI Iris.ProofMode Iris.Std github_com.hashicorp.raft proto EtcdGrove Fs

/-- `durable`'s namespace is open with the disk's invariant open. -/
theorem durN_sub_diff : (↑DurFs.durN : CoPset) ⊆ ⊤ \ ↑diskN := by
  intro x hx
  rw [Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h => diskN_not_durN x h hx⟩

set_option maxRecDepth 100000 in
/-- The shared os invariant's namespace is open with the disk's invariant open. -/
theorem osShN_sub_diff : (↑osShN : CoPset) ⊆ ⊤ \ ↑diskN := by
  intro x hx
  rw [Std.LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h => ?_⟩
  have h1 := nclose_subseteq' _ (mask_ndot_ne' nroot "hraftstore" "osfsShared" (by decide)) x h
  rw [Std.LawfulSet.mem_diff] at h1
  exact h1.2 hx

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- **The disk's crash lemma** (see the file header). -/
theorem diskCrash (Q : OsState → OsState → Prop) (L' : GooseLocalGS GF) (g : DiskGen)
    (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF) (Dl : List Ino) (tt : Bool) (V' : Hist)
    (A : LogAbs) (S : StableAbs)
    (hD : ∀ i ∈ Dl, V'.now.entry g.f.J g.f.b ≠ some (.file i) ∧ V'.now.entry g.f.J g.f.tb ≠ some (.file i)) :
    ⊢ diskInv g Wl Ws Wf -∗ crashed (hC := hG.goose_localGS.goose_crashGS) -∗ token g.γk -∗ £ 1 -∗
      DurFs.durInv (L := hG.goose_localGS) g.γd g.f -∗ DurFs.durCrashTok (GF := GF) g.γd -∗
      osSharedInv (L := hG.goose_localGS) g.R -∗
      diskOwnL g A -∗ diskOwnS g S -∗
      crashRest Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) Dl tt V' ={⊤}=∗
      ∃ (v : Option GoString) (Dl' : List Ino),
        ⌜∀ i ∈ Dl', V'.now.entry g.f.J g.f.b = some (.file i) ∨ V'.now.entry g.f.J g.f.tb = some (.file i)⌝ ∗
        DurFs.durFound (L := L') g.f V'.now v ∗ DurFs.durFoundTmp (L := L') g.f V'.now ∗
        crashRest Q (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) (Dl' ++ Dl) tt V' ∗
        (⌜imgHolds v ⟨A, S⟩⌝ ∨ (∃ op : DiskOp, winOf Wl Ws op ∗ ⌜imgHolds v (op.apply ⟨A, S⟩)⌝) ∨ Wf) := by
  iintro #Hinv #Hcr Htk Hlc #Hdi Hdc #Hsh HA HS Hrest
  iunfold diskInv at Hinv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc Hb with Hb
  iunfold diskBody at Hb
  icases Hb with ⟨%I, %stg, %w, %s, Hds, Hrec0, Hb⟩
  icases Hb with (⟨Hl, Hs, %Hok, Hwin⟩ | ⟨-, Htk'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Htk Htk'
  iunfold diskOwnL at HA
  iunfold diskOwnS at HS
  ihave %HAe := ghostVar_agree _ _ _ _ _ $$ HA Hl
  ihave %HSe := ghostVar_agree _ _ _ _ _ $$ HS Hs
  subst HAe HSe
  imod DurFs.durInv_crash Q hG.goose_localGS L' g.γd g.f g.R Dl tt V' s (⊤ \ ↑diskN) durN_sub_diff
    osShN_sub_diff hD $$ Hdi Hcr Hdc Hds Hsh Hrest
    with ⟨%v, %Dl', ⟨%hv, %hDl'⟩, Hds, Hf, Ht, Hrest⟩
  ihave Hres : iprop(⌜imgHolds v ⟨I.absL stg, I.absS⟩⌝ ∨
      (∃ op : DiskOp, winOf Wl Ws op ∗ ⌜imgHolds v (op.apply ⟨I.absL stg, I.absS⟩)⌝) ∨ Wf) $$ [Hwin]
  · cases w with
    | idle =>
      simp only [diskWinRes]
      icases Hwin with %Hidle
      ileft; ipureintro
      subst Hidle
      have hv' : v = some (encImg I) := by
        rcases hv with h | h; exact h; simp at h
      exact ⟨I, Hok, hv', rfl⟩
    | «open» op I' sy =>
      simp only [diskWinRes]
      icases Hwin with ⟨%Hf', Hw⟩
      obtain ⟨hok', hab, hcur, halt⟩ := Hf'
      rcases hv with hv | hv
      · iright; ileft
        iexists op; iframe Hw
        ipureintro
        refine ⟨I', hok', by rw [hv, hcur], ?_⟩
        rw [← crash_of I' stg, hab]; rfl
      · ileft; ipureintro
        have hv' : v = some (encImg I) := by
          rcases halt with h | ⟨-, h⟩
          · rw [h] at hv; cases hv
          · rw [h] at hv; cases hv; rfl
        exact ⟨I, Hok, hv', rfl⟩
    | fresh r =>
      simp only [diskWinRes]
      icases Hwin with ⟨HWf, -⟩
      iright; iright; iexact HWf
  imod Hclose $$ [Hds Hrec0 Htk] with -
  · inext; iunfold diskBody; iexists I, stg, w, s; iframe Hds Hrec0; iright; iframe #; iframe
  imodintro
  iexists v, Dl'
  iframe
  ipureintro; exact hDl'

end crash

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
