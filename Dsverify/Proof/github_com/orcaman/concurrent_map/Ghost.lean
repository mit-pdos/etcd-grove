/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/Ghost.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The concurrent map's laws (for clients) and ghost steps (for the library's proofs).

Laws: `cmapShards_agree`, `isCMapV_shards`, `readerV_isCMapV`, `cmapOld_alloc`, `isCMap_intro`,
`reader_intro`, `isCMapV_to_old` (a strong map as an old one), `cmapOld_au` (the old specs'
atomic update, from `cmapOld`).

Steps: `cmap_observe` (a reader's atomic observation), `cmap_update` (a writer's atomic update),
both through the invariant `cmapInv`.
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

set_option linter.unusedSectionVars false

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section laws
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]

theorem cmapOldN_cmapN : (↑cmapOldN : CoPset) ⊆ ⊤ \ ↑cmapN :=
  sync.mask_ndot_ne nroot "cmapOld" "cmap" (by decide)

theorem cmapShards_agree (n n' : Nat) :
    cmapShards (GF := GF) n ∗ cmapShards n' ⊢ ⌜n = n'⌝ := by
  iintro ⟨H1, H2⟩
  iunfold cmapShards at H1 H2
  icases H1 with ⟨%w, Hw, %Hw⟩
  icases H2 with ⟨%w', Hw', %Hw'⟩
  icombine Hw Hw' gives %Heq
  ipureintro
  have : w = w' := by simpa using Heq
  subst this; omega

theorem cmapCore_shards (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF)
    (n : w64) (shs : List (Loc × GName)) :
    cmapCore m γ R n shs ⊢ cmapShards (sint.nat n) := by
  iintro #H
  iunfold cmapCore at H
  icases H with ⟨#Hn, -, %Hl, -⟩
  iunfold cmapShards
  iexists n
  iframe Hn
  ipureintro; exact ⟨rfl, by have := Hl.1; word⟩

/-- A map has some number of shards. -/
theorem isCMapV_shards (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) :
    isCMapV m γ R ⊢ ∃ n, cmapShards n := by
  iintro H
  iunfold isCMapV at H
  icases H with ⟨%n, %shs, H⟩
  iexists (sint.nat n)
  iapply cmapCore_shards $$ H

/-- A reader bundle includes the map. -/
theorem readerV_isCMapV (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) :
    readerV m γ R ⊢ isCMapV m γ R := by
  iintro H
  iunfold readerV at H
  icases H with ⟨%n, %shs, H, -⟩
  iunfold isCMapV
  iexists n, shs
  iexact H

/-- Giving the view up to an invariant (for the old specs). -/
theorem cmapOld_alloc (E : CoPset) (γ : GName) (M : GMap GoString GoInterface) :
    cmapView (GF := GF) γ M ⊢ |={E}=> cmapOld γ := by
  iintro Hv
  iunfold cmapOld
  iapply inv_alloc
  inext
  iexists M
  iexact Hv

theorem isCMap_intro (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) :
    isCMapV m γ R ∗ cmapOld γ ⊢ isCMap m R := by
  iintro ⟨H, Ho⟩
  iunfold isCMap
  iexists γ
  iframe

theorem reader_intro (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF) :
    readerV m γ R ∗ cmapOld γ ⊢ reader m R := by
  iintro ⟨H, Ho⟩
  iunfold reader
  iexists γ
  iframe

/-- A strong map, with its view given up, as an old one. -/
theorem isCMapV_to_old (E : CoPset) (m : GoSlice) (γ : GName)
    (R : GoString → GoInterface → IProp GF) (M : GMap GoString GoInterface) :
    isCMapV m γ R ∗ cmapView γ M ⊢ |={E}=> isCMap m R := by
  iintro ⟨#H, Hv⟩
  imod cmapOld_alloc E γ M $$ Hv with #Ho
  imodintro
  iapply isCMap_intro
  iframe H Ho

/-- The old specs' atomic update: the view from `cmapOld`, changed by `f`. -/
theorem cmapOld_au (γ : GName) (f : GMap GoString GoInterface → GMap GoString GoInterface)
    (Q : IProp GF) :
    cmapOld γ ∗ Q ⊢
      |={⊤ \ ↑cmapN, ∅}=> ∃ M, cmapView γ M ∗ (cmapView γ (f M) ={∅, ⊤ \ ↑cmapN}=∗ Q) := by
  iintro ⟨#Hold, HQ⟩
  iunfold cmapOld at Hold
  iinv Hold with ⟨%M, >Hv⟩ Hclose <;> try exact cmapOldN_cmapN
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists M
  iframe Hv
  iintro Hv
  imod Hmask with _
  imod Hclose $$ [Hv] with _
  · inext; iexists (f M); iexact Hv
  imodintro
  iexact HQ

/-- The view is exclusive. -/
theorem cmapView_exclusive (m : GoSlice) (γ : GName) (R : GoString → GoInterface → IProp GF)
    (M1 M2 : GMap GoString GoInterface) :
    isCMapV m γ R ∗ cmapView γ M1 ∗ cmapView γ M2 ⊢ |={⊤}=> False := by
  iintro ⟨#Hm, H1, H2⟩
  iunfold isCMapV at Hm
  icases Hm with ⟨%n, %shs, Hm⟩
  iunfold cmapCore at Hm
  icases Hm with ⟨-, -, -, #Hinv, -⟩
  iinv Hinv with Hi Hclose
  iunfold cmapInv at Hi
  icases Hi with ⟨%M0, >Hv, -⟩
  iunfold cmapView at H1 H2
  icases H1 with ⟨%c1, H1⟩
  icases H2 with ⟨%c2, H2⟩
  icombine H1 H2 gives % ⟨_, Heq⟩
  rw [Heq]
  icombine H1 H2 as H
  icombine H Hv gives % ⟨Hq, _⟩
  exfalso
  simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hq
  have : (0 : Rat) < (Qp.half 1).val := (Qp.half 1).2
  grind

/-- An atomic update from a view the client owns outright (no concurrent writer). -/
theorem cmapView_au (γ : GName) (M : GMap GoString GoInterface)
    (f : GMap GoString GoInterface → GMap GoString GoInterface)
    (Q : GMap GoString GoInterface → IProp GF) :
    cmapView γ M ∗ (cmapView γ (f M) -∗ Q M) ⊢
      |={⊤ \ ↑cmapN, ∅}=> ∃ M', cmapView γ M' ∗ (cmapView γ (f M') ={∅, ⊤ \ ↑cmapN}=∗ Q M') := by
  iintro ⟨Hv, HQ⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists M
  iframe Hv
  iintro Hv
  imod Hmask with _
  imodintro
  iapply HQ $$ Hv

/-- `cmapOld_au`, with a result that depends on the view. -/
theorem cmapOld_au_dep (γ : GName) (f : GMap GoString GoInterface → GMap GoString GoInterface)
    (Q : GMap GoString GoInterface → IProp GF) :
    cmapOld γ ∗ (∀ M, Q M) ⊢
      |={⊤ \ ↑cmapN, ∅}=> ∃ M, cmapView γ M ∗ (cmapView γ (f M) ={∅, ⊤ \ ↑cmapN}=∗ Q M) := by
  iintro ⟨#Hold, HQ⟩
  iunfold cmapOld at Hold
  iinv Hold with ⟨%M, >Hv⟩ Hclose <;> try exact cmapOldN_cmapN
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists M
  iframe Hv
  iintro Hv
  imod Hmask with _
  imod Hclose $$ [Hv] with _
  · inext; iexists (f M); iexact Hv
  imodintro
  iapply HQ

/-- `cmapOld_au` for an update whose commit also gives a pure fact `P M`. -/
theorem cmapOld_au_pure (γ : GName) (f : GMap GoString GoInterface → GMap GoString GoInterface)
    (P : GMap GoString GoInterface → Prop) (Q : IProp GF) :
    cmapOld γ ∗ Q ⊢
      |={⊤ \ ↑cmapN, ∅}=> ∃ M, cmapView γ M ∗
        (⌜P M⌝ -∗ cmapView γ (f M) -∗ |={∅, ⊤ \ ↑cmapN}=> Q) := by
  iintro H
  imod cmapOld_au γ f Q $$ H with ⟨%M, Hv, Hc⟩
  imodintro
  iexists M
  iframe Hv
  iintro _ Hv
  iapply Hc $$ Hv

end laws

section steps
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]

/-- A reader's atomic observation: holding shard `i`'s ghost fraction at `Mi` (its read lock),
the client's view `M` is seen, and `Mi` is `M`'s part in shard `i`. -/
theorem cmap_observe (γ : GName) (n : Nat) (shs : List (Loc × GName)) (i : Nat) (p : Loc × GName)
    (hp : shs[i]? = some p) (q : Qp) (Mi : GMap GoString GoInterface)
    (Q : GMap GoString GoInterface → IProp GF) :
    inv cmapN (cmapInv γ n shs) ∗ ghostVar p.2 q Mi ∗
      (|={⊤ \ ↑cmapN, ∅}=> ∃ M, cmapView γ M ∗ (cmapView γ M ={∅, ⊤ \ ↑cmapN}=∗ Q M)) ⊢
      |={⊤}=> ghostVar p.2 q Mi ∗ ∃ M, ⌜Mi = shardPart n i M⌝ ∗ Q M := by
  iintro ⟨#Hinv, Hg, Hau⟩
  iinv Hinv with Hi0 Hclose
  iunfold cmapInv at Hi0
  icases Hi0 with ⟨%M0, >Hv, >Hs⟩
  imod Hau with ⟨%M, Hview, Hcont⟩
  iunfold cmapView at Hview
  icases Hview with ⟨%c, Hview⟩
  icombine Hview Hv gives % ⟨_, Heq⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
  icases (BigSepL.bigSepL_lookup_acc hp).1 $$ Hs with ⟨Hi, Hback⟩
  icombine Hg Hi gives % ⟨_, HeqI⟩
  ihave Hs := Hback $$ %p Hi
  rw [list_set_lookup_self _ _ _ hp]
  imod Hcont $$ [Hview] with HQ
  · iunfold cmapView; iexists _; iexact Hview
  imod Hclose $$ [Hv Hs] with _
  · inext; iunfold cmapInv; iexists M; iframe Hv Hs
  imodintro
  iframe Hg
  iexists M
  iframe HQ
  ipureintro; exact HeqI

/-- A writer's atomic update: holding all of shard `i`'s ghost variable at `Mi` (half from its
write lock, half from the invariant), the client's view `M` becomes `f M` and the shard's part
`fi Mi`; `f` changes only shard `i`'s part. -/
theorem cmap_update (γ : GName) (n : Nat) (shs : List (Loc × GName)) (i : Nat) (p : Loc × GName)
    (hp : shs[i]? = some p) (Mi : GMap GoString GoInterface)
    (f fi : GMap GoString GoInterface → GMap GoString GoInterface)
    (hfi : ∀ M, shardPart n i (f M) = fi (shardPart n i M))
    (hfj : ∀ j M, j ≠ i → shardPart n j (f M) = shardPart n j M)
    (Q : GMap GoString GoInterface → IProp GF) :
    inv cmapN (cmapInv γ n shs) ∗ ghostVar p.2 (1 : Qp).half Mi ∗
      (|={⊤ \ ↑cmapN, ∅}=> ∃ M, cmapView γ M ∗
        (⌜Mi = shardPart n i M⌝ -∗ cmapView γ (f M) ={∅, ⊤ \ ↑cmapN}=∗ Q M)) ⊢
      |={⊤}=> ghostVar p.2 (1 : Qp).half (fi Mi) ∗ ∃ M, Q M := by
  iintro ⟨#Hinv, Hg, Hau⟩
  iinv Hinv with Hi0 Hclose
  iunfold cmapInv at Hi0
  icases Hi0 with ⟨%M0, >Hv, >Hs⟩
  imod Hau with ⟨%M, Hview, Hcont⟩
  iunfold cmapView at Hview
  icases Hview with ⟨%c, Hview⟩
  icombine Hview Hv gives % ⟨_, Heq⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
  icases BigSepL.bigSepL_lookup_acc_impl hp $$ Hs with ⟨Hi, Hback⟩
  icombine Hg Hi gives % ⟨_, HeqI⟩
  imod ghostVar_update_halves (f M, (n, shs)) γ (M, (n, shs)) (M, (n, shs)) $$ Hview Hv
    with ⟨Hview, Hv⟩
  imod ghostVar_update_halves (fi Mi) p.2 Mi _ $$ Hg Hi with ⟨Hg, Hi⟩
  imod Hcont $$ %HeqI [Hview] with HQ
  · iunfold cmapView; iexists _; iexact Hview
  ihave Hs := Hback $$ %(fun j y => iprop(ghostVar y.2 (1 : Qp).half (shardPart n j (f M)))) [] [Hi]
  · imodintro
    iintro %k %y %_ %hne H
    simp only []
    rw [hfj k M hne]
    iexact H
  · simp only []
    rw [hfi, ← HeqI]
    iexact Hi
  imod Hclose $$ [Hv Hs] with _
  · inext; iunfold cmapInv; iexists (f M); iframe Hv Hs
  imodintro
  iframe Hg
  iexists M
  iexact HQ

end steps

end Perennial.github_com.orcaman.concurrent_map
