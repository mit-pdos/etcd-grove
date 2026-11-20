/-
**The commit point's registrations** (backend-snapshot B2, 2026-11-20; `notes/backend-snapshot-plan.md`):
how a commit arms every snapshot registered in the commit invariant (`cmtRegs`, `InvBackend.lean`).
At its commit point a commit holds the batch lock's inputs at the writer's contents `S`, which become
the committed data there (`obsIn`); each registration's wand, applied to them and its `R` (both under
the invariant's later), gives the observation of `S`, the inputs kept (the conclusion is pure); the
commit counter goes up by one, so that a registration made before it is armed.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.TrackedLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **One registration armed at `S`**: from the inputs at `S`, the entry (under the invariant's
later) at the next count and the new committed data `S`, the inputs kept. -/
theorem entry_arm (γ : BNames) (P : BParams) (W Pk : IProp GF) (c : Nat) (Dc S : Data)
    (e : GName × GName × Nat) (F : IProp GF) (hF : F ⊢ obsIn γ P W Pk S) :
    F ∗ ▷ regEntry γ P W Pk c Dc e ⊢ ◇ (F ∗ ▷ regEntry γ P W Pk (c + 1) S e) := by
  iintro ⟨Hi, He⟩
  iunfold regEntry at He
  icases He with ⟨%R, %Q, Hr, Hp, HR, Hw, -⟩
  ihave Ha := obsWand_apply_later γ P W Pk R Q S F hF $$ [$Hi $HR $Hw]
  imod Ha with ⟨⟨Hi, HR, Hw⟩, %Hq⟩
  imodintro
  iframe Hi
  iunfold regEntry
  inext
  iexists R, Q
  iframe Hr Hp HR Hw
  ipureintro; exact fun _ => Hq

/-- **Every registration armed at `S`** (by induction on the map, the inputs passed along). -/
theorem entries_arm (γ : BNames) (P : BParams) (W Pk : IProp GF) (c : Nat) (Dc S : Data)
    (M : GMap Nat (GName × GName × Nat)) (F : IProp GF) (hF : F ⊢ obsIn γ P W Pk S) :
    F ∗ ▷ ([∗map] _i ↦ e ∈ M, regEntry γ P W Pk c Dc e) ⊢
      ◇ (F ∗ ▷ [∗map] _i ↦ e ∈ M, regEntry γ P W Pk (c + 1) S e) := by
  induction M using Std.LawfulFiniteMap.induction_on with
  | hemp =>
    rw [BigSepM.bigSepM_empty.to_eq, BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hi, -⟩
    imodintro
    iframe Hi
    inext; iempintro
  | hins i x M hi IH =>
    rw [(BigSepM.bigSepM_insert (Φ := fun (_ : Nat) e => regEntry (GF := GF) γ P W Pk c Dc e) hi).to_eq,
      (BigSepM.bigSepM_insert (Φ := fun (_ : Nat) e => regEntry (GF := GF) γ P W Pk (c + 1) S e) hi).to_eq]
    iintro ⟨Hi, Hs⟩
    icases Hs with ⟨He, Hs⟩
    imod entry_arm γ P W Pk c Dc S x F hF $$ [$Hi $He] with ⟨Hi, He⟩
    imod IH $$ [$Hi $Hs] with ⟨Hi, Hs⟩
    imodintro
    iframe Hi
    inext
    iframe He Hs

/-- **The registrations armed at `S`, the counter up by one** (what a commit point does, its new
committed data `S`): a lower bound `n` of the counter before is `n + 1` after. -/
theorem regs_arm (γ : BNames) (P : BParams) (W Pk : IProp GF) (Dc S : Data) (n : Nat)
    (F : IProp GF) (hF : F ⊢ obsIn γ P W Pk S) :
    F ∗ ▷ cmtRegs γ P W Pk Dc ∗ cntLb γ n ⊢
      |==> ◇ (F ∗ ▷ cmtRegs γ P W Pk S ∗ cntLb γ (n + 1)) := by
  iintro ⟨Hi, Hr, #Hlb⟩
  iunfold cmtRegs at Hr
  icases Hr with ⟨%gm, %gc, %c, %M, Hn, Hc, Hm, Hs⟩
  iapply except0_bupd
  iunfold cmtNames at Hn
  imod Hn with #Hn
  imod Hc with Hc
  imod Hm with Hm
  -- the lower bound before: `n ≤ c`
  ihave %Hle : ⌜n ≤ c⌝ $$ [Hc]
  · iunfold cntLb at Hlb
    icases Hlb with (%H0 | ⟨%gm', %gc', #Hn', #Hl⟩)
    · ipureintro; omega
    unfold cmtNames
    icombine Hn Hn' gives %Hag
    simp only [Prod.mk.injEq] at Hag
    obtain ⟨-, rfl, rfl⟩ := Hag
    ihave %Hv := monoNatLbOwn_valid gc 1 c n $$ Hc Hl
    ipureintro; exact Hv.2
  imod entries_arm γ P W Pk c Dc S M F hF $$ [$Hi $Hs] with ⟨Hi, Hs⟩
  imodintro
  imod mono_nat_own_update (c + 1) (by omega) $$ Hc with ⟨Hc, #Hl'⟩
  imodintro
  iframe Hi
  isplitl [Hc Hm Hs]
  · inext
    iunfold cmtRegs
    iexists gm, gc, c + 1, M
    iframe Hc Hm Hs
    unfold cmtNames; iexact Hn
  iunfold cntLb
  iright
  iexists gm, gc
  unfold cmtNames
  iframe Hn
  iapply monoNatLbOwn_le (n + 1) (by omega) $$ Hl'

/-- **The batch lock's inputs from its own pieces**, out of an `Unlock`'s window (the deleted
entries agreeing with the lock's logical view `Lb`): the client resources, the view quarter (thin of
`Lb` through the physical view, `thinV_trans`; the deleted entries exactly, `dlVd_of_dlsOk`), the
hook's keys and tracked buckets (`trkSide`), the compaction keys' values and deleted entries
(`fkHalf`). A frame for the commit point (`regs_arm`), kept whole. -/
theorem obsIn_of_lock (γ : BNames) (P : BParams) (W Pk : IProp GF) (st : BSess) (Lb : VData)
    (hd : dlsOk P st Lb) :
    iprop(W ∗ Pk ∗ viewQ γ (1 : Qp).half.half (vData P (st.C, st.R)) Lb ∗
      thinV γ (sData P st.S) (vData P (st.C, st.R)) ∗ trkSide γ P st ∗ fkHalf γ P st) ⊢
    obsIn (GF := GF) γ P W Pk st.S := by
  unfold obsIn viewAtD trkSide trkHalf fkHalf hkOwn
  iintro ⟨HW, HPk, Hv, #Hpre, ⟨⟨Hhk, Hrb⟩, -⟩, ⟨-, Hfkd, Hdls⟩⟩
  iunfold viewQ at Hv
  icases Hv with ⟨Hv, #Hth⟩
  iframe HW HPk Hhk Hfkd
  isplitl [Hv Hdls]
  · iexists (dlR P st.dl)
    iframe Hdls
    iexists Lb
    unfold viewQ
    iframe Hv
    isplitr
    · iapply thinV_trans γ (sData P st.S) (vData P (st.C, st.R)) Lb $$ [$Hpre $Hth]
    ipureintro; exact dlVd_of_dlsOk hd
  iapply rbSide_rbOwn γ P _ _ $$ Hrb

end lemmas

end backend
end EtcdGrove
end Perennial
