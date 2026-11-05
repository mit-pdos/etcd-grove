/-
**The API's instance of the store's slots** (stage 1, 2026-11-03/04; `notes/decisions.md`, "slots in
place"; `notes/mvcc-api-invariants.md` §1, §2, round 16). Lean-first (no Rocq counterpart).

The internals carry the API's slots in place (`InvStore`: `StoreNames.api`, `slotX`, `slotY`,
`slotF`, `slotFr`, `slotFl`; strict M1, 2026-11-04: the API's ghost state at `γ.api`, no trivial
case), here unfolded at `γ.api = a` (`Api/Ghost.lean`), and the writer's frozen
state (round 16's F2, for `mvccImage_snapshot.law`) is entered and left by the whole backend share
token's holder (`writerInv_freeze`, `writerInv_thaw`). Formerly `Api/InvStoreX.lean`, a parallel
copy of the invariants with explicit slot parameters (retired: the slots now live in today's
definitions).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section slots
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem slotX_some {γ : StoreNames} {a : api.AbsNames} (h : γ.api = a) (q : Qp) (L : Log)
    (c : Int) : slotX (GF := GF) γ q L c ⊣⊢ api.revMuAbs a q L c := by
  unfold slotX; simp only [h]; exact .rfl

theorem slotY_some {γ : StoreNames} {a : api.AbsNames} (h : γ.api = a) (L : Log) :
    slotY (GF := GF) γ L ⊣⊢ ∃ c : Int, api.absPart a (1 : Qp).half.half L c ∗
      api.pndPart a (pndW γ) none ∗ rcvW γ (1 : Qp).half c ∗ api.wcrPart a (1 : Qp).half c := by
  unfold slotY; simp only [h]; exact .rfl

theorem slotF_some {γ : StoreNames} {a : api.AbsNames} (h : γ.api = a) :
    slotF (GF := GF) γ ⊣⊢ api.shareTok a 1 := by
  unfold slotF; simp only [h]; exact .rfl

theorem slotFr_some {γ : StoreNames} {a : api.AbsNames} (h : γ.api = a) :
    slotFr (GF := GF) γ ⊣⊢ api.shareTok a 1 := by
  unfold slotFr; simp only [h]; exact .rfl

theorem slotFl_some {γ : StoreNames} {a : api.AbsNames} (h : γ.api = a) (q : Qp) (b : Bool) :
    slotFl (GF := GF) γ q b ⊣⊢ ghostVar a.frz q b := by
  unfold slotFl; simp only [h]; exact .rfl

/-- **The API's writer excludes the frozen state**: a share of the token and the frozen state's
deposit (the whole token) are too much (`writerInv_checkoutG`'s `G`). -/
theorem slotF_share_excl {γ : StoreNames} {a : api.AbsNames} (h : γ.api = a) (q : Qp) :
    slotF (GF := GF) γ ∗ api.shareTok a q ⊢ False := by
  iintro ⟨HF, HG⟩
  icases (slotF_some h).1 $$ HF with HF
  iapply api.shareTok_excl a q $$ [HF HG]
  iframe HF HG

/-- **What the frozen state's holder took out**: the writer's state with its registration, or (a
write transaction open) the writer's key with its part of the deposit ghost and the registration. -/
def writerTaken (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(writerL s γ ∗ writerReg s γ ∨ writerKey γ ∗ wDep γ ∗ storeRegd s γ)

end slots

section lc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **Freezing the writer** (round 16, F2): the holder of the whole backend share token deposits
it, raises the frozen flag (keeping half of it) and takes out what is there, the writer's state or
the open writer's key (`writerTaken`), at the current names; not while restoring (the restorer's
deposit is the whole token too), nor frozen already. -/
theorem writerInv_freeze (s : Loc) (γ : StoreNames) (a : api.AbsNames) (h : γ.api = a)
    (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ writerInv (GF := GF) s γ -∗ api.shareTok a 1 -∗ curAt γ dq o ={⊤}=∗
      writerTaken s γ ∗ ghostVar a.frz (1 : Qp).half true ∗ curAt γ dq o := by
  iintro Hlc #Hi HF Hpin
  iunfold writerInv at Hi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBody (GF := GF) s γ)
    (by exact CoPset.subseteq_top) $$ Hi with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := writerInvBody (GF := GF) s γ)) $$ Hlc HP with HP
  iunfold writerInvBody at HP
  icases HP with (⟨%p, %o', Hc, HP⟩ | ⟨-, -, HFr, -⟩)
  rotate_left 1
  · iexfalso
    icases (slotFr_some h).1 $$ HFr with HFr
    iapply api.shareTok_excl a 1 $$ [HFr HF]
    iframe HFr HF
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨Hfz, HT⟩ | ⟨-, HF'⟩)
  · icases (slotFl_some h 1 false).1 $$ Hfz with Hfz
    imod ghostVar_update true a.frz false $$ Hfz with Hfz
    icases (ghostVar_split_half (GF := GF) a.frz 1 true).1 $$ Hfz with ⟨Hfz1, Hfz2⟩
    imod Hclose $$ [Hc HF Hfz1] with -
    · inext; iunfold writerInvBody; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
      iframe Hc; iright
      isplitl [Hfz1]
      · iapply (slotFl_some h _ true).2; iexact Hfz1
      iapply (slotF_some h).2; iexact HF
    imodintro; iframe Hpin Hfz2; iunfold writerTaken; iexact HT
  · iexfalso
    icases (slotF_some h).1 $$ HF' with HF'
    iapply api.shareTok_excl a 1 $$ [HF' HF]
    iframe HF' HF

/-- **Thawing the writer**: the frozen state's holder (its half of the flag up) puts back what it
took, lowers the flag and gets the whole share token back. -/
theorem writerInv_thaw (s : Loc) (γ : StoreNames) (a : api.AbsNames) (h : γ.api = a)
    (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ writerInv (GF := GF) s γ -∗ writerTaken s γ -∗ ghostVar a.frz (1 : Qp).half true -∗
      curAt γ dq o ={⊤}=∗ api.shareTok a 1 ∗ curAt γ dq o := by
  iintro Hlc #Hi HT Hfz Hpin
  iunfold writerInv at Hi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBody (GF := GF) s γ)
    (by exact CoPset.subseteq_top) $$ Hi with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := writerInvBody (GF := GF) s γ)) $$ Hlc HP with HP
  iunfold writerInvBody at HP
  icases HP with (⟨%p, %o', Hc, HP⟩ | ⟨-, -, -, Hfz'⟩)
  rotate_left 1
  · icases (slotFl_some h 1 false).1 $$ Hfz' with Hfz'
    ihave %Hv := ghostVar_valid_2 a.frz false 1 true (1 : Qp).half $$ Hfz' Hfz
    exact absurd Hv.1 (Qp_one_add_not_le _)
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨Hfz', -⟩ | ⟨Hfz', HF⟩)
  · icases (slotFl_some h 1 false).1 $$ Hfz' with Hfz'
    ihave %Hv := ghostVar_valid_2 a.frz false 1 true (1 : Qp).half $$ Hfz' Hfz
    exact absurd Hv.1 (Qp_one_add_not_le _)
  icases (slotFl_some h _ true).1 $$ Hfz' with Hfz'
  icases (slotF_some h).1 $$ HF with HF
  icases ghostVar_join_halves a.frz true true $$ [Hfz' Hfz] with ⟨Hfz, -⟩
  · iframe Hfz' Hfz
  imod ghostVar_update false a.frz true $$ Hfz with Hfz
  imod Hclose $$ [Hc HT Hfz] with -
  · inext; iunfold writerInvBody; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
    iframe Hc; ileft
    isplitl [Hfz]
    · iapply (slotFl_some h 1 false).2; iexact Hfz
    iunfold writerTaken at HT; iexact HT
  imodintro; iframe HF Hpin

end lc

end mvcc
end EtcdGrove
end Perennial
