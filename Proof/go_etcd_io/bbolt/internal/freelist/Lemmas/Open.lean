/-
`flPgOwn` and `flRoOwn` (`Inv/Freelist.lean`) opened into an implementation (`FLImpl`) and
`shared`'s fields (`ownSh`), and closed back (U2, `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

/-- `I` is one of the two implementations. -/
def FLImpl.IsImpl [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    {GF : BundledGFunctors} [HeapGS hlc GF] [go.Semantics]
    [go_etcd_io.bbolt.internal.freelist.Assumptions] (I : FLImpl (GF := GF)) (a : Loc) : Prop :=
  I = arrayImpl a ∨ I = hashImpl a

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem array_ne_hash : (go.GoType.PointerType array'.ty) ≠ go.GoType.PointerType hashMap.ty := by
  unfold array'.ty hashMap.ty; simp

theorem mkOk_array_ne_hash (a b : Loc) :
    interface.mkOk (go.GoType.PointerType array'.ty) #a ≠
      interface.mkOk (go.GoType.PointerType hashMap.ty) #b := by
  intro h; simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h
  exact array_ne_hash h.1

theorem pds_to_pend (pp : GMap w64 Loc) (m : GMap w64 Pending) :
    ([∗map] _t ↦ p;pd ∈ pp;m, iprop(⌜p ≠ null⌝ ∗ ownPending (GF := GF) p pd)) ⊢
      [∗map] _t ↦ p;pd ∈ pp;m, ownPend p pd :=
  BigSepM2.bigSepM2_mono_of_forall _ _ _ _ (by
    intro _ p pd
    iintro H
    iunfold ownPend
    iexact H)

theorem pend_to_pds (pp : GMap w64 Loc) (m : GMap w64 Pending) :
    ([∗map] _t ↦ p;pd ∈ pp;m, ownPend (GF := GF) p pd) ⊢
      [∗map] _t ↦ p;pd ∈ pp;m, iprop(⌜p ≠ null⌝ ∗ ownPending p pd) :=
  BigSepM2.bigSepM2_mono_of_forall _ _ _ _ (by
    intro _ p pd
    iintro H
    iunfold ownPend at H
    iexact H)

/-- `flPgOwn`, opened. -/
theorem flPgOwn_open (fli : GoInterface) (fl : FLPg) :
    flPgOwn (GF := GF) fli fl ⊢ ∃ (I : FLImpl (GF := GF)) (a s : Loc),
      ⌜I.IsImpl a ∧ fli = I.iface⌝ ∗ I.hdl s ∗ I.own fl.free ∗ ownSh s fli fl := by
  iintro H
  iunfold flPgOwn at H
  icases H with ⟨%a, %s, %al, %ca, %pe, %c, %pp, Himpl, Hif, Hal, Hallocs, Hca, Hcache, Hpe,
    Hpending, Hpds, Hown, %Hok⟩
  ihave Hpds := pds_to_pend _ _ $$ Hpds
  iunfold flImplAt at Himpl
  iunfold flImplOwn at Hown
  icases Himpl with (⟨%Hfli, #Hsh⟩ | ⟨%Hfli, #Hsh⟩) <;>
    icases Hown with (⟨%Hfli', Hown⟩ | ⟨%Hfli', Hown⟩)
  · iexists arrayImpl a, a, s
    isplitr
    · ipureintro; exact ⟨Or.inl rfl, Hfli⟩
    dsimp only [arrayImpl, hashImpl]
    iframe Hsh
    isplitl [Hown]
    · iexact Hown
    iunfold ownSh
    iexists c
    iunfold ownShC
    iframe
    ipureintro
    exact ⟨Hok.1, Hok.2⟩
  · exact absurd (Hfli.symm.trans Hfli') (mkOk_array_ne_hash a a)
  · exact absurd (Hfli'.symm.trans Hfli) (mkOk_array_ne_hash a a)
  · iexists hashImpl a, a, s
    isplitr
    · ipureintro; exact ⟨Or.inr rfl, Hfli⟩
    dsimp only [arrayImpl, hashImpl]
    iframe Hsh
    isplitl [Hown]
    · iexact Hown
    iunfold ownSh
    iexists c
    iunfold ownShC
    iframe
    ipureintro
    exact ⟨Hok.1, Hok.2⟩

/-- `flPgOwn`, closed. -/
theorem flPgOwn_close (I : FLImpl (GF := GF)) (a s : Loc) (fli : GoInterface) (fl : FLPg)
    (hI : I.IsImpl a) (hfli : fli = I.iface) :
    I.hdl s ∗ I.own fl.free ∗ ownSh s fli fl ⊢ flPgOwn (GF := GF) fli fl := by
  iintro ⟨#Hsh, Hown, Hsh'⟩
  iunfold ownSh at Hsh'
  icases Hsh' with ⟨%c, Hsh', %Hok⟩
  iunfold ownShC at Hsh'
  icases Hsh' with ⟨%al, %ca, %pe, %pp, Hif, Hal, Hallocs, Hca, Hcache, Hpe, Hpending, Hpds⟩
  ihave Hpds := pend_to_pds _ _ $$ Hpds
  iunfold flPgOwn
  iexists a, s, al, ca, pe, c, pp
  iframe
  rcases hI with rfl | rfl <;> dsimp only [arrayImpl, hashImpl]
  · isplitl []
    · iunfold flImplAt; ileft; isplit
      · ipureintro; exact hfli
      · iexact Hsh
    isplitl [Hown]
    · iunfold flImplOwn; ileft; isplit
      · ipureintro; exact hfli
      · iexact Hown
    ipureintro; exact ⟨Hok.1, Hok.2⟩
  · isplitl []
    · iunfold flImplAt; iright; isplit
      · ipureintro; exact hfli
      · iexact Hsh
    isplitl [Hown]
    · iunfold flImplOwn; iright; isplit
      · ipureintro; exact hfli
      · iexact Hown
    ipureintro; exact ⟨Hok.1, Hok.2⟩

theorem flImplAt_array (a s : Loc) :
    structFieldRef array' go!"shared" a ↦□ s ⊢
      flImplAt (GF := GF) (arrayImpl (GF := GF) a).iface a s := by
  iintro #H
  iunfold flImplAt
  ileft
  isplit
  · ipureintro; rfl
  · iexact H

theorem flImplAt_hash (a s : Loc) :
    structFieldRef hashMap go!"shared" a ↦□ s ⊢
      flImplAt (GF := GF) (hashImpl (GF := GF) a).iface a s := by
  iintro #H
  iunfold flImplAt
  iright
  isplit
  · ipureintro; rfl
  · iexact H

end preds

end bbolt
end EtcdGrove
end Perennial
