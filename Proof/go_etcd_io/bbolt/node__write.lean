/-
The proof of `Spec/go_etcd_io/bbolt/node__write.lean` (U9a, `notes/bbolt-proof-plan.md`; ported from
`old/bbolt/Proof/go_etcd_io/bbolt/node__write.lean`), over `internal/common`'s accessor specs and
`WriteInodeToPage`'s (U1).
-/
module

public import Spec.go_etcd_io.bbolt.node__write
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.Page__Flags
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetCount
public import Spec.go_etcd_io.bbolt.internal.common.WriteInodeToPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
theorem node.write.wp_proof (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hCount : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hFlags : internal.common.Page.Flags.spec (GF := GF) (hG := hG))
    (hSetFlags : internal.common.Page.SetFlags.spec (GF := GF) (hG := hG))
    (hSetCount : internal.common.Page.SetCount.spec (GF := GF) (hG := hG))
    (hW : internal.common.WriteInodeToPage.spec (GF := GF) (hG := hG)) :
    node.write.spec (GF := GF) (hG := hG) := by
  intro nl nv ins ms dqn dqi qk qv p hdr R Hc0 Hf0 Hlen Hfit Hbody Hpg Hpos Hmax
  wp_start as ⟨Hn, Hs, Hd, Hp, Hrest⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hml := BigSepL2.bigSepL2_length $$ Hd
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  wp_apply hCount $$ [$Hp] as Hp
  try wp_auto
  rw [Hc0]
  try wp_auto
  wp_apply hFlags $$ [$Hp] as Hp
  try wp_auto
  rw [Hf0]
  try wp_auto
  wp_apply hA
  try wp_auto
  try unfold internal.common.LeafPageFlag
  try unfold internal.common.BranchPageFlag
  wp_join iprop(p_ptr ↦ p ∗
      p ↦ ({ hdr with flags' := (if nv.isLeaf' then W16 2 else W16 1) } : internal.common.Page))
    at next with [Hp p] as ⟨p, Hp⟩
  · cases hl : nv.isLeaf' <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> wp_auto <;>
      wp_apply hSetFlags $$ [$Hp] as Hp <;> wp_join_done
  wp_if_destruct
  · exfalso; word
  wp_apply hSetCount $$ [$Hp] as Hp
  try wp_auto
  wp_apply hCount $$ [$Hp] as Hp
  try wp_auto
  rw [show sint.Z nv.inodes'.len = (ms.length : Int) by word]
  try simp only
  have Hhdr : ({ { hdr with flags' := (if nv.isLeaf' = true then W16 2 else W16 1) } with
      count' := W16 (ms.length : Int) } : internal.common.Page) =
      hdrWritten hdr nv.isLeaf' ms.length := by
    cases nv.isLeaf' <;> rfl
  ihave Hp : (p ↦ hdrWritten hdr nv.isLeaf' ms.length : IProp GF) $$ [Hp]
  · rw [← Hhdr]; iexact Hp
  wp_if_destruct
  · have H0 : ms.length = 0 := by
      have h := congrArg BitVec.toNat Hif
      simp only [BitVec.toNat_ofInt] at h
      word
    have Hms : ms = [] := List.eq_nil_of_length_eq_zero H0
    have Hins : ins = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst Hms Hins
    ihave Hn : (nl ↦{dqn} nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iapply HΦ
    simp [pageBody, elemBytes, leafElems, branchElems, dataBytes]
    iframe
  · wp_apply hW nv.inodes' ins ms dqi qk qv p (hdrWritten hdr nv.isLeaf' ms.length)
      (List.replicate R (W8 0)) Hpos Hfit (by simpa using Hbody)
      (by
        intro hne m hm
        apply Hpg _ m hm
        cases h : nv.isLeaf'
        · rfl
        · rw [h] at hne; exact absurd rfl hne) $$ [Hs Hd Hp Hrest] as ⟨Hs, Hd, Hp, Hrest⟩
    · iframe
    try wp_auto
    have Hdec' : decide (W16 ((if nv.isLeaf' = true then leafPageFlag else branchPageFlag : Nat) : Int)
        = W16 2) = nv.isLeaf' := by
      cases nv.isLeaf' <;> simp [leafPageFlag, branchPageFlag]
    rw [Hdec']
    ihave Hn : (nl ↦{dqn} nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iapply HΦ
    rw [List.drop_replicate, pageBody_length, pageBody_length]
    iframe

end proof

end bbolt
end EtcdGrove
end Perennial
