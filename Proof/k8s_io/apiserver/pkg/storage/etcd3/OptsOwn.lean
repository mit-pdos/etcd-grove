/-
Lean-first (no Rocq counterpart).

# An options slice being appended to (`syncPaginated`, `startWatching`)

The `[]clientv3.OpOption` slices the etcd3 watcher builds with `append`: their elements read-only, the
capacity owned (`optsOwn`), so that each `append` (`wp_slice_append_dfrac`) keeps them and the client
reads them (`optsAt`). Moved from `watchChan__syncPaginated.lean` (7f-5a-P step 5).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]

/-- **An options slice being appended to**: its elements read-only, `optSpec` of `gs`, its
capacity owned. -/
def optsOwn (sl : GoSlice) (gs : List (OpFull → OpFull)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ ownSliceCap GoFunc sl (DFrac.own 1) ∗
    ⌜fs.length = gs.length⌝ ∗
    □ ∀ (i : Nat) (f : GoFunc) (g : OpFull → OpFull), ⌜fs[i]? = some f⌝ -∗ ⌜gs[i]? = some g⌝ -∗
      optSpec f g)

theorem optsOwn_optsAt (sl : GoSlice) (gs : List (OpFull → OpFull)) :
    optsOwn (GF := GF) sl gs ⊢ optsAt sl gs ∗ optsOwn sl gs := by
  unfold optsOwn optsAt
  iintro ⟨%fs, #Hs, Hc, %Hl, #Hf⟩
  isplitr
  · iexists fs
    iframe Hs Hf
    ipureintro; exact Hl
  iexists fs
  iframe Hs Hc Hf
  ipureintro; exact Hl

/-- `append(opts, f)`, `f` with `optSpec f g`, in a fresh one-element slice. -/
theorem wp_optsOwn_append (sl sl2 : GoSlice) (gs : List (OpFull → OpFull)) (f : GoFunc)
    (g : OpFull → OpFull) :
    {{ optsOwn (GF := GF) sl gs ∗ optSpec f g ∗ sl2 ↦* [f] }}
      (App (App (Val #(functions go.append
        [go.GoType.SliceType go_etcd_io.etcd.client.v3.OpOption.ty])) (Val #sl)) (Val #sl2))
    {{ (s' : GoSlice), RET #s'; optsOwn s' (gs ++ [g]) }} := by
  iintro %Φ ⟨Ho, #Hf, Hsl2⟩ HΦ
  iunfold optsOwn at Ho
  icases Ho with ⟨%fs, #Hs, Hcap, %Hl, #Hfs⟩
  wp_apply (wp_slice_append_dfrac (st := go.GoType.SliceType go_etcd_io.etcd.client.v3.OpOption.ty)
    (t := go_etcd_io.etcd.client.v3.OpOption.ty) sl fs DFrac.discard sl2 [f] (DFrac.own 1))
    $$ [Hcap Hsl2] as %s' ⟨#Hs', Hcap', -⟩
  · iframe Hs Hcap Hsl2
    ipureintro; exact DFrac.valid_discard
  iapply HΦ
  iunfold optsOwn
  iexists fs ++ [f]
  iframe Hs' Hcap'
  isplitr
  · ipureintro; simp [Hl]
  iintro !> %i %f' %g' %Hf' %Hg'
  by_cases hi : i < fs.length
  · rw [List.getElem?_append_left hi] at Hf'
    rw [List.getElem?_append_left (by omega)] at Hg'
    iapply Hfs $$ %i %f' %g' %Hf' %Hg'
  · rw [List.getElem?_append_right (by omega)] at Hf'
    rw [List.getElem?_append_right (by omega)] at Hg'
    have hgl : i - gs.length = i - fs.length := by omega
    rw [hgl] at Hg'
    rcases hk : i - fs.length with _ | k <;> rw [hk] at Hf' Hg'
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg'
      subst Hf' Hg'
      iexact Hf
    · simp at Hf'

end opts

end k8s
end EtcdGrove
end Perennial
