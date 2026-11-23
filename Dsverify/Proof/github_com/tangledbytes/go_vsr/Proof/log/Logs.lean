/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/log/Logs.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
The proofs of `pkg/log`'s `Logs` methods (not the JSON ones).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.log

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : log.Assumptions]

/-- A slice points-to of a non-nil slice has a non-null pointer. -/
theorem log.ownSlice_ptr (sl : GoSlice) (dq : DFrac) (ls : List log.Log) (h : sl ≠ slice.nil) :
    (sl ↦*{dq} ls : IProp GF) ⊢ ⌜sl.ptr ≠ null⌝ := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · exact absurd H.1 h
  · iapply typedPointsto_not_null _ _ _ $$ H

/-- A non-empty slice is not nil. -/
theorem log.ownSlice_nonnil (sl : GoSlice) (dq : DFrac) (ls : List log.Log) (h : ls ≠ []) :
    (sl ↦*{dq} ls : IProp GF) ⊢ ⌜sl ≠ slice.nil⌝ := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · exact absurd H.2 h
  · icases typedPointsto_not_null _ _ _ $$ H with %Hn
    ipureintro; intro he; apply Hn; rw [he]; rfl

/-- `make(Logs, 0)`: an empty slice with a non-null pointer. -/
theorem log.wp_make_empty :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make2 [log.Logs.ty])) (Val #(W64 0)))
    {{ (sl : GoSlice), RET #sl; sl ↦* ([] : List log.Log) ∗ ownSliceCap log.Log sl (DFrac.own 1) ∗
        ⌜sl ≠ slice.nil⌝ }} := by
  wp_start
  wp_func_call
  wp_call
  wp_apply wp_GoPrealloc as %p %hnn
  iapply HΦ
  isplitl []
  · iapply ownSlice_empty _ _ (by rfl) (by word)
    iapply array_empty _ _ hnn
  isplitl []
  · iapply ownSliceCap_empty _ rfl (by word)
  · ipureintro
    intro h
    apply hnn
    exact congrArg GoSlice.ptr h

theorem log.elem_of (ls : List log.Log) (es : List VsrModel.Entry) (k : Nat) (e : VsrModel.Entry)
    (h : ls.map log.entryOf = es) (he : es[k]? = some e) :
    ∃ l, ls[k]? = some l ∧ log.entryOf l = e := by
  subst h
  rw [List.getElem?_map] at he
  cases hl : ls[k]? with
  | none => rw [hl] at he; cases he
  | some l => rw [hl] at he; exact ⟨l, rfl, Option.some.inj he⟩

theorem log.NewLogs.wp_proof : log.NewLogs.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply log.wp_make_empty as %sl ⟨Hsl, Hcap, %Hnn⟩
  iapply HΦ
  unfold log.ownLogs
  iframe
  ipureintro; exact ⟨rfl, Hnn⟩

theorem log.Logs.Len.wp_proof : log.Logs.Len.spec (GF := GF) (hG := hG) := fun sl dq es => by
  wp_start as Hl
  wp_auto
  unfold log.ownLogs
  icases Hl with ⟨%ls, Hsl, %Hmap, %Hnn⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  rw [show sl.len = W64 (es.length : Int) by rw [← Hmap, List.length_map]; word]
  iapply HΦ
  iexists ls
  iframe
  ipureintro; exact ⟨Hmap, Hnn⟩

theorem log.Logs.OpAt.wp_proof : log.Logs.OpAt.spec (GF := GF) (hG := hG) := fun sl dq es i e hi he => by
  wp_start as Hl
  unfold log.ownLogs
  icases Hl with ⟨%ls, Hsl, %Hmap, %Hnn⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  obtain ⟨l, hl, hle⟩ := log.elem_of ls es (sint.nat i - 1) e Hmap he
  have hk : (sint.nat i - 1) < ls.length := (List.getElem?_eq_some_iff.1 hl).1
  wp_auto
  rw [if_pos ⟨by word, by word⟩]
  have hk' : (sint.Z (i - W64 1)).toNat = sint.nat i - 1 := by word
  icases ownSlice_elem_acc (sint.Z (i - W64 1)) l sl dq ls (by word) (by rw [hk']; exact hl) $$ Hsl
    with ⟨Hel, Hclose⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hel with ⟨Hel, %Hnn'⟩
  wp_pures
  iStructNamed Hel
  wp_auto
  ihave Hel := typedPointsto_combine _ l dq Hnn' $$ [Data ClientID RequestID]
  · simp only [TypedPointsto.typedPointstoDef, named]; iframe
  ihave Hsl := Hclose $$ Hel
  have hset : ls.set (sint.nat i - 1) l = ls :=
    List.ext_getElem? (fun n => by rw [List.getElem?_set]; split <;> simp_all)
  rw [hk', hset]
  subst hle
  first
    | (rw [show (log.entryOf l).op = l.Data' from rfl])
    | (rw [show W64 ((log.entryOf l).cid : Int) = l.ClientID' by simp only [log.entryOf]; word])
    | (rw [show W64 ((log.entryOf l).req : Int) = l.RequestID' by simp only [log.entryOf]; word])
  iapply HΦ
  iexists ls
  iframe
  ipureintro; exact ⟨Hmap, Hnn⟩

theorem log.Logs.ClientIDAt.wp_proof : log.Logs.ClientIDAt.spec (GF := GF) (hG := hG) := fun sl dq es i e hi he => by
  wp_start as Hl
  unfold log.ownLogs
  icases Hl with ⟨%ls, Hsl, %Hmap, %Hnn⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  obtain ⟨l, hl, hle⟩ := log.elem_of ls es (sint.nat i - 1) e Hmap he
  have hk : (sint.nat i - 1) < ls.length := (List.getElem?_eq_some_iff.1 hl).1
  wp_auto
  rw [if_pos ⟨by word, by word⟩]
  have hk' : (sint.Z (i - W64 1)).toNat = sint.nat i - 1 := by word
  icases ownSlice_elem_acc (sint.Z (i - W64 1)) l sl dq ls (by word) (by rw [hk']; exact hl) $$ Hsl
    with ⟨Hel, Hclose⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hel with ⟨Hel, %Hnn'⟩
  wp_pures
  iStructNamed Hel
  wp_auto
  ihave Hel := typedPointsto_combine _ l dq Hnn' $$ [Data ClientID RequestID]
  · simp only [TypedPointsto.typedPointstoDef, named]; iframe
  ihave Hsl := Hclose $$ Hel
  have hset : ls.set (sint.nat i - 1) l = ls :=
    List.ext_getElem? (fun n => by rw [List.getElem?_set]; split <;> simp_all)
  rw [hk', hset]
  subst hle
  first
    | (rw [show (log.entryOf l).op = l.Data' from rfl])
    | (rw [show W64 ((log.entryOf l).cid : Int) = l.ClientID' by simp only [log.entryOf]; word])
    | (rw [show W64 ((log.entryOf l).req : Int) = l.RequestID' by simp only [log.entryOf]; word])
  iapply HΦ
  iexists ls
  iframe
  ipureintro; exact ⟨Hmap, Hnn⟩

theorem log.Logs.RequestIDAt.wp_proof : log.Logs.RequestIDAt.spec (GF := GF) (hG := hG) := fun sl dq es i e hi he => by
  wp_start as Hl
  unfold log.ownLogs
  icases Hl with ⟨%ls, Hsl, %Hmap, %Hnn⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  obtain ⟨l, hl, hle⟩ := log.elem_of ls es (sint.nat i - 1) e Hmap he
  have hk : (sint.nat i - 1) < ls.length := (List.getElem?_eq_some_iff.1 hl).1
  wp_auto
  rw [if_pos ⟨by word, by word⟩]
  have hk' : (sint.Z (i - W64 1)).toNat = sint.nat i - 1 := by word
  icases ownSlice_elem_acc (sint.Z (i - W64 1)) l sl dq ls (by word) (by rw [hk']; exact hl) $$ Hsl
    with ⟨Hel, Hclose⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hel with ⟨Hel, %Hnn'⟩
  wp_pures
  iStructNamed Hel
  wp_auto
  ihave Hel := typedPointsto_combine _ l dq Hnn' $$ [Data ClientID RequestID]
  · simp only [TypedPointsto.typedPointstoDef, named]; iframe
  ihave Hsl := Hclose $$ Hel
  have hset : ls.set (sint.nat i - 1) l = ls :=
    List.ext_getElem? (fun n => by rw [List.getElem?_set]; split <;> simp_all)
  rw [hk', hset]
  subst hle
  first
    | (rw [show (log.entryOf l).op = l.Data' from rfl])
    | (rw [show W64 ((log.entryOf l).cid : Int) = l.ClientID' by simp only [log.entryOf]; word])
    | (rw [show W64 ((log.entryOf l).req : Int) = l.RequestID' by simp only [log.entryOf]; word])
  iapply HΦ
  iexists ls
  iframe
  ipureintro; exact ⟨Hmap, Hnn⟩

theorem log.Logs.After.wp_proof : log.Logs.After.spec (GF := GF) (hG := hG) := fun l dl sl es i hi hil => by
  wp_start as ⟨Hl, Hls⟩
  unfold log.ownLogs
  icases Hls with ⟨%ls, #Hsl, %Hmap, %Hnn⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
  ihave %Hptr := log.ownSlice_ptr _ _ _ Hnn $$ Hsl
  have hil' : sint.nat i ≤ ls.length := by rw [← Hmap, List.length_map] at hil; exact hil
  wp_auto
  rw [if_pos ⟨hi, by word, Hwf.2⟩]
  wp_auto
  icases (ownSlice_slice i sl.len sl DFrac.discard ls ⟨hi, by word, Int.le_refl _⟩).1 $$ Hsl
    with ⟨-, H2, -⟩
  iapply HΦ
  iframe
  iexists _
  iframe H2
  ipureintro
  constructor
  · rw [← Hmap, ← List.map_drop]
    congr 1
    simp only [subslice, List.drop_take]
    rw [show sint.nat sl.len - sint.nat i = (ls.drop (sint.nat i)).length by simp; word]
    exact List.take_length
  · intro h
    apply Hptr
    have h2 := congrArg GoSlice.ptr h
    simp only [slice.slice, sliceIndexRef] at h2
    exact go.arrayIndexRef_null_inv _ _ _ h2

theorem log.Logs.Add.wp_proof : log.Logs.Add.spec (GF := GF) (hG := hG) := fun l sl dq es e hdq => by
  wp_start as ⟨Hl, Hls, Hcap⟩
  unfold log.ownLogs
  icases Hls with ⟨%ls, Hsl, %Hmap, %Hnn⟩
  by_cases hv : ✓ dq
  case neg => exact absurd hdq hv
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := log.Log) (t := log.Log.ty) [e]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %p ⟨Hs1, Hc1⟩
  wp_auto
  wp_apply (wp_slice_append_dfrac (V := log.Log) (t := log.Log.ty) sl ls dq _ [e] (DFrac.own 1))
    $$ [$Hsl $Hcap $Hs1] as %s' ⟨Hs', Hcap', -⟩
  · ipureintro; exact hv
  ihave %Hnn' := log.ownSlice_nonnil _ _ _ (by simp) $$ Hs'
  iapply HΦ
  iexists s'
  iframe
  ipureintro
  refine ⟨?_, Hnn'⟩
  rw [List.map_append, Hmap]
  rfl

/-- `append(sl, sl2)` of two empty slices, `sl` non-nil: a non-nil empty slice (Go returns
`sl`). -/
theorem log.wp_append_empty (sl sl2 : GoSlice) (dq dq2 : DFrac) (hp : sl.ptr ≠ null) :
    {{ (sl ↦*{dq} ([] : List log.Log) ∗ ownSliceCap log.Log sl (DFrac.own 1) ∗
        sl2 ↦*{dq2} ([] : List log.Log) : IProp GF) }}
      (App (App (Val #(functions go.append [log.Logs.ty])) (Val #sl)) (Val #sl2))
    {{ (s' : GoSlice), RET #s'; s' ↦*{dq} ([] : List log.Log) ∗
        ownSliceCap log.Log s' (DFrac.own 1) ∗ sl2 ↦*{dq2} ([] : List log.Log) ∗ ⌜s' ≠ slice.nil⌝ }} := by
  wp_start_folded as ⟨Hs, Hcap, Hs2⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hs2
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  simp only [List.length_nil] at Hlen Hlen2
  have hl0 : sl.len = W64 0 := by word
  have hl20 : sl2.len = W64 0 := by word
  iapply wp_slice_append_fits sl sl2 _ ⟨Hlen.2, Hlen2.2⟩ (by word)
  have hp' : sliceIndexRef log.Log (sint.Z sl.len) sl ≠ null := fun h =>
    hp (go.arrayIndexRef_null_inv _ _ _ h)
  ihave Hd := ownSlice_empty (V := log.Log) (DFrac.own 1) (slice.slice sl log.Log sl.len (sl.len + sl2.len))
    (by simp only [slice.slice]; word) (by simp only [slice.slice]; word) $$ [] 
  · simp only [slice.slice]
    iapply array_empty _ _ hp'
  wp_apply +noauto wp_slice_copy _ _ sl2 _ dq2 $$ [Hd Hs2] with %n ⟨%Hn, Hd, Hs2⟩
  · iframe
  isplitl []
  · ipureintro; exact isPanic_intoVal _
  imodintro
  iapply HΦ
  have hp'' : sliceIndexRef log.Log (sint.Z (W64 0)) sl ≠ null := fun h =>
    hp (go.arrayIndexRef_null_inv _ _ _ h)
  iframe Hs2
  isplitl []
  · iapply ownSlice_empty (V := log.Log) dq _ (by simp only [slice.slice]; word)
      (by simp only [slice.slice]; word)
    simp only [slice.slice]
    iapply array_empty _ _ hp''
  isplitl [Hcap]
  · rw [show slice.slice sl log.Log (W64 0) (sl.len + sl2.len) = sl by
      rw [hl0, hl20]
      obtain ⟨p, ln, cp⟩ := sl
      simp only at hl0
      subst hl0
      simp only [slice.slice, sliceIndexRef]
      congr 1
      · rw [show sint.Z (W64 0) = (0 : Int) from rfl]; exact go.arrayIndexRef_0 _ _
      all_goals word]
    iexact Hcap
  · ipureintro
    intro h
    apply hp''
    exact congrArg GoSlice.ptr h

theorem log.Logs.Merge.wp_proof : log.Logs.Merge.spec (GF := GF) (hG := hG) := fun l sl dq es sl2 dq2 es2 hdq => by
  wp_start as ⟨Hl, Hls, Hcap, Hls2⟩
  unfold log.ownLogs
  icases Hls with ⟨%ls, Hsl, %Hmap, %Hnn⟩
  icases Hls2 with ⟨%ls2, Hsl2, %Hmap2, %Hnn2⟩
  by_cases hv : ✓ dq
  case neg => exact absurd hdq hv
  by_cases hne : ls ++ ls2 = []
  case pos =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hne
    ihave %Hptr := log.ownSlice_ptr _ _ _ Hnn $$ Hsl
    wp_auto
    wp_apply (log.wp_append_empty sl sl2 dq dq2 Hptr) $$ [$Hsl $Hcap $Hsl2] as %s' ⟨Hs', Hcap', Hsl2, %Hnn'⟩
    iapply HΦ
    iexists s'
    iframe
    ipureintro
    subst Hmap Hmap2
    exact ⟨⟨rfl, Hnn'⟩, rfl, Hnn2⟩
  wp_auto
  wp_apply (wp_slice_append_dfrac (V := log.Log) (t := log.Log.ty) sl ls dq sl2 ls2 dq2)
    $$ [$Hsl $Hcap $Hsl2] as %s' ⟨Hs', Hcap', Hsl2⟩
  · ipureintro; exact hv
  ihave %Hnn' := log.ownSlice_nonnil _ _ _ hne $$ Hs'
  iapply HΦ
  iexists s'
  iframe
  isplitl []
  · ipureintro
    refine ⟨?_, Hnn'⟩
    rw [List.map_append, Hmap, Hmap2]
  · ipureintro; exact ⟨Hmap2, Hnn2⟩

end proofs
end Perennial.github_com.tangledbytes.go_vsr.pkg
