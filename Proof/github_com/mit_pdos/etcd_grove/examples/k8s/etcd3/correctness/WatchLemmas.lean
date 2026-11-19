/-
Lean-first (no Rocq counterpart).

# Lemmas for the proofs of `correctness/watch.go` (k8s 7g step 5)

- `mlistMatchesW`: `PredOk.lean`'s `mlistMatches` for a predicate `predicate(in)` with any
  `AllowWatchBookmarks` (`watchOptions(in)`'s, which `Model.listItems` and `Change.toWatchEvent`
  receive), which `Matches` does not read;
- `objsDeep_persist`: fresh objects made read-only (`deepRO`);
- `wp_slice_make3_nn`: Perennial's `wp_slice_make3` with the fact that the slice is not `nil` (its
  proof, with that fact added: a capacity `0` slice gets a non-null pre-allocated address), for
  `toEventReference`'s `make([]eventReference, 0, len(events))`, which `cmp.Diff`'s spec compares;
- `annotObj`: `storage.HasInitialEventsEndBookmarkAnnotation` of a read-only driver's `*Obj`: its
  `Annotated` field (`annotL`), from the generic spec and `Obj.GetAnnotations`';
- `evsRO_split`: a read-only event slice split at an index (`events[:i]`, `events[i:]`,
  `splitInitialEvents`);
- `getAttrs_func_ne_nil`: the driver's `getAttrs` is not a nil function (`checkWatch`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.EvRep
public import Spec.k8s_io.apiserver.pkg.storage.HasInitialEventsEndBookmarkAnnotation
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__GetAnnotations

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3 k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input labelSel fieldSel)


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- `{ predicate(in) with AllowWatchBookmarks: b }.Matches(&o)` on a model object at a pointer:
`selOkL x o`. -/
abbrev mlistMatchesW.spec : Prop :=
  ∀ (pp : Loc) (x : Input) (b : Bool) (op : Loc) (o : Obj) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      pp ↦ { predV x with AllowWatchBookmarks' := b } ∗ op ↦{dq} o }}
    (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty
      @!! go!"Matches")) (Val #(interface.mkOk
        (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #op)))
  {{ RET (PairV #(selOkL x o) #GoInterface.nil);
      pp ↦ { predV x with AllowWatchBookmarks' := b } ∗ op ↦{dq} o }}

theorem mlistMatchesW.wp_ok
    (wp_Matches : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) :
    mlistMatchesW.spec (GF := GF) (hG := hG) := by
  intro pp x b op o dq
  iintro %Φ ⟨#Hpkg, Hp, Ho⟩ HΦ
  ihave #Hl := labelSelOk_driver wp_LM wp_LE x $$ Hpkg
  ihave #Hf := fieldSelOk_driver wp_FM wp_FE x $$ Hpkg
  ihave #Hg0 := getAttrsOk_ptr wp_GA dq $$ Hpkg
  ihave #Hg : getAttrsOk (objAtPtr dq) (predV x).GetAttrs' labMapL fldMapL $$ []
  · simp only [predV]; iexact Hg0
  ihave #Ps : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave Hobj : objAtPtr dq (interface.mkOk
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #op) o $$ [Ho]
  · unfold objAtPtr; iexists op; iframe Ho; ipureintro; rfl
  wp_apply (wp_Matches Obj (objAtPtr dq) pp (DFrac.own 1) { predV x with AllowWatchBookmarks' := b }
      _ _ _ _ labMapL fldMapL _ o rfl) $$ [$Hp $Hl $Hf $Hg $Hobj] as ⟨Hp, Hobj⟩
  rw [sel_answer]
  iapply HΦ
  iframe Hp
  unfold objAtPtr
  icases Hobj with ⟨%p', %hp', Ho⟩
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at hp'
  have hpe : op = p' := go.intoVal_inj hp'
  subst hpe
  iexact Ho

/-- **`make([]T, len, cap)` is not `nil`** (`wp_slice_make3`, with that fact). -/
theorem wp_slice_make3_nn {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    {st t : go.GoType} [st ↓u go.SliceType t] [IntoValTyped (GF := GF) V t]
    {s : Stuckness} {E : CoPset}
    (len cap : w64) (hle : 0 ≤ sint.Z len ∧ sint.Z len ≤ sint.Z cap) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.make3 [st])) (Val #len)) (Val #cap)) @ s; E
    {{ (sl : GoSlice), RET #sl;
        sl ↦* (List.replicate (sint.nat len) (zero_val V)) ∗
        ownSliceCap V sl (DFrac.own 1) ∗ ⌜sl.cap = cap⌝ ∗ ⌜sl ≠ slice.nil⌝ }} := by
  wp_start
  wp_if_destruct
  · exfalso; omega
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · wp_apply wp_GoPrealloc as %p %hnn
    have hlen : len = W64 0 := by word
    subst hlen
    iapply HΦ
    isplitl []
    · have : sint.nat (W64 0) = 0 := rfl
      rw [this, List.replicate_zero]
      iapply ownSlice_empty _ _ (by rfl) (by word)
      iapply array_empty _ _ hnn
    isplitl []
    · iapply ownSliceCap_empty _ rfl (by word)
    isplitl []
    · ipureintro; rfl
    · ipureintro
      intro h
      rw [slice_mk_eq_nil] at h
      exact hnn h.1
  · iapply HΦ
    have hz : (zero_val (GoArray V (sint.Z cap))).arr =
        List.replicate (sint.Z cap).toNat (zero_val V) := rfl
    have e := array_split (GF := GF) len p_ptr (DFrac.own 1) _ (zero_val (GoArray V (sint.Z cap)))
      ⟨by omega, by omega⟩
    rw [hz, List.take_replicate, List.drop_replicate,
      show min (sint.nat len) (sint.Z cap).toNat = sint.nat len by word] at e
    icases e.1 $$ p with ⟨Hsl, Hcap⟩
    rw [ownSlice_unseal, ownSliceCap_unseal]; unfold ownSliceDef ownSliceCapDef
    isplitl [Hsl]
    · iright; iframe Hsl; ipureintro; dsimp only; omega
    isplitl [Hcap]
    · iright
      isplit
      · ipureintro; dsimp only; omega
      iexists _
      simp only [sliceIndexRef]
      iexact Hcap
    isplitl []
    · ipureintro; rfl
    · ipureintro
      intro h
      rw [slice_mk_eq_nil] at h
      word

/-- **Fresh objects made read-only.** -/
theorem objsDeep_persist : ∀ (xs : List GoInterface) (os : List Obj),
    ([∗list] y;o ∈ xs;os, deepRep (GF := GF) (DFrac.own 1) y (.obj o)) ⊢
      |==> [∗list] y;o ∈ xs;os, deepRO y (.obj o)
  | [], [] => by
    iintro -
    imodintro
    iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
    iempintro
  | [], _ :: _ => by iintro H; ihave %h := BigSepL2.bigSepL2_nil_inv_left $$ H; cases h
  | _ :: _, [] => by iintro H; ihave %h := BigSepL2.bigSepL2_nil_inv_right $$ H; cases h
  | y :: ys, o :: os => by
    iintro ⟨Hy, Hrest⟩
    iunfold deepRep at Hy
    icases Hy with ⟨%p, %hy, Hp⟩
    imod (typedPointsto_dfractional (GF := GF) p o).dfractional_persist (DFrac.own 1) $$ Hp with Hp
    imod objsDeep_persist ys os $$ Hrest with Hrest
    imodintro
    iframe Hrest
    unfold deepRO deepRep
    iexists p
    iframe Hp
    ipureintro; exact hy

/-- `storage.HasInitialEventsEndBookmarkAnnotation(x)` of a read-only driver's `*Obj`. -/
abbrev annotObj.spec : Prop :=
  ∀ (x : GoInterface) (o : Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ deepRO x (.obj o) }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.HasInitialEventsEndBookmarkAnnotation)) (Val #x))
  {{ RET (PairV #o.Annotated' #GoInterface.nil); True }}

theorem annotObj.wp_ok [storage_sem : k8s_io.apiserver.pkg.storage.Assumptions]
    [meta_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]
    [runtime_sem : k8s_io.apimachinery.pkg.runtime.Assumptions]
    (wp_HI : storage.HasInitialEventsEndBookmarkAnnotation.spec (GF := GF) (hG := hG))
    (wp_GA : k8s_etcd3.Obj.GetAnnotations.spec (GF := GF) (hG := hG)) :
    annotObj.spec (GF := GF) (hG := hG) := by
  intro x o
  unfold deepRO
  iintro %Φ ⟨#Hs, #Hd, #Hx⟩ HΦ
  iunfold deepRep at Hx
  icases Hx with ⟨%p, %hx, #Hp⟩
  subst hx
  have hty := objTyOk_holds.2.2
  iapply (wp_HI ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty, #p⟩
    (p ↦□ o) o.Annotated' hty) $$ [] [HΦ]
  · isplitl []
    · iexact Hs
    isplitl []
    · iexact Hp
    iintro %Ψ #Hp' HΨ
    wp_apply (wp_GA p DFrac.discard o) $$ [] as %m ⟨-, Hm⟩
    · iframe #
    iapply HΨ $$ Hp
    cases ha : o.Annotated'
    · isimp only [ha, Bool.false_eq_true, ↓reduceIte] at Hm
      icases Hm with %hm
      ileft; ipureintro; exact ⟨hm, rfl⟩
    · isimp only [ha, ↓reduceIte] at Hm
      iright
      iexists _, _
      iframe Hm
      ipureintro; simp
  · inext
    iintro -
    iapply HΦ; itrivial

/-- **A read-only event slice split at `k`**: `events[:k]` and `events[k:]`. -/
theorem evsRO_split (sl : GoSlice) (rs : List REv) (k : w64)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z sl.len) :
    evsRO (GF := GF) sl rs ⊢
      evsRO (slice.slice sl k8s_io.apimachinery.pkg.watch.Event (W64 0) k) (rs.take (sint.nat k)) ∗
      evsRO (slice.slice sl k8s_io.apimachinery.pkg.watch.Event k sl.len) (rs.drop (sint.nat k)) := by
  iintro #Hs
  iunfold evsRO at Hs
  icases Hs with ⟨%vs, #Hsl, #Hvs⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hvs
  icases (ownSlice_split_all k sl DFrac.discard vs hk).1 $$ Hsl with ⟨#H1, #H2⟩
  have e : ([∗list] v;r ∈ vs;rs, evRep (GF := GF) v r) ⊣⊢
      ([∗list] v;r ∈ vs.take (sint.nat k) ++ vs.drop (sint.nat k);
        rs.take (sint.nat k) ++ rs.drop (sint.nat k), evRep (GF := GF) v r) := by
    rw [List.take_append_drop, List.take_append_drop]; exact .rfl
  icases (e.1.trans (BigSepL2.bigSepL2_append (Or.inl (by simp [Hl2])) ).1) $$ Hvs with ⟨#Hv1, #Hv2⟩
  isplitl []
  · iunfold evsRO
    iexists _
    iframe H1 Hv1
  · iunfold evsRO
    iexists _
    iframe H2 Hv2

/-- The driver's `getAttrs` is not a nil function (a copy of `Model__list.lean`'s `getAttrs_ne_nil`,
which a proof file cannot import). -/
theorem getAttrs_func_ne_nil :
    functions github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs [] ≠ func.nil := by
  intro h
  have hu := FuncUnfold.func_unfold (f := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs)
    (type_args := [])
  rw [h, go.intoVal_unfold GoFunc] at hu
  simp [func.nil, github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs.impl] at hu

end proof

end k8s_correctness
end EtcdGrove
end Perennial
