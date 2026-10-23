/-
`OpGet` (and its callees `applyOpts`, `IsOptsWithPrefix`, `IsOptsWithFromKey`) over options that
need a resource (`optsAtRes`), the vertical slice's unit V2: the proofs of `OpGet.lean`,
`Op__applyOpts.lean`, `IsOptsWithPrefix.lean`, `IsOptsWithFromKey.lean` with the resource passed
along (their specs, which the clients' Links use, take `optsAt`: `optsAt_res`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.client.v3.NewOp
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem applyOpts_res (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpFull) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦ op ∗ opFullAt op o ∗
        optsAtRes sl gs R ∗ R }}
      (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"applyOpts"))
        (Val #sl))
    {{ (op' : go_etcd_io.etcd.client.v3.Op), RET #(); opp ↦ op' ∗ opFullAt op' (opFold gs o) ∗ R }} := by
  wp_start as ⟨Hop, #Hat, #Hopts, HR⟩
  unfold optsAtRes
  icases Hopts with ⟨%fs, #Hfs, %Hlen, #Hf⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hfs
  wp_auto
  ihave IH : iprop(∃ (n : w64) (op' : go_etcd_io.etcd.client.v3.Op) (f0 : GoFunc),
      "i" ∷ i_ptr ↦ n ∗ "Hop" ∷ opp ↦ op' ∗ "opt" ∷ opt_ptr ↦ f0 ∗ "HR" ∷ R ∗
      "#Hat" ∷ opFullAt op' (opFold (gs.take (sint.nat n)) o) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i Hop opt HR]
  · iexists W64 0, op, _
    simp only [named]
    iframe
    isplitl []
    · simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, op_simps, List.foldl_nil]
      iexact Hat
    ipureintro; constructor <;> word
  iclear Hat
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < fs.length := by word
    obtain ⟨f, Hfi⟩ : ∃ f, fs[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨g, Hgi⟩ : ∃ g, gs[sint.nat n]? = some g :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) fs DFrac.discard f Hn.1 $$ [Hfs] as -
    · iframe #; ipureintro; exact Hfi
    ihave #Hg := Hf $$ %(sint.nat n) %f %g %Hfi %Hgi
    unfold optSpecRes
    wp_apply Hg $$ [$Hop $Hat $HR] as %op'' ⟨HR, Hop, #Hat'⟩
    wp_for_post
    iframe
    iexists n + W64 1, op'', f
    simp only [named]
    iframe
    isplitl []
    · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, opFold_take_succ gs o _ g Hgi]
      iexact Hat'
    ipureintro; constructor <;> word
  · have Hge : sint.nat n = gs.length := by rw [← Hlen]; word
    iapply HΦ
    iframe
    rw [show opFold gs o = opFold (gs.take (sint.nat n)) o by rw [Hge, List.take_length]]
    iexact Hat


theorem isOptsWithPrefix_res (wp_NewOp : NewOp.spec (GF := GF) (hG := hG)) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAtRes sl gs R ∗ R }}
      (App (Val (@! go_etcd_io.etcd.client.v3.IsOptsWithPrefix)) (Val #sl))
    {{ RET #((opFold gs OpFull.newOp).withPrefix); R }} := by
  wp_start as ⟨#Hopts, HR⟩
  unfold optsAtRes
  icases Hopts with ⟨%fs, #Hfs, %Hlen, #Hf⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hfs
  wp_alloc o_ptr as Ho
  wp_auto
  wp_apply wp_NewOp as %opp %op ⟨Hop, #Hat⟩
  ihave IH : iprop(∃ (n : w64) (op' : go_etcd_io.etcd.client.v3.Op) (f0 : GoFunc),
      "i" ∷ i_ptr ↦ n ∗ "Hop" ∷ opp ↦ op' ∗ "opt" ∷ opt_ptr ↦ f0 ∗ "HR" ∷ R ∗
      "#Hat" ∷ opFullAt op' (opFold (gs.take (sint.nat n)) OpFull.newOp) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i Hop opt HR]
  · iexists W64 0, op, _
    simp only [named]
    iframe
    isplitl []
    · simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, op_simps, List.foldl_nil]
      iexact Hat
    ipureintro; constructor <;> word
  iclear Hat
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < fs.length := by word
    obtain ⟨f, Hfi⟩ : ∃ f, fs[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨g, Hgi⟩ : ∃ g, gs[sint.nat n]? = some g :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) fs DFrac.discard f Hn.1 $$ [Hfs] as -
    · iframe #; ipureintro; exact Hfi
    ihave #Hg := Hf $$ %(sint.nat n) %f %g %Hfi %Hgi
    unfold optSpecRes
    wp_apply Hg $$ [$Hop $Hat $HR] as %op'' ⟨HR, Hop, #Hat'⟩
    wp_for_post
    iframe
    iexists n + W64 1, op'', f
    simp only [named]
    iframe
    isplitl []
    · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, opFold_take_succ gs _ _ g Hgi]
      iexact Hat'
    ipureintro; constructor <;> word
  · have Hge : sint.nat n = gs.length := by rw [← Hlen]; word
    rw [Hge, List.take_length] at *
    unfold opFullAt
    icases Hat with ⟨-, -, %Ht, -, -⟩
    rw [Ht.2.2.1]
    iapply HΦ
    iexact HR


theorem isOptsWithFromKey_res (wp_NewOp : NewOp.spec (GF := GF) (hG := hG)) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAtRes sl gs R ∗ R }}
      (App (Val (@! go_etcd_io.etcd.client.v3.IsOptsWithFromKey)) (Val #sl))
    {{ RET #((opFold gs OpFull.newOp).withFromKey); R }} := by
  wp_start as ⟨#Hopts, HR⟩
  unfold optsAtRes
  icases Hopts with ⟨%fs, #Hfs, %Hlen, #Hf⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hfs
  wp_alloc o_ptr as Ho
  wp_auto
  wp_apply wp_NewOp as %opp %op ⟨Hop, #Hat⟩
  ihave IH : iprop(∃ (n : w64) (op' : go_etcd_io.etcd.client.v3.Op) (f0 : GoFunc),
      "i" ∷ i_ptr ↦ n ∗ "Hop" ∷ opp ↦ op' ∗ "opt" ∷ opt_ptr ↦ f0 ∗ "HR" ∷ R ∗
      "#Hat" ∷ opFullAt op' (opFold (gs.take (sint.nat n)) OpFull.newOp) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i Hop opt HR]
  · iexists W64 0, op, _
    simp only [named]
    iframe
    isplitl []
    · simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, op_simps, List.foldl_nil]
      iexact Hat
    ipureintro; constructor <;> word
  iclear Hat
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < fs.length := by word
    obtain ⟨f, Hfi⟩ : ∃ f, fs[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨g, Hgi⟩ : ∃ g, gs[sint.nat n]? = some g :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) fs DFrac.discard f Hn.1 $$ [Hfs] as -
    · iframe #; ipureintro; exact Hfi
    ihave #Hg := Hf $$ %(sint.nat n) %f %g %Hfi %Hgi
    unfold optSpecRes
    wp_apply Hg $$ [$Hop $Hat $HR] as %op'' ⟨HR, Hop, #Hat'⟩
    wp_for_post
    iframe
    iexists n + W64 1, op'', f
    simp only [named]
    iframe
    isplitl []
    · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, opFold_take_succ gs _ _ g Hgi]
      iexact Hat'
    ipureintro; constructor <;> word
  · have Hge : sint.nat n = gs.length := by rw [← Hlen]; word
    rw [Hge, List.take_length] at *
    unfold opFullAt
    icases Hat with ⟨-, -, %Ht, -, -⟩
    rw [Ht.2.2.2.1]
    iapply HΦ
    iexact HR


/-- **`OpGet(key, opts...)` over options needing a resource `R`** (`optsAtRes`; `OpGet.spec`'s
case `R = True`; the vertical slice's unit V2, for `isEtcdKVTodo`'s gets): the options are called
one at a time (twice by the panic checks, once by `applyOpts`), `R` passed along. -/
theorem opGet_res (wp_NewOp : NewOp.spec (GF := GF) (hG := hG)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAtRes sl gs R ∗ R ∗
        ⌜¬ opGetPanics gs⌝ }}
      (App (App (Val (@! go_etcd_io.etcd.client.v3.OpGet)) (Val #key)) (Val #sl))
    {{ (op : go_etcd_io.etcd.client.v3.Op), RET #op; opFullAt op (opGetModel key gs) ∗ R }} := by
  wp_start as ⟨#Hopts, HR, %Hnp⟩
  wp_alloc o_ptr as Ho
  wp_auto
  wp_apply (isOptsWithPrefix_res wp_NewOp sl gs R) $$ [$Hopts $HR] as HR
  have Hrest : ∀ Φ' : val → IProp GF,
      (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ o_ptr ↦ sl ∗
        optsAtRes sl gs R ∗ R ∗ (∀ op, opFullAt op (opGetModel key gs) -∗ R -∗ Φ' #op)) ⊢
      WP (exceptionDo
        (let: "$r0" :=
          let: "$v1" := (Convert go.string go.byte.SliceType) #key in
            (CompositeLiteral go_etcd_io.etcd.client.v3.Op.ty)
              (LiteralValue
                [KeyedElement (some (KeyField go!"t"))
                    (ElementExpression go_etcd_io.etcd.client.v3.opType.ty go_etcd_io.etcd.client.v3.tRange),
                  KeyedElement (some (KeyField go!"key")) (ElementExpression go.byte.SliceType "$v1")]) in
          let: "ret" := (GoAlloc go_etcd_io.etcd.client.v3.Op.ty) ((GoZeroVal go_etcd_io.etcd.client.v3.Op.ty) #()) in
            do: "ret" <-[go_etcd_io.etcd.client.v3.Op.ty] "$r0" ;;;
              do:
                  (let: "$a0" := ![go_etcd_io.etcd.client.v3.OpOption.ty.SliceType] #o_ptr in
                    ((MethodResolve go_etcd_io.etcd.client.v3.Op.ty.PointerType go!"applyOpts") "ret") "$a0") ;;;
                return: ![go_etcd_io.etcd.client.v3.Op.ty] "ret")) {{ Φ' }}) := by
    intro Φ'
    iintro ⟨#Hpkg, Ho, #Hopts, HR, HΦ'⟩
    iapply wp_fupd
    wp_apply wp_string_to_bytes key as %ksl ⟨Hks, -⟩
    ipersist Hks
    wp_apply (applyOpts_res ret_ptr _ (OpFull.getInit key) sl gs R) $$ [$ret $HR] as %op' ⟨Hret, #Hat, HR⟩
    · iframe #
      unfold opFullAt opAt OpFields
      dsimp only [op_simps]
      isplitl []
      · isplitl []
        · ipureintro; simp
        · iapply ownSlice_nil
      isplitl []
      · iexact Hks
      isplitl []
      · ipureintro; simp
      isplitl []
      · iapply ownSlice_nil
      · unfold opSortAt; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    imodintro
    iapply HΦ' $$ [] [$HR]
    unfold opGetModel
    iexact Hat
  cases hp : (opFold gs OpFull.newOp).withPrefix
  · wp_auto
    iapply Hrest
    iframe
    iframe #
    iintro %op #Hop HR
    iapply HΦ
    iframe
    iexact Hop
  · wp_auto
    wp_apply (isOptsWithFromKey_res wp_NewOp sl gs R) $$ [$Hopts $HR] as HR
    cases hk : (opFold gs OpFull.newOp).withFromKey
    · wp_auto
      iapply Hrest
      iframe
      iframe #
      iintro %op #Hop HR
      iapply HΦ
      iframe
      iexact Hop
    · exact absurd ⟨hp, hk⟩ Hnp

end proof

end EtcdGrove
end Perennial
