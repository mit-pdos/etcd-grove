/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/Config__Clone.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Config__Clone

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The body of `Clone`'s closure `clone := func(m map[uint64]struct{}) map[uint64]struct{}
{ if m == nil { return nil }; mm := make(..., len(m)); for k := range m { mm[k] = {} };
return mm }`, copied from the translation (`Config.Clone.impl`,
`Code/go_etcd_io/raft/v3/tracker.lean`) so that its triple is proved once for its four
calls. -/
noncomputable abbrev cloneMapBody [FfiSyntax] [GoGlobalContext] : Expr :=
  (App (Val exceptionDo)
  (Let "m" (App (Val (GoInstruction (GoAlloc (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (Var "m"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (App (Val (GoInstruction (FuncResolve go.make2 [(go.GoType.MapType go.uint64 (go.GoType.StructType []))]))) (Val #())) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (Var "m"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.MapType go.uint64 (go.GoType.StructType []))]))) (Val #())) (Var "$a0"))))
  (Let "mm" (App (Val (GoInstruction (GoAlloc (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (App (Val (GoInstruction (GoZeroVal (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (Var "mm")))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (Var "m"))
  (Let "k" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (App (App (Val (map.forRange go.uint64 (go.GoType.StructType []))) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (CompositeLiteral (go.GoType.StructType [])))) (LiteralValue []))
  (App (Val doExecute)
  (App (App (App (Val (map.insert go.uint64)) (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (Var "mm"))) (App (Val (GoInstruction (GoLoad go.uint64))) (Var "k"))) (Var "$r0"))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "k") (Var "$key")))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (Pair (Var "mm") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (Var "m")) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (Val UntypedNil)))))
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.MapType go.uint64 (go.GoType.StructType []))))) (Val UntypedNil)))
  (App (Val doExecute)
  (Val #()))))))

/-- What the closure returns for `m`: `nil` for `nil`, otherwise a fresh map with `s`. -/
def clonedMap (m m' : Loc) (s : GMap w64 Unit) : IProp GF :=
  iprop(⌜m = map.nil ∧ m' = map.nil⌝ ∨ (⌜m ≠ map.nil⌝ ∗ m' ↦$ s))

/-- The closure. The function value is a variable `f` fixed to the literal, so that
`wp_auto` cannot inline the call. -/
theorem wp_cloneMap (f : GoFunc) (hf : f = func.mk BAnon (BNamed "m") cloneMapBody)
    (m : Loc) (dq : DFrac) (s : GMap w64 Unit) :
    {{ ownIdsetQ (GF := GF) m dq s }}
      (App (Val #f) (Val #m))
    {{ (m' : Loc), RET #m'; ownIdsetQ m dq s ∗ clonedMap m m' s }} := by
  subst hf
  wp_start_folded as Hm
  wp_auto
  unfold ownIdsetQ clonedMap
  icases Hm with (⟨%Hnil, %Hs⟩ | Hm)
  · subst Hnil Hs
    wp_auto
    iapply HΦ
    isplitl
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
  ihave %Hvnn := ownMap_not_nil _ _ _ $$ Hm
  wp_if_destruct
  · exact absurd rfl Hvnn
  wp_apply wp_map_len $$ Hm as Hm
  wp_apply wp_map_make2 as %mref Hmref
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64)
      (mv : GMap w64 Unit),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hmv" ∷ ⌜∀ k, k ∈ domSet mv ↔ k ∈ keys.take i.toNat⌝ ∗
      "k" ∷ k_ptr ↦ x ∗
      "mm" ∷ mm_ptr ↦ mref ∗
      "Hmref" ∷ mref ↦$ mv)) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [k mm Hmref]
  · iexists zero_val w64, ∅
    simp only [named]
    iframe k mm Hmref
    ipureintro
    refine ⟨Int.le_refl _, fun k => ?_⟩
    simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, iff_false]
    rw [GMap.elem_of_dom]
    rintro ⟨v, hv⟩
    simp at hv
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_mapInsert $$ Hmref as Hmref
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, _
    simp only [named]
    iframe k mm Hmref
    ipureintro
    refine ⟨by omega, fun k => ?_⟩
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake, List.mem_append, List.mem_singleton, ← Hmv, GMap.elem_of_dom,
      GMap.elem_of_dom]
    by_cases hk : key = k
    · subst hk; simp
    · rw [GMap.lookup_insert_ne _ _ hk]
      constructor
      · intro h; exact .inl h
      · rintro (h | h)
        · exact h
        · exact absurd h.symm hk
  iintro HP Hm
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv
  -- the copy is `s` itself: same keys, and the values are `()`
  have Hmv' : mv = s := by
    apply GMap.map_eq; intro k
    have := Hmv k
    rw [Hkset, GMap.elem_of_dom] at this
    rcases h1 : mv !! k with _ | ⟨⟩ <;> rcases h2 : s !! k with _ | ⟨⟩ <;> simp_all
  subst Hmv'
  wp_auto
  iapply HΦ
  isplitl [Hm]
  · iright; iexact Hm
  · iright; iframe Hmref; ipureintro; exact Hvnn

/-- An id set's clone, as an id set. -/
theorem clonedMap_Q (m m' : Loc) (dq : DFrac) (s : GMap w64 Unit) :
    ownIdsetQ (GF := GF) m dq s -∗ clonedMap m m' s -∗
      ownIdsetQ m dq s ∗ ownIdsetQ m' (DFrac.own 1) s := by
  iintro Hm Hc
  unfold ownIdsetQ clonedMap
  icases Hm with (%H | Hm)
  · isplitr
    · ileft; ipureintro; exact H
    icases Hc with (%H' | ⟨%Hnn, -⟩)
    · ileft; ipureintro; exact ⟨H'.2, H.2⟩
    · exact absurd H.1 Hnn
  · icases Hc with (%H' | ⟨-, H'⟩)
    · ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
      exact absurd H'.1 Hnn
    · isplitl [Hm]
      · iright; iexact Hm
      · iright; iexact H'

/-- A canonical id set's clone is canonical. -/
theorem clonedMap_C (m m' : Loc) (dq : DFrac) (s : GMap w64 Unit) :
    ownIdsetC (GF := GF) m dq s -∗ clonedMap m m' s -∗
      ownIdsetC m dq s ∗ ownIdsetC m' (DFrac.own 1) s := by
  iintro Hm Hc
  unfold ownIdsetC clonedMap
  icases Hm with (%H | ⟨Hm, %Hne⟩)
  · isplitr
    · ileft; ipureintro; exact H
    icases Hc with (%H' | ⟨%Hnn, -⟩)
    · ileft; ipureintro; exact ⟨H'.2, H.2⟩
    · exact absurd H.1 Hnn
  · icases Hc with (%H' | ⟨-, H'⟩)
    · ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
      exact absurd H'.1 Hnn
    · isplitl [Hm]
      · iright; iframe Hm; ipureintro; exact Hne
      · iright; iframe H'; ipureintro; exact Hne

theorem tracker.Config.Clone.wp_proof : tracker.Config.Clone.spec (GF := GF) (hG := hG) := by
  intro p cfg c dq dqc
  wp_start as ⟨Hp, Hc⟩
  unfold ownCfgCC
  iNamed Hc
  wp_auto
  -- the closure, as an opaque function value (so that its calls are not inlined)
  generalize hf : (func.mk BAnon (BNamed "m") cloneMapBody : GoFunc) = f
  -- the receiver is read at fraction `dq`: split the struct into its fields, then peel
  -- `Voters[0]` and `Voters[1]` off the array
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  icases array_acc _ (sint.Z (W64 0)) _ _ _ vin (by decide) (by rw [Harr]; rfl)
    $$ Voters with ⟨Hv0, Hvback⟩
  wp_auto
  ihave %Hinnn := ownMap_not_nil _ _ _ $$ Hin
  ihave Hin : ownIdsetQ vin dqc c.incoming $$ [Hin]
  · unfold ownIdsetQ; iright; iexact Hin
  wp_apply (wp_cloneMap f hf.symm) $$ Hin as %m0 ⟨Hin, Hm0⟩
  ihave Voters := Hvback $$ Hv0
  icases array_acc _ (sint.Z (W64 1)) _ _ _ vout (by decide)
    (by
      rw [list_set_lookup_self _ _ _ (show cfg.Voters'.arr[(sint.Z (W64 0)).toNat]? = some vin by
        rw [Harr]; rfl)]
      show cfg.Voters'.arr[(sint.Z (W64 1)).toNat]? = some vout
      rw [Harr]; rfl)
    $$ Voters with ⟨Hv1, Hvback⟩
  wp_auto
  icases ownIdsetC_split _ _ _ $$ Hout with ⟨Hout, %Hcout⟩
  wp_apply (wp_cloneMap f hf.symm) $$ Hout as %m1 ⟨Hout, Hm1⟩
  ihave Hout := ownIdsetC_join _ _ _ Hcout $$ Hout
  icases clonedMap_C _ _ _ _ $$ Hout Hm1 with ⟨Hout, Hm1⟩
  icases ownIdsetC_split _ _ _ $$ Hl with ⟨Hl, %Hcl⟩
  wp_apply (wp_cloneMap f hf.symm) $$ Hl as %ml ⟨Hl, Hml⟩
  ihave Hl := ownIdsetC_join _ _ _ Hcl $$ Hl
  icases clonedMap_C _ _ _ _ $$ Hl Hml with ⟨Hl, Hml⟩
  icases ownIdsetC_split _ _ _ $$ Hln with ⟨Hln, %Hcln⟩
  wp_apply (wp_cloneMap f hf.symm) $$ Hln as %mln ⟨Hln, Hmln⟩
  ihave Hln := ownIdsetC_join _ _ _ Hcln $$ Hln
  icases clonedMap_C _ _ _ _ $$ Hln Hmln with ⟨Hln, Hmln⟩
  iapply HΦ
  ihave Voters := Hvback $$ Hv1
  rw [list_set_lookup_self _ _ _ (show cfg.Voters'.arr[(sint.Z (W64 0)).toNat]? = some vin by
    rw [Harr]; rfl)]
  rw [show (array.mk 2 cfg.Voters'.arr).arr = cfg.Voters'.arr from rfl]
  rw [list_set_lookup_self _ _ _ (show cfg.Voters'.arr[(sint.Z (W64 1)).toNat]? = some vout by
    rw [Harr]; rfl)]
  isplitl [AutoLeave Learners LearnersNext Voters]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  isplitl [Hin Hout Hl Hln]
  · iexists vin, vout
    simp only [named]
    unfold ownIdsetQ
    icases Hin with (%H | Hin)
    · exact absurd H.1 Hinnn
    iframe Hin Hout Hl Hln
    ipureintro; exact ⟨Harr, Hal⟩
  iexists m0, m1
  simp only [named]
  unfold clonedMap
  icases Hm0 with (%H | ⟨-, Hm0⟩)
  · exact absurd H.1 Hinnn
  iframe Hm0 Hm1 Hml Hmln
  ipureintro
  simp only [List.set, List.replicate]
  rfl

end proof

end EtcdGrove
end Perennial
