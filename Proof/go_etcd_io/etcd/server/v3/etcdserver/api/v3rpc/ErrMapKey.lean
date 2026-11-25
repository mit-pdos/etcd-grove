/-
**`togRPCError`'s error map's keys** (ctx-leaf-fix, 2026-11-25). Lean-first.

`togRPCError` looks its error up in `toGRPCErrorMap`, a `map[error]error` whose keys are pointer
errors (`errors.New`'s). The error may be `context.DeadlineExceeded`'s `deadlineExceededError{}` or
a bcrypt `InvalidCostError` (an `int`), neither a pointer. Perennial's interface keys
(`mapKeys_interface`) are `nil` and pointers only, and invite a proof that needs other keys to give
its own instance (as `v3rpc.streamKeys` does for the leader monitor): `v3rpc.errKeys`, the keys
`errKeyOk` (`apply/Base.lean`), with `v3rpc.safeMapKey_errKeys`, from `==`'s reduction on
interfaces (the dynamic types, then the values: pointers, a field-less struct, `int`s).
`v3rpc.wp_errMap_lookup2` looks such a key up in a read-only map owned at Perennial's keys (every
pointer or `nil` key is an `errKeyOk` one, `v3rpc.ownMap_keys_mono`).

Until then the error was a `SafeMapKey` at Perennial's keys, which no non-pointer is
(`notes/axiom-review/ctx-readerrs-vacuity.md`, `notes/bcrypt-invalidcost-false.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.errors.CtxErr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode

/-- **`togRPCError`'s map keys** (a `MapKeys` instance for local use, not a global one): the
`errKeyOk` errors. -/
@[instance_reducible] def v3rpc.errKeys [GooseExts] [GoGlobalContext] : MapKeys GoInterface :=
  ⟨errKeyOk⟩

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `==` at `error` of `nil` and `nil`. -/
theorem v3rpc.wp_eq_nil_nil (s : Stuckness) (E : CoPset) (Φ : val → IProp GF) :
    Φ #(decide ((GoInterface.nil : GoInterface) = GoInterface.nil)) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals go.error)))
        (Val (PairV #(GoInterface.nil : GoInterface) #(GoInterface.nil : GoInterface)))) @ s; E
        {{ Φ }} := by
  rw [show decide ((GoInterface.nil : GoInterface) = GoInterface.nil) = true by simp]
  iintro HΦ
  wp_auto
  iapply HΦ

/-- `==` at `error` of `nil` and a non-nil interface. -/
theorem v3rpc.wp_eq_nil_ok (t : go.GoType) (v : val) (s : Stuckness) (E : CoPset)
    (Φ : val → IProp GF) :
    Φ #(decide ((GoInterface.nil : GoInterface) = interface.mkOk t v)) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals go.error)))
        (Val (PairV #(GoInterface.nil : GoInterface) #(interface.mkOk t v)))) @ s; E {{ Φ }} := by
  rw [show decide ((GoInterface.nil : GoInterface) = interface.mkOk t v) = false by
    simp [interface.mkOk]]
  iintro HΦ
  wp_auto
  iapply HΦ

/-- `==` at `error` of a non-nil interface and `nil`. -/
theorem v3rpc.wp_eq_ok_nil (t : go.GoType) (v : val) (s : Stuckness) (E : CoPset)
    (Φ : val → IProp GF) :
    Φ #(decide (interface.mkOk t v = (GoInterface.nil : GoInterface))) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals go.error)))
        (Val (PairV #(interface.mkOk t v) #(GoInterface.nil : GoInterface)))) @ s; E {{ Φ }} := by
  rw [show decide (interface.mkOk t v = (GoInterface.nil : GoInterface)) = false by
    simp [interface.mkOk]]
  iintro HΦ
  wp_auto
  iapply HΦ

/-- `==` at `error` of two interfaces of different dynamic types: `false`. -/
theorem v3rpc.wp_eq_ty_ne (t t' : go.GoType) (v v' : val) (ht : t ≠ t') (s : Stuckness)
    (E : CoPset) (Φ : val → IProp GF) :
    Φ #(decide (interface.mkOk t v = interface.mkOk t' v')) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals go.error)))
        (Val (PairV #(interface.mkOk t v) #(interface.mkOk t' v')))) @ s; E {{ Φ }} := by
  rw [decide_eq_false (fun h => ht ((interface_mkOk_inj t t' v v').1 h).1)]
  iintro HΦ
  wp_pures
  rw [if_neg ht]
  wp_auto
  iapply HΦ

/-- `==` at `error` of two interfaces of one dynamic type `t` whose `==` is the equality of the
values of `V`: the equality of the interfaces. -/
theorem v3rpc.wp_eq_same {V : Type} [DecidableEq V] (t : go.GoType)
    (hinj : Function.Injective (intoVal (V := V)))
    [hchk : ⟦CheckComparable t, #()⟧ ⤳ #()]
    [heq : ∀ v1 v2 : V, ⟦GoOp GoEquals t, (#v1, #v2)⟧ ⤳ #(decide (v1 = v2))]
    (v v' : V) (s : Stuckness) (E : CoPset) (Φ : val → IProp GF) :
    Φ #(decide (interface.mkOk t #v = interface.mkOk t #v')) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals go.error)))
        (Val (PairV #(interface.mkOk t #v) #(interface.mkOk t #v')))) @ s; E {{ Φ }} := by
  have h : decide (interface.mkOk t #v = interface.mkOk t #v') = decide (v = v') := by
    by_cases hv : v = v'
    · subst hv; simp
    · have hv' : ¬ (#v : val) = #v' := fun e => hv (hinj e)
      simp only [interface_mkOk_inj, _root_.true_and]
      simp [hv, hv']
  rw [h]
  iintro HΦ
  wp_auto
  iapply HΦ

variable [ctx_sem : _root_.Perennial.context.Assumptions]
variable [bc_sem : _root_.Perennial.golang_org.x.crypto.bcrypt.Assumptions]

omit bc_sem in
/-- `==` at `error` of `deadlineExceededError{}` with itself: `true`. -/
theorem v3rpc.wp_eq_de (s : Stuckness) (E : CoPset) (Φ : val → IProp GF) :
    Φ #(decide (interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
        #(zero_val _root_.Perennial.context.deadlineExceededError) =
      interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
        #(zero_val _root_.Perennial.context.deadlineExceededError))) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals go.error)))
        (Val (PairV
          #(interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
            #(zero_val _root_.Perennial.context.deadlineExceededError))
          #(interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
            #(zero_val _root_.Perennial.context.deadlineExceededError))))) @ s; E {{ Φ }} := by
  haveI : ⟦CheckComparable _root_.Perennial.context.deadlineExceededError.ty, #()⟧ ⤳ #() := by
    have hf : _root_.Perennial.context.deadlineExceededError.fields = [] := by
      unfold _root_.Perennial.context.deadlineExceededError.fields; rfl
    haveI : ⟦CheckComparable (go.StructType _root_.Perennial.context.deadlineExceededError.fields),
        #()⟧ ⤳[under] #() := by
      rw [hf]; infer_instance
    infer_instance
  haveI : ∀ v1 v2 : _root_.Perennial.context.deadlineExceededError,
      ⟦GoOp GoEquals _root_.Perennial.context.deadlineExceededError.ty, (#v1, #v2)⟧ ⤳
        #(decide (v1 = v2)) := fun v1 v2 => by
    have hd : decide (v1 = v2) = true := decide_eq_true (by cases v1; cases v2; rfl)
    rw [hd]
    infer_instance
  exact v3rpc.wp_eq_same _root_.Perennial.context.deadlineExceededError.ty
    (fun a b _ => by cases a; cases b; rfl)
    (zero_val _root_.Perennial.context.deadlineExceededError)
    (zero_val _root_.Perennial.context.deadlineExceededError) s E Φ

omit ctx_sem in
/-- `==` at `error` of two `InvalidCostError`s: the equality of the `int`s. -/
theorem v3rpc.wp_eq_ic (c c' : w64) (s : Stuckness) (E : CoPset) (Φ : val → IProp GF) :
    Φ #(decide (interface.mkOk _root_.Perennial.golang_org.x.crypto.bcrypt.InvalidCostError.ty #c =
      interface.mkOk _root_.Perennial.golang_org.x.crypto.bcrypt.InvalidCostError.ty #c')) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals go.error)))
        (Val (PairV #(interface.mkOk _root_.Perennial.golang_org.x.crypto.bcrypt.InvalidCostError.ty #c)
          #(interface.mkOk _root_.Perennial.golang_org.x.crypto.bcrypt.InvalidCostError.ty #c')))) @ s; E
        {{ Φ }} :=
  v3rpc.wp_eq_same _root_.Perennial.golang_org.x.crypto.bcrypt.InvalidCostError.ty
    GoGlobalContext.intoVal_inj_w64 c c' s E Φ

/-- The three non-nil kinds of `errKeyOk` keys have different dynamic types. -/
theorem v3rpc.de_ne_ptr (T : go.GoType) :
    _root_.Perennial.context.deadlineExceededError.ty ≠ go.GoType.PointerType T := by
  unfold _root_.Perennial.context.deadlineExceededError.ty; intro h; cases h

theorem v3rpc.ic_ne_ptr (T : go.GoType) :
    _root_.Perennial.golang_org.x.crypto.bcrypt.InvalidCostError.ty ≠ go.GoType.PointerType T := by
  unfold _root_.Perennial.golang_org.x.crypto.bcrypt.InvalidCostError.ty; intro h; cases h

theorem v3rpc.de_ne_ic :
    _root_.Perennial.context.deadlineExceededError.ty ≠
      _root_.Perennial.golang_org.x.crypto.bcrypt.InvalidCostError.ty := by
  unfold _root_.Perennial.context.deadlineExceededError.ty
    _root_.Perennial.golang_org.x.crypto.bcrypt.InvalidCostError.ty
  intro h; cases h

/-- **`==` on two `errKeyOk` keys at `error` is equality.** -/
theorem v3rpc.wp_errKey_eq (k k' : GoInterface) (hk : errKeyOk k) (hk' : errKeyOk k')
    (s : Stuckness) (E : CoPset) (Φ : val → IProp GF) :
    Φ #(decide (k = k')) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals go.error))) (Val (PairV #k #k'))) @ s; E
        {{ Φ }} := by
  rcases hk with rfl | ⟨t, l, rfl⟩ | rfl | ⟨c, rfl⟩ <;>
    rcases hk' with rfl | ⟨t', l', rfl⟩ | rfl | ⟨c', rfl⟩
  · exact v3rpc.wp_eq_nil_nil s E Φ
  · exact v3rpc.wp_eq_nil_ok _ _ s E Φ
  · exact v3rpc.wp_eq_nil_ok _ _ s E Φ
  · exact v3rpc.wp_eq_nil_ok _ _ s E Φ
  · exact v3rpc.wp_eq_ok_nil _ _ s E Φ
  · exact (safeMapKey_interface_pointer (GF := GF) go.error t l).wp_go_eq_map_key _
      (Or.inr ⟨t', l', rfl⟩) s E Φ
  · exact v3rpc.wp_eq_ty_ne _ _ _ _ (v3rpc.de_ne_ptr t).symm s E Φ
  · exact v3rpc.wp_eq_ty_ne _ _ _ _ (v3rpc.ic_ne_ptr t).symm s E Φ
  · exact v3rpc.wp_eq_ok_nil _ _ s E Φ
  · exact v3rpc.wp_eq_ty_ne _ _ _ _ (v3rpc.de_ne_ptr t') s E Φ
  · exact v3rpc.wp_eq_de s E Φ
  · exact v3rpc.wp_eq_ty_ne _ _ _ _ v3rpc.de_ne_ic s E Φ
  · exact v3rpc.wp_eq_ok_nil _ _ s E Φ
  · exact v3rpc.wp_eq_ty_ne _ _ _ _ (v3rpc.ic_ne_ptr t') s E Φ
  · exact v3rpc.wp_eq_ty_ne _ _ _ _ v3rpc.de_ne_ic.symm s E Φ
  · exact v3rpc.wp_eq_ic c c' s E Φ

attribute [local instance 1100] v3rpc.errKeys in
/-- **An `errKeyOk` error is a safe key** of a map at `v3rpc.errKeys`. -/
theorem v3rpc.safeMapKey_errKeys (k : GoInterface) (hk : errKeyOk k) :
    SafeMapKey (GF := GF) go.error k where
  key_ok := hk
  wp_go_eq_map_key k' hk' s E Φ := v3rpc.wp_errKey_eq k k' hk hk' s E Φ

omit ctx_sem bc_sem in
/-- A map owned at keys `k1` is owned at any keys `k2` that admit every key `k1` does. -/
theorem v3rpc.ownMap_keys_mono {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V]
    [go.IntoValInj K] (k1 k2 : MapKeys K) (h : ∀ k, k1.keyOk k → k2.keyOk k) (mp : Loc)
    (dq : DFrac) (m : GMap K V) :
    (letI := k1; (mp ↦${dq} m : IProp GF)) ⊢ (letI := k2; (mp ↦${dq} m : IProp GF)) := by
  try simp only []
  rw [ownMap_unseal]
  unfold ownMapDef
  simp only [named]
  iintro ⟨%mv, %ps, Hown, %Hrepr⟩
  iexists mv, ps
  iframe Hown
  ipureintro
  obtain ⟨h1, h2, h3, h4⟩ := Hrepr
  exact ⟨h1, h2, fun p hp => h _ (h3 p hp), h4⟩

attribute [local instance 1100] v3rpc.errKeys in
/-- `m[k]` of a read-only map owned at `v3rpc.errKeys`, for an `errKeyOk` key. -/
theorem v3rpc.wp_errMap_lookup2_at (mp : Loc) (M : GMap GoInterface GoInterface) (k : GoInterface)
    (hk : errKeyOk k) :
    {{ (mp ↦$□ M : IProp GF) }}
      (App (App (Val (map.lookup2 go.error go.error)) (Val #mp)) (Val #k))
    {{ RET (PairV #((M !! k).getD (zero_val GoInterface)) #(decide ((M !! k).isSome)));
      mp ↦$□ M }} := by
  haveI := v3rpc.safeMapKey_errKeys (GF := GF) k hk
  iintro %Φ #Hm HΦ
  wp_apply (wp_map_lookup2 go.error go.error mp M k DFrac.discard) $$ Hm as #Hm2
  iapply HΦ
  iexact Hm2

/-- **`m[k]` (`v, ok := m[k]`) of a read-only `map[error]error` owned at Perennial's interface keys,
for an `errKeyOk` key** (`togRPCError`'s lookup; its keys are `nil` or pointers, so `errKeyOk`
ones). -/
theorem v3rpc.wp_errMap_lookup2 (mp : Loc) (M : GMap GoInterface GoInterface) (k : GoInterface)
    (hk : errKeyOk k) :
    {{ (mp ↦$□ M : IProp GF) }}
      (App (App (Val (map.lookup2 go.error go.error)) (Val #mp)) (Val #k))
    {{ RET (PairV #((M !! k).getD (zero_val GoInterface)) #(decide ((M !! k).isSome)));
      mp ↦$□ M }} := by
  iintro %Φ #Hm HΦ
  ihave #Hm' := v3rpc.ownMap_keys_mono (GF := GF) (V := GoInterface) mapKeys_interface
    v3rpc.errKeys (fun k h => by
      rcases h with h | ⟨t, l, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨t, l, h⟩)) mp DFrac.discard M $$ Hm
  wp_apply (v3rpc.wp_errMap_lookup2_at (GF := GF) mp M k hk) $$ Hm' as -
  iapply HΦ
  iexact Hm

end proofs

end EtcdGrove
end Perennial
