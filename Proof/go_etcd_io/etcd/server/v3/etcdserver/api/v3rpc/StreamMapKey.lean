/-
**The leader monitor's map keys** (k8s 7f-4, step 4; `notes/k8s-7f4-draft.md` §6 R1,
`notes/k8s-7f4-mapkey-check.lean.txt`). Lean-first.

`newStreamInterceptor`'s require-leader branch inserts `ss = serverStreamWithCtx{ctx, ss}` into
`smap.streams` (a `map[grpc.ServerStream]struct{}`): an interface holding a struct of the raw
stream (a pointer, `rawStreamKeyTy`, T-c) and the `*cancellableContext`. Perennial's default
interface keys (`mapKeys_interface`) are nil and pointers only, and invite a proof that needs other
keys to give its own instance: `v3rpc.streamKeys` (the keys `v3rpc.sKey t ls l`), with
`v3rpc.safeMapKey_sKey`, from `==`'s reduction (`v3rpc.sKey_eq`: the dynamic types, then the
struct's fields, then the pointers). A map of these keys is owned with this instance only.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota
public import Proof.google_golang_org.grpc.InvGrpcStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode

section names
variable [GooseExts] [GoGlobalContext]

/-- **A leader-monitor map key**: the `serverStreamWithCtx` whose raw stream is the pointer
`ls` of type `*t` and whose context is the `*cancellableContext` `l`, as a `grpc.ServerStream`. -/
abbrev v3rpc.sKey (t : go.GoType) (ls l : Loc) : GoInterface :=
  interface.mkOk go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverStreamWithCtx.ty
    #(go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverStreamWithCtx.mk
      (interface.mkOk (go.PointerType t) #ls) l)

/-- **The leader monitor's map keys** (a local `MapKeys` instance, not a global one): the
`v3rpc.sKey`s. -/
@[instance_reducible] def v3rpc.streamKeys : MapKeys GoInterface :=
  ⟨fun k => ∃ (t : go.GoType) (ls l : Loc), k = v3rpc.sKey t ls l⟩

end names

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [gsem : google_golang_org.grpc.Assumptions]
variable [vsem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- Two values with a field's deterministic projection have equal projections (as
`examples/k8s/etcd3/MDefs.lean`'s). -/
private theorem proj_eq' {t : Tag} {f : GoInstruction} {a b : val} {ea eb : Expr}
    (ha : go.IsGoStepPureDetTagged t f a ea) (hb : go.IsGoStepPureDetTagged t f b eb)
    (h : a = b) : ea = eb := by
  have h1 := ha.isGoStep_det_internal.isGoStep_pure_det
  have h2 := hb.isGoStep_det_internal.isGoStep_pure_det
  subst h
  rw [h2] at h1
  exact cast (congrFun h1 eb) rfl

omit gsem in
include vsem in
/-- The injectivity of `serverStreamWithCtx`'s values (its two fields' projections). -/
theorem v3rpc.serverStreamWithCtx_intoVal_inj :
    Function.Injective
      (intoVal (V := go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverStreamWithCtx)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (V := GoInterface) (Expr.Val.inj (proj_eq'
    (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverStreamWithCtx.TypeAssumptions.get_ServerStream x)
    (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverStreamWithCtx.TypeAssumptions.get_ServerStream y) h))
  have := GoGlobalContext.intoVal_inj_loc (Expr.Val.inj (proj_eq'
    (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverStreamWithCtx.TypeAssumptions.get_ctx x)
    (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverStreamWithCtx.TypeAssumptions.get_ctx y) h))
  cases x; cases y; simp_all

/-- **`==` on two monitor keys is equality.** -/
theorem v3rpc.sKey_eq (t t' : go.GoType) (ls ls' l l' : Loc) (s : Stuckness) (E : CoPset)
    (Φ : val → IProp GF) :
    Φ #(decide (v3rpc.sKey t ls l = v3rpc.sKey t' ls' l')) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals google_golang_org.grpc.ServerStream.ty)))
        (Val (PairV #(v3rpc.sKey t ls l) #(v3rpc.sKey t' ls' l')))) @ s; E {{ Φ }} := by
  have hinj := v3rpc.serverStreamWithCtx_intoVal_inj (GF := GF)
  iintro HΦ
  wp_pures
  by_cases ht : go.PointerType t = go.PointerType t'
  · rw [ite_eq_left ht]
    have ht' : t = t' := by simpa using ht
    subst ht'
    wp_pures
    by_cases hl : ls = ls'
    · subst hl
      rw [show decide (ls = ls) = true by simp]
      wp_pures
      by_cases hc : l = l'
      · subst hc
        rw [show decide (l = l) = true by simp]
        rw [show decide (v3rpc.sKey t ls l = v3rpc.sKey t ls l) = true by simp]
        iexact HΦ
      · rw [show decide (l = l') = false by simp [hc]]
        have hk : decide (v3rpc.sKey t ls l = v3rpc.sKey t ls l') = false := by
          simp only [v3rpc.sKey, interface.mkOk, decide_eq_false_iff_not]
          intro h
          simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at h
          have := hinj h
          simp at this
          exact hc this
        rw [hk]; iexact HΦ
    · rw [show decide (ls = ls') = false by simp [hl]]
      wp_pures
      have hk : decide (v3rpc.sKey t ls l = v3rpc.sKey t ls' l') = false := by
        simp only [v3rpc.sKey, interface.mkOk, decide_eq_false_iff_not]
        intro h
        simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at h
        have := hinj h
        simp only [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverStreamWithCtx.mk.injEq,
          GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at this
        exact hl (GoGlobalContext.intoVal_inj_loc this.1)
      rw [hk]; iexact HΦ
  · rw [ite_eq_right ht]
    wp_pures
    have hk : decide (v3rpc.sKey t ls l = v3rpc.sKey t' ls' l') = false := by
      simp only [v3rpc.sKey, interface.mkOk, decide_eq_false_iff_not]
      intro h
      simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at h
      have := hinj h
      simp only [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverStreamWithCtx.mk.injEq,
        GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at this
      exact ht this.1.1
    rw [hk]; iexact HΦ

attribute [local instance 1100] v3rpc.streamKeys in
/-- **A monitor key is a safe map key** under `v3rpc.streamKeys` (a file that owns the monitor's
map makes `v3rpc.streamKeys` a local instance of higher priority than `mapKeys_interface`). -/
instance v3rpc.safeMapKey_sKey (t : go.GoType) (ls l : Loc) :
    SafeMapKey (GF := GF) google_golang_org.grpc.ServerStream.ty
      (v3rpc.sKey t ls l) where
  key_ok := ⟨t, ls, l, rfl⟩
  wp_go_eq_map_key k' hk' s E Φ := by
    obtain ⟨t', ls', l', rfl⟩ := hk'
    exact v3rpc.sKey_eq t t' ls ls' l l' s E Φ

end proofs

end EtcdGrove
end Perennial
