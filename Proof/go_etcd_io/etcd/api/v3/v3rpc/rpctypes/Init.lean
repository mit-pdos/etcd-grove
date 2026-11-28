/-
Package initialization of `go_etcd_io.etcd.api.v3.v3rpc.rpctypes`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`rpctypesInit`, `cache/v3/Base.lean`): the errors `ErrFutureRev`, `ErrCompacted`
(`EtcdError`s, whose `Error()` returns), the map `errStringToError` (its values `status.Error`
errors grpc's `status` accepts), `EtcdError`'s method set (`EtcdGrove.RpctypesEtcdErrorMethods`, of
the method set goose emits), the `EtcdError`s `ErrUserEmpty`, `ErrInvalidAuthToken`,
`ErrAuthOldRevision`, `ErrNoLeader`, `ErrAuthNotEnabled` and the pointer error `ErrGRPCNotSupportedForLearner`, the token keys, the `ErrGRPC*` errors
`v3rpc`'s checks and interceptors return and its metadata keys, and (D19j) the `ErrGRPC*` errors its
watch server returns, whose `Error()` returns. (prove-rpcmap, 2026-11-20) Its
variables' initializers (`error.go`, `md.go`, `metadatafields.go`) are all translated: the
`status.Error` errors, the map literal `errStringToError` (keys `ErrorDesc(ErrGRPC*)`) and the
client-side `Err* = Error(ErrGRPC*)` (`Error.wp_initErr`); until then the trust-boundary axioms
`opaqueInitsOk`, `errStringToError_init` and `<X>_init` for the errors the fact reads.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.grpc.codes.Init
public import Proof.google_golang_org.grpc.status.Init
public import Perennial.Golang.Theory.TypeSet

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- **The method set of `rpctypes.EtcdError`** is `{Code, Error}` (`error.go`): no `As`,
`Unwrap`, `GRPCStatus` or `Is` method: a theorem of the method set goose emits
(`EtcdError.TypeAssumptions.method_set`), as `EtcdGrove.ErrorStringLeaf`. -/
class EtcdGrove.RpctypesEtcdErrorMethods [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] : Prop where
  leaf : ∀ v : val, errors.isLeafError ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, v⟩
  noGRPCStatus : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"GRPCStatus" = none
  noIs : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Is" = none
  /-- (premise-fixes-4) nor a `Format` method (`fmt` prints it with its `Error`). -/
  noFormat : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Format" = none
  /-- (fmt soundness 2) and its `Error` is `Error() string` (what `fmt.argOk` asks). -/
  errorSig : methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Error" =
    some (go.signature.Signature [] false [go.string])

instance EtcdGrove.rpctypesEtcdErrorMethods_inst [GooseExts] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] [_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] :
    EtcdGrove.RpctypesEtcdErrorMethods := by
  have h := fun m => go.method_set_is (t := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) m
  have hAs := h go!"As"; have hU := h go!"Unwrap"; have hG := h go!"GRPCStatus"; have hIs := h go!"Is"
  have hF := h go!"Format"; have hE := h go!"Error"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hAs hU hG hIs hF hE
  exact ⟨fun _ => by simp [errors.isLeafError, hAs, hU], hG, hIs, hF, hE⟩

/-- `rpctypes.EtcdError` implements `error` (its `Error` has a value receiver): a target
`errors.As` accepts. -/
theorem EtcdGrove.rpctypesEtcdError_asTarget [GooseExts] [GoGlobalContext] [GoLocalContext]
    [sem : go.Semantics] [_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] :
    errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty :=
  Or.inr (by go_type_set)

section rpcmap
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- (prove-rpcmap) A lookup in `<[k := v]> m` finds `v` at `k`, or one of `m`'s entries. -/
theorem EtcdGrove.rpctypes_lookup_insert_some {K V : Type} [DecidableEq K] {m : GMap K V} {k k' : K}
    {v w : V} (h : (<[k := v]> m) !! k' = some w) : (k = k' ∧ v = w) ∨ m !! k' = some w :=
  ((GMap.lookup_insert_Some m k k' v w).1 h).imp id And.right

/-- (prove-rpcmap) A key of `<[k := v]> m`: `k`, or one of `m`'s. -/
theorem EtcdGrove.rpctypes_lookup_insert_isSome {K V : Type} [DecidableEq K] (m : GMap K V) (k k' : K)
    (v : V) (h : k = k' ∨ (m !! k').isSome) : ((<[k := v]> m) !! k').isSome :=
  (GMap.lookup_insert_is_Some m k k' v).2 (by by_cases hk : k = k' <;> simp_all)

/-- (prove-rpcmap) The map literal `errStringToError` while `rpctypes`' initializer builds it: its
values are errors grpc's `status` accepts, each under its description (`rpctypesInit`'s map). -/
abbrev EtcdGrove.rpctypesErrMapInv (mref : Loc) (M : GMap GoString GoInterface) : IProp GF :=
  iprop(mref ↦$ M ∗
    (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.statusErrOk v) ∗
    (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.descIs v k))

theorem EtcdGrove.rpctypes_errMapInv_elim (mref : Loc) (M : GMap GoString GoInterface) :
    (EtcdGrove.rpctypesErrMapInv mref M : IProp GF) ⊢ mref ↦$ M ∗
      (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.statusErrOk v) ∗
      (□ ∀ (k : GoString) (v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.descIs v k) := by
  iintro H; iexact H

theorem EtcdGrove.rpctypes_errMapInv_empty (mref : Loc) :
    (mref ↦$ (∅ : GMap GoString GoInterface) : IProp GF) ⊢ EtcdGrove.rpctypesErrMapInv mref ∅ := by
  iintro Hm
  unfold EtcdGrove.rpctypesErrMapInv
  iframe Hm
  isplitr
  · iintro !> %k %v %h; simp at h
  · iintro !> %k %v %h; simp at h

/-- (prove-rpcmap) Inserting an error grpc's `status` accepts under its description. -/
theorem EtcdGrove.rpctypes_wp_errMapInsert (mref : Loc) (M : GMap GoString GoInterface) (e : GoInterfaceOk)
    (d : GoString) :
    {{ (EtcdGrove.rpctypesErrMapInv mref M : IProp GF) ∗ go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗
        go_etcd_io.etcd.cache.v3.descIs (GoInterface.ok e) d }}
      (App (App (App (Val (map.insert go.string)) (Val #mref))
        (Val #d)) (Val #(GoInterface.ok e)))
    {{ RET #(); EtcdGrove.rpctypesErrMapInv mref (<[d := GoInterface.ok e]> M) }} := by
  wp_start_folded as ⟨Hinv, #Hok, #Hd⟩
  ihave ⟨Hm, #HS, #HD⟩ := EtcdGrove.rpctypes_errMapInv_elim _ _ $$ Hinv
  wp_apply (wp_mapInsert (K := GoString) (V := GoInterface) go.string) $$ Hm as Hm
  iapply HΦ
  unfold EtcdGrove.rpctypesErrMapInv
  iframe Hm
  isplitr
  · iintro !> %k %v %h
    rcases EtcdGrove.rpctypes_lookup_insert_some h with ⟨-, rfl⟩ | h
    · iexact Hok
    · iapply HS; ipureintro; exact h
  · iintro !> %k %v %h
    rcases EtcdGrove.rpctypes_lookup_insert_some h with ⟨rfl, rfl⟩ | h
    · iexact Hd
    · iapply HD; ipureintro; exact h

end rpcmap

end Perennial
