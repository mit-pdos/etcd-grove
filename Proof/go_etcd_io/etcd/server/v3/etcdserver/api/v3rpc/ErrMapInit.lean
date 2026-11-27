/-
**Building `togRPCError`'s error map** (grpcerrmap, 2026-11-26). Lean-first.

`toGRPCErrorMap = map[error]error{...}` (`util.go:35-93`): fifty-three keys, the server's error
variables (membership's, `etcdserver/errors`', mvcc's, `version`'s, lease's, auth's and `context`'s),
each mapped to one of `rpctypes`' errors. The package initializer (translated since grpcerrmap; until
then the trust-boundary axiom `toGRPCErrorMap_init`, whose post was unsatisfiable: it owned the map at
Perennial's interface keys, `nil` and pointers, but said `context.DeadlineExceeded`'s
`deadlineExceededError{}` is a key, `notes/axiom-review/togrpcerrormap-keys.md`) loads them and
inserts them in order. `v3rpc.errMapInv` is the map while it is built, at `v3rpc.errKeys`:
`grpcErrMapOk`'s per-entry facts, every value one grpc's `status` accepts, and every variable inserted
so far a key; `v3rpc.wp_errMapInsert` inserts one entry, `v3rpc.errMap_done` gives the package fact's
pieces (`grpcErrMap`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ErrMapKey
public import Proof.errors.NewVar
public import Proof.errors.NewVarCell

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`X` holds a key of the error map with description `m`** (persistent): an `errKeyOk` error. -/
abbrev v3rpc.errMapKeyVar (X m : GoString) : IProp GF :=
  iprop(∃ k : GoInterface, globalAddr X ↦□ k ∗ ⌜errKeyOk k⌝ ∗ go_etcd_io.etcd.cache.v3.descIs k m)

/-- **The error map while the initializer builds it**, after inserting the variables `G`: owned at
`v3rpc.errKeys` (its keys are `errKeyOk` errors, `context.DeadlineExceeded`'s struct among them), its
values non-nil errors grpc's `status` accepts, each entry as `grpcErrMapOk` says (at mvcc's two read
errors `kf` and `kc`), and the value of each variable of `G` a key. -/
abbrev v3rpc.errMapInv (mref : Loc) (M : GMap GoInterface GoInterface) (kf kc : GoInterface)
    (G : List GoString) : IProp GF :=
  iprop((letI := v3rpc.errKeys; (mref ↦$ M : IProp GF)) ∗
    ⌜∀ k v, M !! k = some v → v ≠ GoInterface.nil⌝ ∗
    (□ ∀ (k v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.statusErrOk v) ∗
    (□ ∀ (k v : GoInterface), ⌜M !! k = some v⌝ →
      (∃ mv : GoString, go_etcd_io.etcd.cache.v3.descIs v mv ∗
        ⌜(mv = go_etcd_io.etcd.cache.v3.futureRevDesc → k = kf) ∧
          (mv = go_etcd_io.etcd.cache.v3.compactedDesc → k = kc)⌝) ∗
      (∃ mk : GoString, go_etcd_io.etcd.cache.v3.descIs k mk ∗
        ⌜mk ≠ go_etcd_io.etcd.cache.v3.futureRevDesc ∧ mk ≠ go_etcd_io.etcd.cache.v3.compactedDesc⌝)) ∗
    (□ ∀ (g : GoString) (k : GoInterface), ⌜g ∈ G⌝ → globalAddr g ↦□ k -∗ ⌜(M !! k).isSome⌝))

omit sem in
/-- A lookup in `<[k := v]> m` finds `v` at `k`, or one of `m`'s entries. -/
theorem v3rpc.lookup_insert_some {K V : Type} [DecidableEq K] {m : GMap K V} {k k' : K}
    {v w : V} (h : (<[k := v]> m) !! k' = some w) : (k = k' ∧ v = w) ∨ m !! k' = some w :=
  ((GMap.lookup_insert_Some m k k' v w).1 h).imp id And.right

omit sem in
/-- A key of `<[k := v]> m`: `k`, or one of `m`'s. -/
theorem v3rpc.lookup_insert_isSome {K V : Type} [DecidableEq K] (m : GMap K V) (k k' : K)
    (v : V) (h : k = k' ∨ (m !! k').isSome) : ((<[k := v]> m) !! k').isSome :=
  (GMap.lookup_insert_is_Some m k k' v).2 (by by_cases hk : k = k' <;> simp_all)

attribute [local instance 1100] v3rpc.errKeys in
/-- **The map literal's `make`**: an empty map, no variable inserted. -/
theorem v3rpc.wp_errMap_make (kf kc : GoInterface) :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make1 [go.MapType go.error go.error])) (Val #()))
    {{ (mref : Loc), RET #mref; v3rpc.errMapInv mref ∅ kf kc
      (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrKeyGlobals.take 0) }} := by
  iintro %Φ - HΦ
  wp_apply (wp_map_make1 (GF := GF) (K := GoInterface) (V := GoInterface) go.error go.error) as %mref Hm
  iapply HΦ
  unfold EtcdGrove.v3rpc.errMapInv
  iframe Hm
  isplitr
  · ipureintro; intro k v h; simp at h
  isplitr
  · iintro !> %k %v %h; simp at h
  isplitr
  · iintro !> %k %v %h; simp at h
  · iintro !> %g %k %h; simp at h

attribute [local instance 1100] v3rpc.errKeys in
/-- **Inserting an entry of the literal**: the value `e` of the variable `X`, a key `k` with a
description `mk` neither read error's, mapped to an error grpc's `status` accepts with a
description `mv` that is a read error's only for that read error's own key. -/
theorem v3rpc.wp_errMapInsert [bc_sem : _root_.Perennial.golang_org.x.crypto.bcrypt.Assumptions]
    [ctx_sem : _root_.Perennial.context.Assumptions]
    [impl_sem : google_golang_org.protobuf.internal.impl.Assumptions]
    (mref : Loc) (M : GMap GoInterface GoInterface)
    (kf kc : GoInterface) (n : Nat) (X : GoString) (k : GoInterface) (e : GoInterfaceOk)
    (mk mv : GoString)
    (hX : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrKeyGlobals[n]? = some X) (hk : errKeyOk k)
    (hmk : mk ≠ go_etcd_io.etcd.cache.v3.futureRevDesc ∧ mk ≠ go_etcd_io.etcd.cache.v3.compactedDesc)
    (hmv : (mv = go_etcd_io.etcd.cache.v3.futureRevDesc → k = kf) ∧
      (mv = go_etcd_io.etcd.cache.v3.compactedDesc → k = kc)) :
    {{ v3rpc.errMapInv (GF := GF) mref M kf kc
        (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrKeyGlobals.take n) ∗ globalAddr X ↦□ k ∗ go_etcd_io.etcd.cache.v3.descIs k mk ∗
        go_etcd_io.etcd.cache.v3.statusErrOk (GoInterface.ok e) ∗
        go_etcd_io.etcd.cache.v3.descIs (GoInterface.ok e) mv }}
      (App (App (App (Val (map.insert go.error)) (Val #mref)) (Val #k)) (Val #(GoInterface.ok e)))
    {{ RET #(); v3rpc.errMapInv mref (<[k := GoInterface.ok e]> M) kf kc
        (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrKeyGlobals.take (n + 1)) }} := by
  haveI := v3rpc.safeMapKey_errKeys (GF := GF) k hk
  wp_start_folded as ⟨⟨Hm, %HN, #HS, #HO, #HK⟩, #HX, #Hdk, #Hs, #Hdv⟩
  wp_apply (wp_mapInsert (GF := GF) (K := GoInterface) (V := GoInterface) go.error) $$ Hm as Hm
  iapply HΦ
  unfold EtcdGrove.v3rpc.errMapInv
  iframe Hm
  isplitr
  · ipureintro
    intro k' v' h
    rcases v3rpc.lookup_insert_some h with ⟨-, rfl⟩ | h
    · exact nofun
    · exact HN k' v' h
  isplitr
  · iintro !> %k' %v' %h
    rcases v3rpc.lookup_insert_some h with ⟨-, rfl⟩ | h
    · iexact Hs
    · iapply HS; ipureintro; exact h
  isplitr
  · iintro !> %k' %v' %h
    rcases v3rpc.lookup_insert_some h with ⟨rfl, rfl⟩ | h
    · isplitl
      · iexists mv; iframe Hdv; ipureintro; exact hmv
      · iexists mk; iframe Hdk; ipureintro; exact hmk
    · iapply HO; ipureintro; exact h
  · iintro !> %g %k' %hg Hk'
    rw [List.take_succ, hX] at hg
    rcases List.mem_append.1 hg with hg | hg
    · ihave %h := HK $$ %g %k' %hg Hk'
      ipureintro
      exact v3rpc.lookup_insert_isSome _ _ _ _ (Or.inr h)
    · simp only [Option.toList_some, List.mem_singleton] at hg
      subst hg
      icombine HX Hk' gives %Heq
      ipureintro
      exact v3rpc.lookup_insert_isSome _ _ _ _ (Or.inl Heq)

/-- **The built map**: the package fact's pieces (`grpcErrMap`), once every variable of
`grpcErrKeyGlobals` is inserted. -/
theorem v3rpc.errMap_done (mref : Loc) (M : GMap GoInterface GoInterface) (kf kc : GoInterface)
    (n : Nat) (hn : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrKeyGlobals.length ≤ n) :
    v3rpc.errMapInv (GF := GF) mref M kf kc
      (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrKeyGlobals.take n) ⊢
      globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev ↦□ kf -∗
      globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□ kc -∗
    (letI := v3rpc.errKeys; (mref ↦$ M : IProp GF)) ∗
      (□ ∀ (k v : GoInterface), ⌜M !! k = some v⌝ → go_etcd_io.etcd.cache.v3.statusErrOk v) ∗
      (□ ∀ (g : GoString) (k : GoInterface),
        ⌜g ∈ go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrKeyGlobals⌝ →
        globalAddr g ↦□ k -∗ ⌜(M !! k).isSome⌝) ∗
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrMapOk M kf kc := by
  rw [List.take_of_length_le hn]
  iintro ⟨Hm, %HN, #HS, #HO, #HK⟩ #HF #HC
  ihave %hf := HK $$ %_ %kf %(by
    unfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrKeyGlobals
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) HF
  ihave %hc := HK $$ %_ %kc %(by
    unfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrKeyGlobals
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail)) HC
  iframe Hm HS HK
  unfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.grpcErrMapOk
  isplitr
  · ipureintro; exact ⟨HN, hf, hc⟩
  · iexact HO

/-- `Error()` of the `*errorString` at `x` whose `s` field holds `msg` returns `msg`. -/
theorem v3rpc.errStrCell_msg [_root_.Perennial.errors.Assumptions] (x : Loc) (msg : GoString) :
    errStrCell (GF := GF) x msg ⊢
      □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
          go!"Error" #x)) (Val #())) {{ Φ }} := by
  unfold errStrCell
  iintro #Hs !> %Φ HΦ
  rw [method_unfold]
  wp_auto
  iexact HΦ

/-- **An `errors.New` error is a key with its message as description.** -/
theorem v3rpc.keyVar_of_msg [_root_.Perennial.errors.Assumptions] (X : GoString) (x : Loc) (msg : GoString) :
    globalAddr X ↦□ interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x ∗
      (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
          go!"Error" #x)) (Val #())) {{ Φ }}) ⊢ v3rpc.errMapKeyVar X msg := by
  iintro ⟨#HX, #Hm⟩
  iexists _
  iframe HX
  isplitr
  · ipureintro; exact Or.inr (Or.inl ⟨_, x, rfl⟩)
  iapply (go_etcd_io.etcd.cache.v3.descIs_of_msg
    ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ msg
    (go_etcd_io.etcd.cache.v3.ptrTy_ne_etcdError _))
  · have := go.method_set_is (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
      go!"GRPCStatus"
    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at this
    simp [this]
  unfold go_etcd_io.etcd.cache.v3.errorMsgIs
  iexact Hm

/-- An `errorsNewVar` variable holds a key with its message as description. -/
theorem v3rpc.keyVar_of_newVar [_root_.Perennial.errors.Assumptions] (X msg : GoString) :
    errorsNewVar (GF := GF) X msg ⊢ v3rpc.errMapKeyVar X msg := by
  unfold errorsNewVar
  iintro ⟨%x, #HX, #Hm⟩
  iapply v3rpc.keyVar_of_msg X x msg
  iframe HX Hm

/-- An `errVarCell` variable holds a key with its message as description. -/
theorem v3rpc.keyVar_of_cell [_root_.Perennial.errors.Assumptions] (X msg : GoString) :
    errVarCell (GF := GF) X msg ⊢ v3rpc.errMapKeyVar X msg := by
  unfold errVarCell
  iintro ⟨%x, #HX, #Hc⟩
  ihave #Hm := v3rpc.errStrCell_msg x msg $$ Hc
  iapply v3rpc.keyVar_of_msg X x msg
  iframe HX Hm

/-- **`context.DeadlineExceeded`'s `deadlineExceededError{}` is a key** with description
`"context deadline exceeded"`. -/
theorem v3rpc.keyVar_deadline [_root_.Perennial.context.Assumptions] :
    globalAddr _root_.Perennial.context.DeadlineExceeded ↦□
        interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
          #(zero_val _root_.Perennial.context.deadlineExceededError) ⊢
      v3rpc.errMapKeyVar (GF := GF) _root_.Perennial.context.DeadlineExceeded
        go!"context deadline exceeded" := by
  iintro #HX
  iexists _
  iframe HX
  isplitr
  · ipureintro; exact Or.inr (Or.inr (Or.inl rfl))
  iapply go_etcd_io.etcd.cache.v3.descIs_deadlineZero

end proofs

end EtcdGrove
end Perennial
