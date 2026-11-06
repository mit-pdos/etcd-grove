/-
**`shapes.law`** (track A, 2026-11-06). Lean-first (no Rocq counterpart). Over the sealed
definitions of `Api.lean` (imported with `import all`).

`shapes.law_holds`: a store's handle, a transaction and a stream are `interface.mkOk ty v` values of
the types the handles record (`isMvcc`: `*store` or `*watchableStore`; `mvccTxn`: `*metricsTxnWrite`,
`*txnReadWrite` or `*watchableStoreTxnWrite`, `roWrap`/`wrWrap`; `isMvccWatchStream`:
`*watchStream`), so the law follows from the bundles at those types (`isKV`, `isWatchableKV`,
`isTxn`, `isWatchStream`: each a conjunction of the canonical specs, which the linking assembles,
as `sync`'s `Mutex_is_Locker`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A read transaction's chain is at `*metricsTxnWrite` or `*txnReadWrite`. -/
theorem roWrap_ty (n : Nat) (t : GoInterface) (mw : Loc) :
    roWrap (GF := GF) n t mw ⊢
      ⌜∃ l : Loc, t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #l ∨
        t = interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #l⌝ := by
  cases n with
  | zero =>
    simp only [roWrap]
    iintro %h
    ipureintro; exact ⟨mw, Or.inl h⟩
  | succ n =>
    simp only [roWrap]
    iintro ⟨%trw, %ty, %v, %h, -⟩
    ipureintro; exact ⟨trw, Or.inr h⟩

/-- A write transaction is at `*metricsTxnWrite` or `*watchableStoreTxnWrite`. -/
theorem wrWrap_ty (t : GoInterface) (γ : StoreNames) (s mw : Loc) (ilog : Log) :
    wrWrap (GF := GF) t γ s mw ilog ⊢
      ⌜∃ l : Loc, t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #l ∨
        t = interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #l⌝ := by
  iintro H
  iunfold wrWrap at H
  icases H with (%h | ⟨%tw, %sw, %γw, %h, -⟩)
  · ipureintro; exact ⟨mw, Or.inl h.1⟩
  · ipureintro; exact ⟨tw, Or.inr h.1⟩

/-- **`shapes.law`**, from the bundles at the handles' types. -/
theorem shapes.law_holds
    (hKVS : ∀ s : Loc, isKV (GF := GF) (go.GoType.PointerType store.ty) #s)
    (hKVW : ∀ s : Loc, isWatchableKV (GF := GF) (go.GoType.PointerType watchableStore.ty) #s)
    (hTM : ∀ t : Loc, isTxn (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #t)
    (hTT : ∀ t : Loc, isTxn (GF := GF) (go.GoType.PointerType watchableStoreTxnWrite.ty) #t)
    (hTR : ∀ t : Loc, isTxn (GF := GF) (go.GoType.PointerType txnReadWrite.ty) #t)
    (hWS : ∀ w : Loc, isWatchStream (GF := GF) (go.GoType.PointerType watchStream.ty) #w) :
    shapes.law (GF := GF) := by
  refine ⟨?_, hKVW, ?_, ?_⟩
  · intro kv γ
    iintro Hmv
    iunfold isMvcc at Hmv
    icases Hmv with #(⟨Hmv, -⟩ | Hmv)
    · iunfold isMvccPlain at Hmv
      icases Hmv with ⟨%s, %Hk, -⟩
      ipureintro; exact ⟨_, _, Hk, hKVS s⟩
    · iunfold isMvccWatchable at Hmv
      icases Hmv with ⟨%s, %st, %γw, %γp, %Hk, -⟩
      ipureintro; exact ⟨_, _, Hk.1, (hKVW s).1⟩
  · intro t γ trace k
    iintro Ht
    iunfold mvccTxn at Ht
    cases k with
    | read σ =>
      simp only [mvccTxnI]
      icases Ht with ⟨%mw, %s, %n, -, -, -, Hw⟩
      ihave %Hty := roWrap_ty n t mw $$ Hw
      obtain ⟨l, hl | hl⟩ := Hty
      · ipureintro; exact ⟨_, _, hl, hTM l⟩
      · ipureintro; exact ⟨_, _, hl, hTR l⟩
    | write σ pend =>
      simp only [mvccTxnI]
      icases Ht with ⟨%mw, %s, %p, %puts, %deletes, %putSize, -, -, -, -, Hw⟩
      ihave %Hty := wrWrap_ty t _ s mw σ.log $$ Hw
      obtain ⟨l, hl | hl⟩ := Hty
      · ipureintro; exact ⟨_, _, hl, hTM l⟩
      · ipureintro; exact ⟨_, _, hl, hTT l⟩
  · intro w γ ι
    iintro Hw
    iunfold isMvccWatchStream at Hw
    icases Hw with ⟨-, #Hw⟩
    iunfold isMvccWatchStreamRest at Hw
    icases Hw with ⟨%γw, %γc, %w', %s, %st, %γo, %γp, %Hk, -⟩
    ipureintro; exact ⟨_, _, Hk.2.2.2, hWS w'⟩

end proof

#print axioms shapes.law_holds

end api
end mvcc
end EtcdGrove
end Perennial
