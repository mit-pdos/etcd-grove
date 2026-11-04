/-
**Placeholders of the M1 migration** (strict M1, 2026-11-04: `notes/decisions.md`, "strict M1, no
scaffold"). Lean-first (no Rocq counterpart).

The store's locks hold the API's ghost state outright (`InvStore`'s slots at `StoreNames.api`).
Today's specs of the methods that move it (`storeTxnWrite.End`, `store.updateCompactRev`,
`store.Write`'s checkout) give their callers none of the client's parts, so their proofs cannot
take the API's steps; each such step is one of the lemmas below, **false in general** and proved
by `sorry`, marked `M1-REPLACE` with the API contract whose proof replaces it at stage 2 (the
proofs using them are rewritten against the API's contracts, and this module goes). Nothing new
may use them.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI

section placeholders
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **(Placeholder, false in general.)** The lock's slot moved to a new log and compaction
revision without the client's half of the view. M1-REPLACE: `KV.Put`/`KV.DeleteRange`/
`Txn.End.contract`'s bump (the client's update) and `KV.Compact.contract`. -/
theorem slotX_step_M1 {γ : StoreNames} {q : Qp} {L : Log} {c : Int} (L' : Log) (c' : Int) :
    slotX (GF := GF) γ q L c ⊢ slotX γ q L' c' := by
  sorry -- M1-REPLACE: Txn.End.contract (bump), KV.Compact.contract

/-- **(Placeholder, false in general.)** The writer's slot made from nothing. M1-REPLACE:
`Txn.End.contract` (the writer's slot carried from `Write` to `End`, stage 1's step 3). -/
theorem slotY_make_M1 (γ : StoreNames) (L : Log) : ⊢ slotY (GF := GF) γ L := by
  sorry -- M1-REPLACE: Txn.End.contract (the writer's slot from Write)

/-- **(Placeholder, false in general.)** The frozen state excluded without a share of the token.
M1-REPLACE: `KV.Write.contract`, `Txn.End.contract` (the writer's backend share,
`mvccBackend γ q`, excludes it: `slotF_share_excl`). -/
theorem slotF_excl_M1 (γ : StoreNames) : slotF (GF := GF) γ ∗ iprop(emp) ⊢ False := by
  sorry -- M1-REPLACE: KV.Write.contract, Txn.End.contract (the backend share)

end placeholders

end mvcc
end EtcdGrove
end Perennial
