/-
**The laws of the SMD API's vocabulary** that its clients need (`notes/smd-plan.md`, "Laws"),
stated, not proved: each is a `def <name>.law : Prop`, proved after the freeze by
`<name>_law_holds` (a linking module passes it to the proofs that take it, CLAUDE.md "Import
tiers"). A client never unfolds a representation predicate: it uses these.

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## Persistence (every representation predicate but `freshSchema`) -/

def isIface_persistent.law : Prop := ∀ i x, isIface (GF := GF) i x ⊢ □ isIface i x
def isVal_persistent.law : Prop := ∀ v x, isVal (GF := GF) v x ⊢ □ isVal v x
def isPE_persistent.law : Prop := ∀ e pe, isPE (GF := GF) e pe ⊢ □ isPE e pe
def isPath_persistent.law : Prop := ∀ s p, isPath (GF := GF) s p ⊢ □ isPath s p
def isSet_persistent.law : Prop := ∀ p S, isSet (GF := GF) p S ⊢ □ isSet p S
def isVSet_persistent.law : Prop := ∀ i e, isVSet (GF := GF) i e ⊢ □ isVSet i e
def isMF_persistent.law : Prop := ∀ m mf, isMF (GF := GF) m mf ⊢ □ isMF m mf
def isSchema_persistent.law : Prop := ∀ sc S, isSchema (GF := GF) sc S ⊢ □ isSchema sc S
def isTypeRef_persistent.law : Prop := ∀ tr t, isTypeRef (GF := GF) tr t ⊢ □ isTypeRef tr t
def isTV_persistent.law : Prop := ∀ p sc S t x, isTV (GF := GF) p sc S t x ⊢ □ isTV p sc S t x
def isConflicts_persistent.law : Prop := ∀ s cs, isConflicts (GF := GF) s cs ⊢ □ isConflicts s cs
def isIdentityConverter_persistent.law : Prop :=
  ∀ cv, isIdentityConverter (GF := GF) cv ⊢ □ isIdentityConverter cv

/-- The separating conjunction of `f` over a list. -/
def sepL {α : Type} (f : α → IProp GF) (xs : List α) : IProp GF :=
  xs.foldr (fun a acc => iprop(f a ∗ acc)) iprop(True)

/-! ## Introduction (a client's literals) -/

/-- A schema literal becomes a shared schema (its lazy indexes put under their onces). -/
def isSchema_intro.law : Prop :=
  ∀ sc S, freshSchema (GF := GF) sc S ⊢ |={⊤}=> isSchema sc S

/-- Scalars. -/
def isIface_scalar.law : Prop :=
  (iprop(True) ⊢ isIface (GF := GF) interface.nil .null) ∧
  (∀ b, iprop(True) ⊢ isIface (GF := GF) (interface.mkOk go.bool #b) (.bool b)) ∧
  (∀ n, iprop(True) ⊢ isIface (GF := GF) (interface.mkOk go.int64 #n) (.int n)) ∧
  (∀ s, iprop(True) ⊢ isIface (GF := GF) (interface.mkOk go.string #s) (.str s))

/-- A `[]interface{}` literal, read-only. -/
def isIface_list.law : Prop :=
  ∀ (sl : GoSlice) (xs : List GoInterface) (vs : List UVal), xs.length = vs.length →
    sl ↦*{DFrac.discard} xs -∗ sepL (fun xv => isIface (GF := GF) xv.1 xv.2) (xs.zip vs) -∗
    isIface (interface.mkOk sliceIfaceTy #sl) (.list vs)

/-- A `map[string]interface{}` literal, read-only, its entries `kvs` sorted. -/
def isIface_map.law : Prop :=
  ∀ (m : GoMap) (M : GMap GoString GoInterface) (kvs : List (GoString × UVal)),
    keysSorted kvs = true → (∀ k, (M !! k).isSome = (lookupKV k kvs).isSome) →
    m ↦$□ M -∗ sepL (fun kv => iprop(∃ x, ⌜M !! kv.1 = some x⌝ ∗ isIface (GF := GF) x kv.2)) kvs -∗
    isIface (interface.mkOk mapStrIfaceTy #m) (.map kvs)

/-- A `ManagedFields` literal, read-only. -/
def isMF_intro.law : Prop :=
  ∀ (m : fieldpath.ManagedFields) (M : GMap GoString GoInterface) (ms : List (GoString × VSet)),
    (ms.map (·.1)).Nodup → (∀ k, (M !! k).isSome ↔ k ∈ ms.map (·.1)) →
    m ↦$□ M -∗ sepL (fun me => iprop(∃ i, ⌜M !! me.1 = some i⌝ ∗ isVSet (GF := GF) i me.2)) ms -∗
    isMF m (fun k => lookupKV k ms)

/-- A `[]Conflict` literal, read-only. -/
def isConflicts_intro.law : Prop :=
  ∀ (s : merge.Conflicts) (xs : List merge.Conflict) (cs : List (GoString × Path)),
    xs.length = cs.length →
    s ↦*{DFrac.discard} xs -∗
    sepL (fun xc => iprop(⌜xc.1.Manager' = xc.2.1⌝ ∗ isPath (GF := GF) xc.1.Path' xc.2.2)) (xs.zip cs) -∗
    isConflicts s cs

/-! ## Elimination -/

/-- A typed value conforms to its type. -/
def isTV_conforms.law : Prop :=
  ∀ p sc S t x, isTV (GF := GF) p sc S t x ⊢ ⌜conforms S t x⌝

end laws

/-! ## Pure laws -/

/-- A set written at this schema is its own reconciliation. -/
def reconcile_id.law : Prop :=
  ∀ S t s, schemaConsistent S t s → reconcile S t s = s

/-- `Apply` keeps its own premise on the managers: the new managers' sets are at the request's
version and keep items with their key fields (so a client can chain applies). -/
def applyResult_premise.law : Prop :=
  ∀ S t rion live config ver mf mgr force obj mf', S.WF → conforms S t live → conforms S t config →
    (∀ m e, mf m = some e → e.version = ver ∧ keysWithItems S t e.set) →
    applyResult S t rion live config ver mf mgr force = .ok obj mf' →
    (∀ m e, mf' m = some e → e.version = ver ∧ keysWithItems S t e.set ∧ schemaConsistent S t e.set)

/-- `Update` likewise. -/
def updateResult_premise.law : Prop :=
  ∀ S t live new ver mf mgr, S.WF → conforms S t live → conforms S t new →
    (∀ m e, mf m = some e → e.version = ver ∧ keysWithItems S t e.set) →
    (∀ m e, updateResult S t live new ver mf mgr m = some e →
      e.version = ver ∧ keysWithItems S t e.set ∧ schemaConsistent S t e.set)

/-- Merging nothing into a value is the value (a list item only one side has). -/
def mergeF_none.law : Prop :=
  ∀ S t x n, S.WF → conforms S t x → x.size < n → mergeF n S t (some x) none = some x

end smd
end EtcdGrove
end Perennial
