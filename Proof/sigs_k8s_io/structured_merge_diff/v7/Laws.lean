/-
**The laws of the SMD API's vocabulary** that its clients need (`notes/smd-plan.md`, "Laws"),
stated, not proved: each is a `def <name>.law : Prop`, proved after the freeze by
`<name>_law_holds` (a linking module passes it to the proofs that take it, CLAUDE.md "Import
tiers"). A client never unfolds a representation predicate (they are sealed, `@[no_expose]`): it
uses these.

Round 1 (2026-11-19) added: the fractional `isValF` (split, persistence, agreement); `ownSet`
(persistence, the empty set); persistence of `isFieldList`, `isPaths`, `isUpdater`; the
introduction laws for the driver's literals (`isFieldList`, `isPath`, `isPaths` nil/cons/append,
the schema literal's pieces and `freshSchema`, an `Updater` literal, maps over `UVal.ofMap`,
managed fields over `MF.ofList`); `isTV_schema`; agreement laws; the declarative readings of the
computable `ensureNamed`, `atomicNodes`, `reconcile` and `keysWithItemsB`; extensionality of sets
and managed fields; the chaining laws over the strengthened `keysWithItems`.

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

/-! ## Persistence (every representation predicate but `freshSchema` and `ownSet`) -/

def isIface_persistent.law : Prop := ∀ i x, isIface (GF := GF) i x ⊢ □ isIface i x
def isVal_persistent.law : Prop := ∀ v x, isVal (GF := GF) v x ⊢ □ isVal v x
def isFieldList_persistent.law : Prop := ∀ s fl, isFieldList (GF := GF) s fl ⊢ □ isFieldList s fl
def isPE_persistent.law : Prop := ∀ e pe, isPE (GF := GF) e pe ⊢ □ isPE e pe
def isPath_persistent.law : Prop := ∀ s p, isPath (GF := GF) s p ⊢ □ isPath s p
def isPaths_persistent.law : Prop := ∀ ss ps, isPaths (GF := GF) ss ps ⊢ □ isPaths ss ps
def isSet_persistent.law : Prop := ∀ p S, isSet (GF := GF) p S ⊢ □ isSet p S
def isVSet_persistent.law : Prop := ∀ i e, isVSet (GF := GF) i e ⊢ □ isVSet i e
def isMF_persistent.law : Prop := ∀ m mf, isMF (GF := GF) m mf ⊢ □ isMF m mf
def isSchema_persistent.law : Prop := ∀ sc S, isSchema (GF := GF) sc S ⊢ □ isSchema sc S
def isTypeRef_persistent.law : Prop := ∀ tr t, isTypeRef (GF := GF) tr t ⊢ □ isTypeRef tr t
def isTV_persistent.law : Prop := ∀ p sc S t x, isTV (GF := GF) p sc S t x ⊢ □ isTV p sc S t x
def isConflicts_persistent.law : Prop := ∀ s cs, isConflicts (GF := GF) s cs ⊢ □ isConflicts s cs
def isIdentityConverter_persistent.law : Prop :=
  ∀ cv, isIdentityConverter (GF := GF) cv ⊢ □ isIdentityConverter cv
def isUpdater_persistent.law : Prop :=
  ∀ u cv igf igfl rion, isUpdater (GF := GF) u cv igf igfl rion ⊢ □ isUpdater u cv igf igfl rion

/-- A `ManagedFields` map's model is sorted by manager (review round 2: a client needs it for
`MF_ext` and for the chaining laws' premise). -/
def isMF_sorted.law : Prop := ∀ m mf, isMF (GF := GF) m mf ⊢ ⌜keysSorted mf = true⌝

/-- **Introduction of `isIdentityConverter`** (review round 2: the driver must build it): a
converter value of dynamic type `T` whose `Convert` returns its argument with a nil error and whose
`IsMissingVersionError` returns `false`. -/
def isIdentityConverter_intro.law : Prop :=
  ∀ (T : go.GoType) (v : val),
    (□ (∀ (p : Loc) (ver : fieldpath.APIVersion) (Φ : val → IProp GF),
        ▷ Φ (PairV #p #(interface.nil : GoInterface)) -∗
        WP (App (App (Val #(methods T go!"Convert" v)) (Val #p)) (Val #ver)) {{ Φ }}) ∗
     □ (∀ (e : GoInterface) (Φ : val → IProp GF), ▷ Φ #false -∗
        WP (App (Val #(methods T go!"IsMissingVersionError" v)) (Val #e)) {{ Φ }}))
    ⊢ isIdentityConverter (interface.mkOk T v)

/-! ## Fractions and ownership -/

/-- A lent wrapper splits and recombines (`isValF` is fractional in `dq`). -/
def isValF_split.law : Prop :=
  ∀ v dq1 dq2 x, isValF (GF := GF) v (dq1 • dq2) x ⊣⊢ isValF v dq1 x ∗ isValF v dq2 x

/-- Any share of a wrapper can be given up for good: the persistent `isVal`. -/
def isValF_persist.law : Prop := ∀ v dq x, isValF (GF := GF) v dq x ⊢ |==> isVal v x

/-- A set under construction, finished, is handed out persistently. -/
def ownSet_persist.law : Prop := ∀ p S, ownSet (GF := GF) p S ⊢ |==> isSet p S

/-- `&Set{}`: an owned empty set. -/
def ownSet_empty.law : Prop :=
  ∀ p, p ↦ (zero_val fieldpath.Set') ⊢ ownSet (GF := GF) p PathSet.empty

/-! ## Agreement (two descriptions of one object) -/

def isIface_agree.law : Prop := ∀ i x y, isIface (GF := GF) i x ∗ isIface i y ⊢ ⌜x = y⌝
def isValF_agree.law : Prop :=
  ∀ v dq1 dq2 x y, isValF (GF := GF) v dq1 x ∗ isValF v dq2 y ⊢ ⌜x = y⌝
def isSet_agree.law : Prop := ∀ p S S', isSet (GF := GF) p S ∗ isSet p S' ⊢ ⌜S = S'⌝
def isMF_agree.law : Prop := ∀ m a b, isMF (GF := GF) m a ∗ isMF m b ⊢ ⌜a = b⌝
def isSchema_agree.law : Prop := ∀ sc S S', isSchema (GF := GF) sc S ∗ isSchema sc S' ⊢ ⌜S = S'⌝

/-- The separating conjunction of `f` over a list. -/
def sepL {α : Type} (f : α → IProp GF) (xs : List α) : IProp GF :=
  xs.foldr (fun a acc => iprop(f a ∗ acc)) iprop(True)

/-! ## Introduction (a client's literals) -/

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

/-- A `map[string]interface{}` literal with the entries `kvs` (distinct keys, any order: a Go map
literal's), read-only: its value is `UVal.ofMap kvs`. -/
def isIface_ofMap.law : Prop :=
  ∀ (m : GoMap) (M : GMap GoString GoInterface) (kvs : List (GoString × UVal)),
    (kvs.map (·.1)).Nodup → (∀ k, (M !! k).isSome = (lookupKV k kvs).isSome) →
    m ↦$□ M -∗ sepL (fun kv => iprop(∃ x, ⌜M !! kv.1 = some x⌝ ∗ isIface (GF := GF) x kv.2)) kvs -∗
    isIface (interface.mkOk mapStrIfaceTy #m) (UVal.ofMap kvs)

/-- A `value.FieldList` literal (`[]value.Field{{Name: n, Value: v}, ...}`), read-only. -/
def isFieldList_intro.law : Prop :=
  ∀ (s : GoSlice) (fs : List value.Field) (fl : FieldList), fs.length = fl.length →
    s ↦*{DFrac.discard} fs -∗
    sepL (fun ff => iprop(⌜ff.1.Name' = ff.2.1⌝ ∗ isVal (GF := GF) ff.1.Value' ff.2.2)) (fs.zip fl) -∗
    isFieldList s fl

/-- A `fieldpath.Path` literal (`fieldpath.Path{e1, ...}`), read-only. -/
def isPath_intro.law : Prop :=
  ∀ (s : GoSlice) (es : List fieldpath.PathElement) (p : Path), es.length = p.length →
    s ↦*{DFrac.discard} es -∗ sepL (fun ep => isPE (GF := GF) ep.1 ep.2) (es.zip p) -∗ isPath s p

/-- `[]fieldpath.Path` element lists: empty, one more, and two concatenated (both ways). -/
def isPaths_nil.law : Prop := iprop(True) ⊢ isPaths (GF := GF) [] []
def isPaths_cons.law : Prop :=
  ∀ s ss p ps, isPaths (GF := GF) (s :: ss) (p :: ps) ⊣⊢ isPath s p ∗ isPaths ss ps
def isPaths_app.law : Prop :=
  ∀ ss ss' ps ps', ss.length = ps.length →
    isPaths (GF := GF) (ss ++ ss') (ps ++ ps') ⊣⊢ isPaths ss ps ∗ isPaths ss' ps'
/-- A path list's length is its slices'. -/
def isPaths_length.law : Prop := ∀ ss ps, isPaths (GF := GF) ss ps ⊢ ⌜ss.length = ps.length⌝

/-- A `ManagedFields` literal with the entries `ms` (distinct managers, any order), read-only. -/
def isMF_intro.law : Prop :=
  ∀ (m : fieldpath.ManagedFields) (M : GMap GoString GoInterface) (ms : List (GoString × VSet)),
    (ms.map (·.1)).Nodup → (∀ k, (M !! k).isSome = (lookupKV k ms).isSome) →
    m ↦$□ M -∗ sepL (fun me => iprop(∃ i, ⌜M !! me.1 = some i⌝ ∗ isVSet (GF := GF) i me.2)) ms -∗
    isMF m (MF.ofList ms)

/-- A `[]Conflict` literal, read-only. -/
def isConflicts_intro.law : Prop :=
  ∀ (s : merge.Conflicts) (xs : List merge.Conflict) (cs : List (GoString × Path)),
    xs.length = cs.length →
    s ↦*{DFrac.discard} xs -∗
    sepL (fun xc => iprop(⌜xc.1.Manager' = xc.2.1⌝ ∗ isPath (GF := GF) xc.1.Path' xc.2.2)) (xs.zip cs) -∗
    isConflicts s cs

/-- A `merge.Updater` literal (Kubernetes' `structuredmerge.go` builds one directly), read-only. -/
def isUpdater_intro.law : Prop :=
  ∀ u cv igf igfl rion,
    u ↦□ (merge.Updater.mk cv igf igfl rion) ⊢ isUpdater (GF := GF) u cv igf igfl rion

/-- A named `schema.TypeRef` literal (`schema.TypeRef{NamedType: &n}`). -/
def isTypeRef_intro.law : Prop :=
  ∀ (tr : schema.TypeRef) (t : TypeRef),
    tr.Inlined'.Scalar' = null → tr.Inlined'.List' = null → tr.Inlined'.Map' = null →
    tr.ElementRelationship' = null → tr.Nullable' = t.nullable →
    tr.NamedType' ↦□ t.name ⊢ isTypeRef (GF := GF) tr t

/-- A schema literal's atoms (`schema.Atom{Scalar: &s}`, `{List: &schema.List{...}}`,
`{Map: &schema.Map{...}}`), their lazy index still zero: the pieces of a `freshSchema`. -/
def freshAtom_scalar.law : Prop :=
  ∀ (a : schema.Atom) (s : Scalar), a.List' = null → a.Map' = null →
    a.Scalar' ↦□ s.goName ⊢ freshAtom (GF := GF) a (.scalar s)
def freshAtom_list.law : Prop :=
  ∀ (a : schema.Atom) (v : schema.List') (ksl : GoSlice) (e : TypeRef) (rel : ElemRel)
    (ks : List GoString), a.Scalar' = null → a.Map' = null →
    v.ElementRelationship' = rel.goName → v.Keys' = ksl →
    a.List' ↦□ v -∗ ksl ↦*{DFrac.discard} ks -∗ isTypeRef (GF := GF) v.ElementType' e -∗
    freshAtom a (.list e rel ks)
def freshAtom_map.law : Prop :=
  ∀ (a : schema.Atom) (fsl : GoSlice) (sfs : List schema.StructField)
    (fs : List (GoString × TypeRef)) (etv : schema.TypeRef) (e : Option TypeRef) (rel : ElemRel),
    a.Scalar' = null → a.List' = null → a.Map' ≠ null → sfs.length = fs.length →
    (∀ sf ∈ sfs, sf.Default' = interface.nil) →
    a.Map'.[schema.Map, go!"Fields"] ↦□ fsl -∗ fsl ↦*{DFrac.discard} sfs -∗
    sepL (fun sf => iprop(⌜sf.1.Name' = sf.2.1⌝ ∗ isTypeRef (GF := GF) sf.1.Type' sf.2.2)) (sfs.zip fs) -∗
    a.Map'.[schema.Map, go!"Unions"] ↦□ slice.nil -∗
    a.Map'.[schema.Map, go!"ElementType"] ↦□ etv -∗
    (match e with
     | some t => isTypeRef etv t
     | none => iprop(⌜etv.NamedType' = null ∧ etv.Inlined'.Scalar' = null ∧
         etv.Inlined'.List' = null ∧ etv.Inlined'.Map' = null ∧
         etv.ElementRelationship' = null ∧ etv.Nullable' = false⌝)) -∗
    a.Map'.[schema.Map, go!"ElementRelationship"] ↦□ rel.goName -∗
    a.Map'.[schema.Map, go!"once"] ↦ (zero_val sync.Once) -∗
    a.Map'.[schema.Map, go!"m"] ↦ (zero_val (sync.atomic.Pointer GoMap)) -∗
    freshAtom a (.map fs e rel)

/-- A schema literal (`&schema.Schema{Types: []schema.TypeDef{...}}`), its lazy index zero. -/
def freshSchema_intro.law : Prop :=
  ∀ (sc : Loc) (tys : GoSlice) (tds : List schema.TypeDef) (S : Schema),
    tds.length = S.types.length →
    sc.[schema.Schema, go!"Types"] ↦□ tys -∗ tys ↦*{DFrac.discard} tds -∗
    sepL (fun ta => iprop(⌜ta.1.Name' = ta.2.1⌝ ∗ freshAtom (GF := GF) ta.1.Atom' ta.2.2))
      (tds.zip S.types) -∗
    sc.[schema.Schema, go!"once"] ↦ (zero_val sync.Once) -∗
    sc.[schema.Schema, go!"m"] ↦ (zero_val (sync.atomic.Pointer GoMap)) -∗
    freshSchema sc S

/-- A schema literal becomes a shared schema (its lazy indexes put under their onces). -/
def isSchema_intro.law : Prop :=
  ∀ sc S, freshSchema (GF := GF) sc S ⊢ |={⊤}=> isSchema sc S

/-! ## Elimination -/

/-- A typed value conforms to its type. -/
def isTV_conforms.law : Prop :=
  ∀ p sc S t x, isTV (GF := GF) p sc S t x ⊢ ⌜conforms S t x⌝

/-- A typed value's schema, in scope. -/
def isTV_schema.law : Prop :=
  ∀ p sc S t x, isTV (GF := GF) p sc S t x ⊢ isSchema sc S ∗ ⌜S.WF⌝

end laws

/-! ## Pure laws -/

/-- Sets are equal when they have the same paths. -/
def PathSet_ext.law : Prop := ∀ a b : PathSet, (∀ q, q ∈ a ↔ q ∈ b) → a = b

/-- Managed fields kept sorted (every `isMF`'s, `MF.ofList`'s) are equal when every manager's entry
is. -/
def MF_ext.law : Prop :=
  ∀ a b : MF, keysSorted a = true → keysSorted b = true → (∀ m, a.get m = b.get m) → a = b

/-- `ensureNamed`, declaratively. -/
def ensureNamed_mem.law : Prop :=
  ∀ S t s q, q ∈ ensureNamed S t s ↔ q ∈ s ∨ ∃ p n, q = p ++ [.field n] ∧
    (∃ r, r ≠ [] ∧ (q ++ r) ∈ s) ∧
    ∃ fs e rel, (typeAlong S (some t) p).bind (fun t => S.find t.name) = some (.map fs e rel) ∧
      (lookupKV n fs).isSome

/-- `atomicNodes`, declaratively. -/
def atomicNodes_mem.law : Prop :=
  ∀ S t s p, p ∈ atomicNodes S t s ↔ p ≠ [] ∧ (∃ r, r ≠ [] ∧ (p ++ r) ∈ s) ∧
    ∃ t', reconAt S t p = some t' ∧ isAtomicT S t' = true

/-- `reconcile`, declaratively. -/
def reconcile_mem.law : Prop :=
  ∀ S t s q, q ∈ reconcile S t s ↔
    (q ∈ s ∧ ¬ ∃ p, p ∈ atomicNodes S t s ∧ p <+: q) ∨ q ∈ atomicNodes S t s

/-- A set written at this schema is its own reconciliation. -/
def reconcile_id.law : Prop :=
  ∀ S t s, schemaConsistent S t s → reconcile S t s = s

/-- `keysWithItemsB` decides `keysWithItems`. -/
def keysWithItemsB_iff.law : Prop :=
  ∀ S t s, keysWithItemsB S t s = true ↔ keysWithItems S t s

/-- `Apply` keeps its own premise on the managers: the new managers' sets are at the request's
version, keep items with their key fields and have nothing below a key field (so a client can
chain applies). -/
def applyResult_premise.law : Prop :=
  ∀ S t rion live config ver (mf : MF) mgr force obj mf', S.WF → conforms S t live → conforms S t config →
    keysSorted mf = true →
    (∀ m e, mf.get m = some e → e.version = ver ∧ keysWithItems S t e.set) →
    applyResult S t rion live config ver mf mgr force = .ok obj mf' →
    keysSorted mf' = true ∧
    (∀ m e, mf'.get m = some e → e.version = ver ∧ keysWithItems S t e.set ∧ schemaConsistent S t e.set)

/-- `Update` likewise (its result's managers are at `ver` if the input's are). -/
def updateResult_premise.law : Prop :=
  ∀ S t live new ver (mf : MF) mgr, S.WF → conforms S t live → conforms S t new →
    keysSorted mf = true →
    (∀ m e, mf.get m = some e → e.version = ver ∧ keysWithItems S t e.set) →
    keysSorted (updateResult S t live new ver mf mgr) = true ∧
    (∀ m e, (updateResult S t live new ver mf mgr).get m = some e →
      e.version = ver ∧ keysWithItems S t e.set ∧ schemaConsistent S t e.set)

/-- Merging nothing into a value is the value (a list item only one side has). -/
def mergeF_none.law : Prop :=
  ∀ S t x n, S.WF → conforms S t x → x.size < n → mergeF n S t (some x) none = some x

end smd
end EtcdGrove
end Perennial
