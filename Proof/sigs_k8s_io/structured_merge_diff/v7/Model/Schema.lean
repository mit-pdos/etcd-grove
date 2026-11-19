/-
The pure model of SMD's **schema** (`schema` package): `TypeRef`, `Atom`, `List`, `Map`,
`StructField`, `Schema`, `Resolve`, `FindNamedType`, `FindField` and the `Equals` methods.

Not modelled (the representation predicate requires them absent): a `TypeRef`'s
`ElementRelationship` override (`nil`: `Resolve` never takes the lock nor fills
`resolvedTypes`; `TypeRef.Equals` compares that field by pointer), a `Map`'s `Unions` (empty), a
`StructField`'s `Default` (`nil`: `reflect.DeepEqual(nil, nil)` is the only case of
`StructField.Equals`, and associative-list keys have no defaults). `Option ListT`, `Option MapT`
and `List StructField` are spelled `OptListT`, `OptMapT` and `Fields` inside the mutual block, so
that the `Equals` functions are structurally recursive (kernel-reducible).

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.Model.Value

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace smd

/-! ## schema (no unions, no field defaults, no element-relationship overrides) -/

mutual
/-- `schema.TypeRef` (its `ElementRelationship` override is `nil`). -/
inductive TypeRef where
  | mk (namedType : Option GoString) (inlined : Atom) (nullable : Bool)
/-- `schema.Atom`. -/
inductive Atom where
  | mk (scalar : Option GoString) (list : OptListT) (map : OptMapT)
/-- An `Option ListT` (in the mutual block, for structural recursion). -/
inductive OptListT where
  | none
  | some (l : ListT)
/-- An `Option MapT`. -/
inductive OptMapT where
  | none
  | some (m : MapT)
/-- `schema.List`. -/
inductive ListT where
  | mk (elementType : TypeRef) (er : GoString) (keys : List GoString)
/-- `schema.Map` (no unions). -/
inductive MapT where
  | mk (fields : Fields) (elementType : TypeRef) (er : GoString)
/-- A `List StructField`. -/
inductive Fields where
  | nil
  | cons (f : StructField) (rest : Fields)
/-- `schema.StructField` (no default). -/
inductive StructField where
  | mk (name : GoString) (type : TypeRef)
end

instance : Inhabited TypeRef := ⟨.mk none (.mk none .none .none) false⟩

def OptListT.isSome : OptListT → Bool | .none => false | .some _ => true
def OptMapT.isSome : OptMapT → Bool | .none => false | .some _ => true
def OptListT.toOption : OptListT → Option ListT | .none => Option.none | .some l => Option.some l
def OptMapT.toOption : OptMapT → Option MapT | .none => Option.none | .some m => Option.some m
def Fields.toList : Fields → List StructField | .nil => [] | .cons f fs => f :: fs.toList
def Fields.ofList : List StructField → Fields | [] => .nil | f :: fs => .cons f (Fields.ofList fs)

namespace TypeRef
def namedType : TypeRef → Option GoString | .mk n _ _ => n
def inlined : TypeRef → Atom | .mk _ a _ => a
def nullable : TypeRef → Bool | .mk _ _ b => b
end TypeRef
namespace Atom
def scalar : Atom → Option GoString | .mk s _ _ => s
def list : Atom → Option ListT | .mk _ l _ => l.toOption
def map : Atom → Option MapT | .mk _ _ m => m.toOption
def ofScalar (s : GoString) : Atom := .mk (some s) .none .none
def ofList (l : ListT) : Atom := .mk none (.some l) .none
def ofMap (m : MapT) : Atom := .mk none .none (.some m)
end Atom
namespace ListT
def elementType : ListT → TypeRef | .mk t _ _ => t
def er : ListT → GoString | .mk _ e _ => e
def keys : ListT → List GoString | .mk _ _ k => k
end ListT
namespace MapT
def fields : MapT → List StructField | .mk f _ _ => f.toList
def elementType : MapT → TypeRef | .mk _ t _ => t
def er : MapT → GoString | .mk _ _ e => e
end MapT
namespace StructField
def name : StructField → GoString | .mk n _ => n
def type : StructField → TypeRef | .mk _ t => t
end StructField

/-- `schema.Schema` (`Types`). -/
structure Schema where
  types : List (GoString × Atom)

def erAtomic : GoString := go!"atomic"
def erAssociative : GoString := go!"associative"

/-- `Schema.FindNamedType`: the last type of that name (the index is built in order). -/
def Schema.findNamedType (sc : Schema) (n : GoString) : Option Atom :=
  sc.types.foldl (fun acc (n', a) => if n' = n then some a else acc) none

/-- `Schema.Resolve` (no override). -/
def Schema.resolve (sc : Schema) (tr : TypeRef) : Option Atom :=
  match tr.namedType with
  | some n => sc.findNamedType n
  | none => some tr.inlined

/-- `Map.FindField`: the last field of that name. -/
def MapT.findField (m : MapT) (n : GoString) : Option StructField :=
  m.fields.foldl (fun acc f => if f.name = n then some f else acc) none

-- The `Equals` methods of `schema` (no unions or defaults: `reflect.DeepEqual(nil, nil)`).
mutual
def TypeRef.equals : TypeRef → TypeRef → Bool
  | .mk n a b, .mk n' a' b' =>
    (match n, n' with
      | none, none => true
      | some x, some y => decide (x = y)
      | _, _ => false) &&
    b == b' && Atom.equals a a'
  termination_by structural x => x
def Atom.equals : Atom → Atom → Bool
  | .mk s l m, .mk s' l' m' =>
    s.isSome == s'.isSome && OptListT.isSome l == OptListT.isSome l' &&
      OptMapT.isSome m == OptMapT.isSome m' &&
    (if s.isSome then decide (s = s')
     else if OptListT.isSome l then OptListT.equals l l'
     else OptMapT.equals m m')
  termination_by structural x => x
def OptListT.equals : OptListT → OptListT → Bool
  | .none, .none => true
  | .some x, .some y => ListT.equals x y
  | _, _ => false
  termination_by structural x => x
def OptMapT.equals : OptMapT → OptMapT → Bool
  | .none, .none => true
  | .some x, .some y => MapT.equals x y
  | _, _ => false
  termination_by structural x => x
def ListT.equals : ListT → ListT → Bool
  | .mk t e k, .mk t' e' k' => TypeRef.equals t t' && decide (e = e') && decide (k = k')
  termination_by structural x => x
def MapT.equals : MapT → MapT → Bool
  | .mk f t e, .mk f' t' e' => TypeRef.equals t t' && decide (e = e') && Fields.equals f f'
  termination_by structural x => x
/-- The fields' lengths and the fields, in order. -/
def Fields.equals : Fields → Fields → Bool
  | .nil, .nil => true
  | .cons a as, .cons b bs => StructField.equals a b && Fields.equals as bs
  | _, _ => false
  termination_by structural x => x
def StructField.equals : StructField → StructField → Bool
  | .mk n t, .mk n' t' => decide (n = n') && TypeRef.equals t t'
  termination_by structural x => x
end

/-- `t == schema.TypeRef{}`. -/
def TypeRef.isZero (tr : TypeRef) : Bool :=
  tr.namedType.isNone && tr.inlined.scalar.isNone && tr.inlined.list.isNone &&
    tr.inlined.map.isNone && !tr.nullable

-- Every associative list's key names are distinct (a premise of the specs: `FieldList.Sort`
-- sorts a list item's key fields with `sort.SliceStable`, whose trust-boundary spec does not state
-- stability, so only distinct names have one sorted order).
mutual
def TypeRef.keysNodup : TypeRef → Bool
  | .mk _ a _ => Atom.keysNodup a
  termination_by structural x => x
def Atom.keysNodup : Atom → Bool
  | .mk _ l m => OptListT.keysNodup l && OptMapT.keysNodup m
  termination_by structural x => x
def OptListT.keysNodup : OptListT → Bool
  | .none => true
  | .some l => ListT.keysNodup l
  termination_by structural x => x
def OptMapT.keysNodup : OptMapT → Bool
  | .none => true
  | .some m => MapT.keysNodup m
  termination_by structural x => x
def ListT.keysNodup : ListT → Bool
  | .mk t _ ks => decide ks.Nodup && TypeRef.keysNodup t
  termination_by structural x => x
def MapT.keysNodup : MapT → Bool
  | .mk fs t _ => Fields.keysNodup fs && TypeRef.keysNodup t
  termination_by structural x => x
def Fields.keysNodup : Fields → Bool
  | .nil => true
  | .cons f rest => StructField.keysNodup f && Fields.keysNodup rest
  termination_by structural x => x
def StructField.keysNodup : StructField → Bool
  | .mk _ t => TypeRef.keysNodup t
  termination_by structural x => x
end

def Schema.keysNodup (sc : Schema) : Bool := sc.types.all (fun (_, a) => a.keysNodup)

end smd
end EtcdGrove
end Perennial
