/-
The structured-merge-diff driver's scenario (`examples/k8s/smd/smd.go`) in the SMD API's abstract
vocabulary (`Proof/sigs_k8s_io/structured_merge_diff/v7/{value,fieldpath,schema,typed,merge}/
Defs.lean`): the schema `newSchema` builds, the type of its objects, the paths and versioned sets
the driver writes out, and its `state` as a pair of an object and managed fields. The nine steps'
expected results are computed from the API's vocabulary by `decide` in `Steps.lean`; why the API
specs give them is `notes/smd-plan.md`, "Sanity checks".

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open smd

/-! ## The schema (`newSchema`) -/

def strRef : TypeRef := ⟨go!"string", false⟩
def numRef : TypeRef := ⟨go!"numeric", false⟩

/-- The schema `newSchema` builds. -/
def sc0 : Schema := ⟨[
  (go!"root", .map [(go!"name", strRef), (go!"image", strRef), (go!"replicas", numRef),
    (go!"containers", ⟨go!"containers", false⟩), (go!"labels", ⟨go!"labels", false⟩),
    (go!"selector", ⟨go!"selector", false⟩)] none .unset),
  (go!"container", .map [(go!"name", strRef), (go!"image", strRef), (go!"port", numRef)] none .unset),
  (go!"containers", .list ⟨go!"container", false⟩ .associative [go!"name"]),
  (go!"labels", .map [] (some strRef) .separable),
  (go!"selector", .map [] (some strRef) .atomic),
  (go!"string", .scalar .string),
  (go!"numeric", .scalar .numeric)]⟩

/-- `schema.TypeRef{NamedType: &rootName}`. -/
def rootRef : TypeRef := ⟨go!"root", false⟩

/-- The scenario's one API version. -/
abbrev version : GoString := go!"v1"

/-! ## Paths and versioned sets -/

def str (x : GoString) : UVal := .str x

/-- `field(name)`. -/
def field (n : GoString) : Path := [.field n]
/-- `mapKey(name, key)`. -/
def mapKey (n k : GoString) : Path := [.field n, .field k]
/-- `item(key)`: the container with that name. -/
def item (k : GoString) : Path := [.field go!"containers", .key [(go!"name", str k)]]
/-- `itemField(key, name)`. -/
def itemField (k n : GoString) : Path := item k ++ [.field n]
/-- `containerPaths(key)`. -/
def containerPaths (k : GoString) : List Path := [item k, itemField k go!"name", itemField k go!"image"]

/-- `applied(paths...)`. -/
def applied (ps : List Path) : VSet := ⟨PathSet.ofList ps, version, true⟩
/-- `updated(paths...)`. -/
def updated (ps : List Path) : VSet := ⟨PathSet.ofList ps, version, false⟩

/-- `container(name, image)`'s entries (sorted: `kvsOf`). -/
def containerKVs (n i : GoString) : List (GoString × UVal) :=
  kvsOf [(go!"name", str n), (go!"image", str i)]

/-- `container(name, image)`. -/
def container (n i : GoString) : UVal := .map (containerKVs n i)

/-! ## The driver's `state` -/

/-- The driver's state: the stored object and its managed fields. -/
structure St where
  live : UVal
  mf : MF

end k8s_smd
end EtcdGrove
end Perennial
