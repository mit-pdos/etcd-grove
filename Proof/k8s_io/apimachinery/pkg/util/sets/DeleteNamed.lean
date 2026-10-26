/-
**Go's semantics: `delete(m, k)` on a map of a named type** (2026-10-26). Lean-first.

Perennial's semantics unfolds `delete` only at a literal map type (`MapSemantics.delete_map`,
`FuncUnfold go.delete [go.MapType key_type elem_type]`), where its `len` takes any type whose
underlying type is a map (`len_map`, `[t ↓u go.MapType key_type elem_type]`: "otherwise `len(m)`
would be stuck when `m` has a named map type"). Goose emits `delete` at the operand's type, so
`delete(s, item)` in `sets.Set[T].Delete` (`s : Set[T]`, `type Set[T comparable] map[T]Empty`) is
`FuncResolve go.delete [Set[T]]`, which does not step. In Go, `delete` on a named map type is
`delete` on its underlying map type (the language specification, "Deletion of map elements": the
operand's core type is a map). `DeleteNamedMapSemantics` states that much, in `len_map`'s shape.

A **hypothesis class**, like `EtcdGrove.Float64ToInt64Semantics` (`FloatToInt.lean`), not an
axiom: the results that need it take it as an instance argument (`etc/gen-link.py`'s
`SEM_PREMISES`). The general fix, `delete_map` (and `clear_map`) at `[t ↓u go.MapType ..]`, is for
Perennial (`notes/perennial-changes.md`, "`delete` and `clear` on a named map type").
-/
module

public import Perennial.Golang.Theory.Map

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode

/-- **`delete` on a map of a named type** (a hypothesis on the semantics in use, see the file
header): it unfolds as at the underlying map type. -/
class DeleteNamedMapSemantics [FfiSyntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] : Prop where
  delete_named {t key_type elem_type : go.GoType} [t ↓u go.MapType key_type elem_type] :
    FuncUnfold go.delete [t]
    (λ: "m" "k",
       InternalMapCheckKey key_type "k" ;;
       Store "m" (InternalMapDelete (Read "m", "k")) : val)

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

/-- `wp_mapDelete` at a named map type `t`. -/
theorem wp_mapDelete_named [DeleteNamedMapSemantics] {t key_type elem_type : go.GoType}
    [ht : t ↓u go.MapType key_type elem_type]
    (l : Loc) (m : GMap K V) (k : K) [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (l ↦$ m : IProp GF) }}
      (App (App (Val #(functions go.delete [t])) (Val #l)) (Val #k)) @ s; E
    {{ RET #(); l ↦$ (GMap.delete k m) }} := by
  have h1 := (DeleteNamedMapSemantics.delete_named (t := t) (key_type := key_type)
    (elem_type := elem_type)).func_unfold
  have h2 := (go.MapSemantics.delete_map key_type elem_type).func_unfold
  rw [h1, ← h2]
  exact wp_mapDelete l m k key_type elem_type

end lemmas

end EtcdGrove
end Perennial
