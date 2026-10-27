/-
`delete(m, k)` on a map of a named map type (2026-10-26). Lean-first.

Goose emits `delete` at the operand's type, so `delete(s, item)` in `sets.Set[T].Delete`
(`s : Set[T]`, `type Set[T comparable] map[T]Empty`) is `FuncResolve go.delete [Set[T]]`.
Perennial's semantics resolves it at the underlying type (`PredeclaredSemantics.delete_underlying`),
where `MapSemantics.delete_map` unfolds it: `wp_mapDelete` at a named map type, as raft's
`wp_mapDelete_named` (`Proof/go_etcd_io/raft/v3/InvTracker.lean`, keys `uint64`) for any key type.
-/
module

public import Perennial.Golang.Theory.Map
public import Perennial.Golang.Defn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {s : Stuckness} {E : CoPset}
variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

/-- `wp_mapDelete` at a named map type `t`. -/
theorem wp_mapDelete_underlying {t key_type elem_type : go.GoType}
    [h : go.UnderlyingDirectedEq t (go.MapType key_type elem_type)]
    (l : Loc) (m : GMap K V) (k : K) [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (l ↦$ m : IProp GF) }}
      (App (App (Val #(functions go.delete [t])) (Val #l)) (Val #k)) @ s; E
    {{ RET #(); l ↦$ (GMap.delete k m) }} := by
  rw [go.delete_underlying t, h.underlying_unfold, ← go.delete_underlying]
  exact wp_mapDelete l m k key_type elem_type

end lemmas

end EtcdGrove
end Perennial
