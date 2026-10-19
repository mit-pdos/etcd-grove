/-
Lean-first (no Rocq counterpart).

# Porcupine's cache entries (2026-10-14)

`checkSingle`'s cache is a `map[uint64][]cacheEntry`; an entry is a clone of the bitset of the
operations linearized and the model's state. Nothing writes an entry once it is in the cache,
so what the checker knows of one is persistent (`cacheEntryOk`): its bitset's words `ws` (a
read-only slice), the abstract state `t` its state value represents (shared in the pool `p`,
`Shared.lean`: the model's `Equal` may write to it), and a fact `P ws t` (in `checkSingle`, that
the configuration is in the abstract cache of `Theory`).
-/
module

public import Proof.github_com.anishathalye.porcupine.Bitset
public import Proof.github_com.anishathalye.porcupine.Shared

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.anishathalye.porcupine

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [NaInvG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]
variable {σ : Type}

/-- A cache entry: a read-only bitset of words `ws` and a state value of `t` shared in the pool
`p`, with `P ws t`. -/
def cacheEntryOk (S : ModelSpec GF σ) (p : NaInvPoolName) (P : List w64 → σ → Prop)
    (ce : cacheEntry) : IProp GF :=
  iprop(∃ (ws : List w64) (t : σ), ce.linearized' ↦*□ ws ∗ shared S p ce.state' t ∗ ⌜P ws t⌝)

instance cacheEntryOk_persistent (S : ModelSpec GF σ) (p : NaInvPoolName)
    (P : List w64 → σ → Prop) (ce : cacheEntry) : Persistent (cacheEntryOk S p P ce) := by
  unfold cacheEntryOk; infer_instance

end defs

end github_com.anishathalye.porcupine

end Perennial
