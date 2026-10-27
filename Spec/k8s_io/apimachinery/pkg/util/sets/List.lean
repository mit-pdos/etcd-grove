/-
`List[T](s)` (`set.go:195`) at `string`: the set's items, sorted. Lean-first; for client-go's
thread-safe store (`storeIndex.addIndexers`, `threadSafeMap.IndexKeys`).
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.sets.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI k8s_io.apimachinery.pkg.util.sets

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

/-- `List(s)` of a set of strings with at most `2^62` items (`slices.Sort`'s bound): a new slice of
the items, each once, in increasing order. -/
abbrev List'.spec : Prop :=
  ∀ (m : Loc) (dq : DFrac) (s : GMap GoString Elem), GMap.size s ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗ m ↦${dq} s }}
    (App (Val #(functions List' [go.string])) (Val #m))
  {{ (sl : GoSlice) (ks : List GoString), RET #sl; m ↦${dq} s ∗ sl ↦* ks ∗
      ⌜(∀ k, k ∈ ks ↔ (s !! k).isSome) ∧ ks.Nodup ∧
        ∀ (i j : Nat) (a b : GoString), ks[i]? = some a → ks[j]? = some b → i < j →
          ¬ go.GoStringLt b a⌝ }}

end spec

end sets
end EtcdGrove
end Perennial
