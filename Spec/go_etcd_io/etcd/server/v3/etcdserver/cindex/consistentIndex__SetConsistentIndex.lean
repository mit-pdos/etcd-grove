/-
`(*consistentIndex).SetConsistentIndex(v, term)`. Lean-first (no Rocq counterpart); see
`InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci.SetConsistentIndex(v, term)`, under the pair mutex, stores the index `v` (the
linearization point: the caller's update gets `ciIdx γ k` and gives back `ciIdx γ v`), then the
term. (keepfix-d, 2026-11-27) The caller gives the pair predicate of the pair it stores, for a
non-zero index. -/
abbrev consistentIndex.SetConsistentIndex.spec : Prop :=
  ∀ (ci : Loc) (γ : CINames) (P : w64 → w64 → IProp GF) (v term : w64),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI ci γ P ∗ (⌜v = W64 0⌝ ∨ □ P v term)) -∗
    (|={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ k ∗ (ciIdx γ v ={∅, ⊤ \ ↑ciN}=∗ Φ #())) -∗
    WP (App (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"SetConsistentIndex"))
      (Val #v)) (Val #term)) {{ Φ }}

end spec

end EtcdGrove
end Perennial
