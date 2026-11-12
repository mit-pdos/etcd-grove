/-
`(*consistencyStore).getWrittenRecord(owner)` (`consistency.go:103`): the owner's record (or nil),
read under the map's read lock. Lean-first; internal (`WroteAt`'s and `EnsureReady`'s
linearization points are at its read).
-/
module

public import Proof.k8s_io.client_go.util.consistency.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI k8s_io.client_go.util.consistency

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

/-- `c.getWrittenRecord(o)`: `W !! o` (or nil) of the map `W` it reads; the caller's view shift
`Q` runs at the read, holding the read lock's share of the map's mirror (`γ.W`), so it may open
the store's invariant and find `W` there. -/
abbrev consistencyStore.getWrittenRecord.spec : Prop :=
  ∀ (c : Loc) (γ : ConsNames) (T : Owner → Qp → IProp GF) (S : GMap GR LastSyncRVGetter)
    (G : GR → GoString → IProp GF) (o : Owner) (Q : GMap Owner Loc → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency ∗
      isCons c γ T S G ∗ consReader c γ ∗
      (∀ W, ghostVar γ.W sync.rfrac.half W ={⊤}=∗ ghostVar γ.W sync.rfrac.half W ∗ Q W) }}
    (App (Val (c @!! go.GoType.PointerType consistencyStore.ty @!! go!"getWrittenRecord"))
      (Val #o))
  {{ (r : Loc), RET #r; consReader c γ ∗ ∃ W, ⌜r = (W !! o).getD (zero_val Loc)⌝ ∗ Q W }}

end spec

end consistency
end EtcdGrove
end Perennial
