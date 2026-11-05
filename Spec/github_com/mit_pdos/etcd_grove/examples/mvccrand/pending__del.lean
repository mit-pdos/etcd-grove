/- Lean-first (no Rocq counterpart).

`p.del(key, end)` (`examples/mvccrand/mvccrand.go`): the pending transaction's model deletes the
range's present keys, in the tester's key order (`PendM.del`, `Pending.lean`), each delete's change
appended; it returns how many it deleted.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Pending

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev pending.del.spec : Prop :=
  ∀ (p : Loc) (P : PendM) (key endk : GoSlice) (kk e : GoString) (dq dq' : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      ownPending p P ∗ key ↦*{dq} kk ∗ endk ↦*{dq'} e }}
    (App (App (Val (p @!! go.GoType.PointerType pending.ty @!! go!"del")) (Val #key)) (Val #endk))
  {{ RET #(W64 (P.delKeys (decide (endk = slice.nil)) kk e).length);
      ownPending p (P.del (decide (endk = slice.nil)) kk e) ∗ key ↦*{dq} kk ∗ endk ↦*{dq'} e }}

end spec

end mvccrand
end EtcdGrove
end Perennial
