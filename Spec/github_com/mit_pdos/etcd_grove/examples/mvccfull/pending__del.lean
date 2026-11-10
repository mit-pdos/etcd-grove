/- Lean-first (no Rocq counterpart).

`p.del(keys, key, end)` (`examples/mvccfull/mvccfull.go`): the pending transaction's model deletes
the range's present keys among `keys`, in their order (`PendM.del`, `Pending.lean`), each delete's
change appended; it returns how many it deleted. (mvccrand's took the keys from its package
variable; here the caller passes `runner.keys`.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Pending

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev pending.del.spec : Prop :=
  ∀ (p : Loc) (P : PendM) (keys : GoSlice) (ks : List GoString) (dks : DFrac) (key endk : GoSlice)
    (kk e : GoString) (dq dq' : DFrac),
  ks.Pairwise go.GoStringLt →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ ownPending p P ∗ keys ↦*{dks} ks ∗ key ↦*{dq} kk ∗ endk ↦*{dq'} e }}
    (App (App (App (p @!! go.GoType.PointerType pending.ty @!! go!"del") (Val #keys)) (Val #key)) (Val #endk))
  {{ RET #(W64 (P.delKeys ks (decide (endk = slice.nil)) kk e).length);
      ownPending p (P.del ks (decide (endk = slice.nil)) kk e) ∗ keys ↦*{dks} ks ∗
      key ↦*{dq} kk ∗ endk ↦*{dq'} e }}

end spec

end mvccfull
end EtcdGrove
end Perennial
