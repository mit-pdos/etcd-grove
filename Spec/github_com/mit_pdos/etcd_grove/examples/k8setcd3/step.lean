/- Lean-first (no Rocq counterpart).

`step(c, in, out)` (k8setcd3.go): the configurations `c` steps to by `(in, out)` (`stepL`): a
call that returned no error took effect and answered the model's output; a failed write becomes
pending; a failed read does nothing. Its premises bound the lengths (`mstep`'s, and the pending
list's `make`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8setcd3


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev step.spec : Prop :=
  ∀ (c : mcfg) (g : GCfg) (x : Input) (y : Output),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ cfgOwn c g ∗ ⌜g.st.items.length + 1 < 2 ^ 63 ∧ g.pend.length + 1 < 2 ^ 63⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.step)) (Val #c)) (Val #x)) (Val #y))
  {{ (r : GoSlice) (cs : List mcfg), RET #r;
      r ↦* cs ∗ [∗list] c';g' ∈ cs;stepL g x y, cfgOwn c' g' }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
