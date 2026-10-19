/- Lean-first (no Rocq counterpart).

`step(c, in, out)` (linkv.go): the configurations `c` steps to by the operation `(in, out)`
(`stepL`, the model's `CStep`: `stepL_sound`, `stepL_complete`), each held by `cfgOwn` (sharing
`c`'s slices). The premise bounds `c`'s lengths, for `set` and `insertSorted`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- See the file header. -/
abbrev step.spec : Prop :=
  ∀ (c : kvConfig) (g : GCfg) (x : Input) (y : Output),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv ∗
      cfgOwn c g ∗ ⌜g.kv.length + 1 < 2 ^ 63 ∧ g.pend.length + 1 < 2 ^ 63⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.step)) (Val #c)) (Val #x))
      (Val #y))
  {{ (r : GoSlice) (cs : List kvConfig), RET #r;
      r ↦* cs ∗ [∗list] c';g' ∈ cs;stepL g x y, cfgOwn c' g' }}

end spec

end linkv
end EtcdGrove
end Perennial
