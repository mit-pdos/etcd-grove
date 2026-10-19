/- Lean-first (no Rocq counterpart).

`Model()` (linkv.go): the key-value store's porcupine model, against `kvM decOp` (`linkvS`,
`Defs.lean`): porcupine's `isModel linkvS m`, in the parts it is made of over any `HasLC`
(`isModel_of_step` assembles them; `isModel` is stated at `HasLC.hasLC`, as `StepContext`'s
`isContext` is). `Partition`, `StepContext` and `Hash` are `nil`;
`Init` returns a value of the initial state (one empty configuration); `Equal` returns `true` only
on equal lists, so on one state; and `Step` steps as `kvM decOp` does.

`linkvS.rep k` is `stRepB (k + 1)`: a value made by `k` steps has configurations of lengths below
`k + 1`, so a step from an index below porcupine's `2^60` stays below `2^63`. Without the index
no model of a Go value of `Model()` meets porcupine's `stepSpec`: after `2^63 - 1` failed puts on
one configuration, `insertSorted`'s `make([]kvEntry, 0, len(pend)+1)` overflows and panics there
(`set`'s likewise, with `2^63 - 1` distinct keys); porcupine passes the bound (`ModelSpec.rep`,
`notes/STATUS.md`, D20).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkv github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- See the file header. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.Model)) (Val #()))
  {{ (m : Model), RET #m;
      ⌜m.Partition' = func.nil⌝ ∗ initSpec linkvS m.Init' ∗
      ⌜m.StepContext' = func.nil ∧ m.Step' ≠ func.nil⌝ ∗ stepSpec linkvS m.Step' ∗
      isEqHash linkvS m }}

end spec

end linkv
end EtcdGrove
end Perennial
