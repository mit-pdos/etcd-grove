/- Lean-first (no Rocq counterpart).

`Model()` (linkvtxn.go): etcd's KV as a porcupine model, against `pM TS decOp` (`linkvtxnS`,
`Defs.lean`), in the parts `isModel_of_step` assembles: `Partition`, `StepContext` and `Hash`
are `nil`; `Init` returns a value of the initial state (one configuration, the empty store at
revision 1); `Equal` returns `true` only on equal lists, so on one state; and `Step` steps as
`pM TS decOp` does. `linkvtxnS.rep k` is `stRepB (k + 1)`: a value made by `k` steps has
revisions and pending counts summing to at most `k + 1` (`Bounded`), so `mstep`'s revision and
the pending list's `make` stay far from overflow below porcupine's index `2^60`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.Model)) (Val #()))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m;
      ⌜m.Partition' = func.nil⌝ ∗ github_com.anishathalye.porcupine.initSpec linkvtxnS m.Init' ∗
      ⌜m.StepContext' = func.nil ∧ m.Step' ≠ func.nil⌝ ∗
      github_com.anishathalye.porcupine.stepSpec linkvtxnS m.Step' ∗
      github_com.anishathalye.porcupine.isEqHash linkvtxnS m }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
