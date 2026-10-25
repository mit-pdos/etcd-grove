/-
`Permitted(who, k)` (`examples/authkv/authkv.go`; the auth plan's E2b). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- `Permitted(who, k)` is `who = u ∧ k ∈ [lo, hi)` (`permittedK`), the model's verdict at the
set-up's state for the workload's principals (`granted_setupSt_iff`). -/
abbrev Permitted.spec : Prop :=
  ∀ (who k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.Permitted)) (Val #who))
      (Val #k))
  {{ RET #(decide (permittedK who k)); True }}

end spec

end authkv
end EtcdGrove
end Perennial
