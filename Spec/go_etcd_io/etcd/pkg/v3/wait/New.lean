/-
`wait.New()` (`wait.go`): a new wait registry, the contract `isWait` (`wait/Defs.lean`) for any
registration condition. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.wait.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `wait.New()` returns a `Wait` meeting `isWait` for the ids `γi` and any registration
condition `R`, with a fresh ghost map of the registered ids (`γw`) and the reader's resource
`RD` (the shards' reader slots). -/
abbrev wait.New.spec : Prop :=
  ∀ (γi : IdNames) (R : w64 → (GoInterface → IProp GF) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait }}
    (App (Val (@! wait.New)) (Val #()))
  {{ (w : GoInterface), RET #w; ∃ (γw : GName) (RD : IProp GF), isWait w γi γw R RD ∗ RD }}

end spec

end EtcdGrove
end Perennial
