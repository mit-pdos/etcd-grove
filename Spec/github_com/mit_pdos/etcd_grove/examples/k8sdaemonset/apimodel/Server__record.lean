/-
`s.record(t, typ, rv, obj)`, under the lock: the object stored (or removed, for a deletion) and a copy of it logged; waiters woken.
Lean-first (no Rocq counterpart); phase 3 of `notes/k8s-daemonset-plan.md` (the model API server's
specs, D50's internal layer).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

abbrev Server.record.spec : Prop :=
  ∀ [ApiDeps] (s : Loc) (γ : ApiNames) (L : SrvLocs) (cfg : apimodel.Config) (r : Res) (tb : Table)
    (typ : EvTy) (rv : w64) (obj : GoInterface) (o : Obj),
  {{ (srvFixed s γ L cfg : IProp GF) ∗ tableLocked (L.tbl r) tb ∗ objAt obj (DFrac.own 1) o }}
    (App (App (App (App (Val (s @!! go.GoType.PointerType apimodel.Server.ty @!! go!"record")) (Val #(L.tbl r).t)) (Val #typ.str)) (Val #rv)) (Val #obj))
  {{ RET #(); tableLocked (L.tbl r) (tb.record ⟨typ, rv, o⟩) }}

end spec

end apimodel
end EtcdGrove
end Perennial
