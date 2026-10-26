/-
`decomposeOpts(lg, optstr)` (`server/auth/store.go`): the token options' decomposition, for
`NewTokenProvider`. Lean-first (no Rocq counterpart); the auth plan's E2g (2026-10-25).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `decomposeOpts(lg, optstr)`: the token type, the first of `optstr`'s comma-separated fields
(`strings.Split`), with an owned map of the other fields' `key=value` pairs; or an error (a field
that is not one `key=value` pair, or a key given twice), not `nil`, only if there is more than one
field. -/
abbrev auth.decomposeOpts.spec : Prop :=
  ∀ (lg : Loc) (optstr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.decomposeOpts)) (Val #lg)) (Val #optstr))
  {{ (tt : GoString) (m : Loc) (err : GoInterface), RET (PairV (PairV #tt #m) #err);
      (⌜err = GoInterface.nil⌝ ∗ ⌜tt = (_root_.Perennial.strings.split optstr go!",").head!⌝ ∗
        ∃ mm : GMap GoString GoString, m ↦$ mm) ∨
      ⌜err ≠ GoInterface.nil ∧ 1 < (_root_.Perennial.strings.split optstr go!",").length⌝ }}

end spec

end EtcdGrove
end Perennial
