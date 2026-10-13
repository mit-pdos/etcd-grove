/-
grpc's `status.Error(c, msg)` (`google.golang.org/grpc/status`), called by
`clientv3.WatchResponse.Err`. grpc is not translated (`Code/google_golang_org/grpc/status.toml`
declares only the names), so it is an axiom (`Proof/google_golang_org/grpc/status/Error.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `status.Error(c, msg)` (`New(c, msg).Err()`) for a code other than `codes.OK` returns a
non-nil error (a `*status.Error`), whose `Error()` returns some string (`errStrOk`: it formats
the code and the message). Only what `WatchResponse.Err` needs: nothing about which error, nor
about `codes.OK` (for which it returns `nil`). -/
abbrev status.Error.spec : Prop :=
  ∀ (c : w32) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
      ⌜(#c : val) ≠ google_golang_org.grpc.codes.OK⌝ }}
    (App (App (Val (@! google_golang_org.grpc.status.Error)) (Val #c)) (Val #msg))
  {{ (err : GoError), RET #err; ⌜err ≠ interface.nil⌝ ∗ errStrOk err }}

end spec

end EtcdGrove
end Perennial
