/-
`types.IDFromString`: the trust boundary (`client/pkg/v3/types` is names-only; rafthttp stage 5e-2,
accepted by the user 2026-10-23). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.IDStr
public import Proof.net.http.Boundary

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `types.IDFromString(s)` (`strconv.ParseUint(s, 16, 64)`): an id and an error whose `Error()`
returns; of a member id's string (`types.idStr x`, `ID.String`'s), `x` and no error (`ParseUint`
inverts `FormatUint`). -/
abbrev types.IDFromString.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.types.IDFromString)) (Val #s))
  {{ (id : w64) (err : GoInterface), RET (PairV #id #err); http.errStrOk err ∗
      ⌜∀ x, s = types.idStr x → id = x ∧ err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
