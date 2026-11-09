/-
`types.IDFromString` (`client/pkg/v3/types/id.go`).

Users: the server (membership, rafthttp: 2e, 2f).

Proof sketch: `strconv.ParseUint(s, 16, 64)` (trusted): the hexadecimal string of `x` parses to `x`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/pkg/v3/types/IDFromString.lean`.

Margin: other strings' results not described.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Types

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

/-- `IDFromString(s)`: `x` for `s = idStr x`. -/
def IDFromString.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.types.IDFromString)) (Val #s))
  {{ (id : w64) (err : GoInterface), RET (PairV #id #err);
      ⌜∀ x, s = idStr x → id = x ∧ err = GoInterface.nil⌝ }}

end spec

end Types
end EtcdGrove
end Perennial
