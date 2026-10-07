/- Port of election_proof/spec_big_Int__Int64.v (feb5c73d4). -/
import EtcdGrove.Raft.InvBig

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `p.Int64()` reads back a `big.Int` that fits in an `int64`.

**Trust boundary**, like `big.NewInt.spec`: `math/big` is not translated. -/
abbrev big.Int.Int64.spec : Prop :=
  ∀ (p : Loc) (z : Int),
  - 2 ^ 63 ≤ z ∧ z < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.math.big ∗ ownBigInt p z }}
    (App (Val (p @!! go.GoType.PointerType math.big.Int'.ty @!! go!"Int64")) (Val #()))
  {{ RET #(W64 z); ownBigInt p z }}

end spec

end EtcdGrove
end Perennial
