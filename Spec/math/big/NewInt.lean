/-
Port of election_proof/spec_big_NewInt.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvBig

@[expose] public section

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

/-- `big.NewInt(x)` allocates a `big.Int` holding `x`. The argument is Go's `int64`,
i.e. a `w64` read signed. Proved in Perennial (`math.big.wp_NewInt`); its only consumer
is `lockedRand.Intn`. -/
abbrev big.NewInt.spec : Prop :=
  ∀ (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.math.big }}
    (App (Val #(functions math.big.NewInt [])) (Val #x))
  {{ (p : Loc), RET #p; ownBigInt p (sint.Z x) }}

end spec

end EtcdGrove
end Perennial
