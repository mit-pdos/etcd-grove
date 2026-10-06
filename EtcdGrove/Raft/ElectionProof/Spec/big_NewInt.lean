/-
Port of `election_proof/spec_big_NewInt.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvBig

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

/-- `big.NewInt(x)` allocates a `big.Int` holding `x`.

**Trust boundary.** `math/big` is not raft and is not translated (Goose declares only
the name `math.big.NewInt`; there is no `NewInt.impl` and no `FuncUnfold`), so the
call cannot be stepped and this triple stands in for it. Its only consumer is
`lockedRand.Intn`, which is on the RNG path the scope rule allows to be assumed. The
argument is Go's `int64`, i.e. a `w64` read signed. -/
abbrev big.NewInt.spec : Prop :=
  ∀ (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.math.big }}
    (App (Val #(functions math.big.NewInt [])) (Val #x))
  {{ (p : Loc), RET #p; ownBigInt p (sint.Z x) }}

end spec

end EtcdGrove
end Perennial
