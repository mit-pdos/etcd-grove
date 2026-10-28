/-
`(*grpc.ClientConn).Target()` (names only; unit P3a): the retry interceptor logs it.
-/
module

public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `conn.Target()` on a dialed connection returns some string (its `target`, fixed since the
dial). -/
abbrev grpc.ClientConn.Target.spec : Prop :=
  ∀ (conn : Loc) (addrs : List GoString) (ics : List GoFunc) (dopts : List GoInterface),
  {{ grpcConn (GF := GF) conn addrs ics dopts }}
    (App (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!!
      go!"Target")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
