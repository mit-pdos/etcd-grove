/-
`fmt.Sprintf("%+v", md)` of a gRPC `metadata.MD` (Go's standard library): **assumed** (trust
boundary; Perennial's `fmt.Sprintf.spec` leaves a map argument's output arbitrary).

**Why it is true of Go's `fmt`** (go1.27 `fmt/print.go`, `internal/fmtsort`): `%+v` of a
`map[string][]string` prints `map[` then each key in sorted order as `k:[v1 v2 ...]`, separated by
spaces, then `]`; it reads the map and its slices only, never calls a method (`metadata.MD` has no
`String` or `Format` method), and never panics. The output is a function of the map's contents:
`printMD md` (`Api.lean`), injective on printable maps (`printMD_inj`).

Users: 1b's `streamKeyFromCtx` (`client/v3/watch.go`: the watch stream's key), through grpc's
`FromOutgoingContext` (`Grpc.mdAt` of the map). Requested by client-watch and grpc-v3rpc (second
pass, 2026-11-09).
-/
module

public import Spec.fmt.Api
public import Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Fmt

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- **`fmt.Sprintf("%+v", md)`** of a metadata map `m` holding `md` (any fraction, kept): `printMD
md`. -/
def Sprintf_md.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (m : Loc) (dm : DFrac) (md : Grpc.MD),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      sl ↦*{dq} [interface.mkOk google_golang_org.grpc.metadata.MD.ty #m] ∗ Grpc.mdAt m dm md }}
    (App (App (Val (@! fmt.Sprintf)) (Val #go!"%+v")) (Val #sl))
  {{ (s : GoString), RET #s;
      sl ↦*{dq} [interface.mkOk google_golang_org.grpc.metadata.MD.ty #m] ∗ Grpc.mdAt m dm md ∗
      ⌜s = printMD md⌝ }}

end spec

end Fmt
end EtcdGrove
end Perennial
