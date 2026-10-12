/-
Package initialization for etcd's gRPC KV service (`server/v3/etcdserver/api/v3rpc`: the
handlers of `key.go`, the request checks, the response header, `togRPCError`). Lean-first (no
Rocq counterpart); plan: `notes/decisions.md`, "The request path".

Every package it imports already has its instance: the server's (`etcdserver/BaseApply.lean`:
`etcdserver`, with the request path's facts `srvInit`), the apply package's and the txn
package's, the cache's (`etcdserverpb`, `rpctypes`, grpc's `codes` and `status`), the interval
tree's (`pkg/v3/adt/Base.lean`) and Perennial's (`context`, `errors`).

As elsewhere, the package fact is an assumption about package initialization, not proved from
`initialize'` (which runs the axiomatized initializers of the package's variables, the error
map among them). `v3rpcInit` states what the translated code reads of package variables: its
own error map `toGRPCErrorMap` (a `map[error]error` literal over sixty error variables of seven
packages, names only: a fixed map whose values are non-nil errors), and the `rpctypes` errors
the checks return, each a fixed non-nil error (stated here rather than in `rpctypes`' facts,
which the cache's proofs destructure by position).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc

/-- The package variable `g` holds a fixed non-nil error (persistent). -/
def errVarSet (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e)

instance errVarSet_persistent (g : GoString) : Persistent (errVarSet (GF := GF) g) := by
  unfold errVarSet; infer_instance

/-- **The gRPC error map** (`toGRPCErrorMap`, `util.go`): a fixed map from the server's errors to
gRPC errors, every value a non-nil error (each an `rpctypes.ErrGRPC*`/`ErrTooManyRequests`/
`ErrMemberNotEnoughStarted`, all `status` errors). Which keys it has is left open: `togRPCError`
returns the mapped error for a key, or `status.Error(codes.Unknown, err.Error())`, both non-nil,
and the handlers' specs say no more of an error. -/
def grpcErrMap : IProp GF :=
  iprop(∃ (mp : Loc) (M : GMap GoInterface GoInterface),
    globalAddr toGRPCErrorMap ↦□ mp ∗ mp ↦$□ M ∗
    ⌜∀ k v, M !! k = some v → v ≠ GoInterface.nil⌝)

/-- **The `rpctypes` errors the checks return** (`checkRangeRequest`, ..., `checkIntervals`,
`checkRequestOp`), each a fixed non-nil error. -/
abbrev checkErrVars : IProp GF :=
  iprop(errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCEmptyKey ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidSortOption ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCValueProvided ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseProvided ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTooManyOps ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDuplicateKey ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCKeyNotFound)

/-- **The protobuf enumerations' name maps** `checkRangeRequest` looks the sort order and target
up in (`etcdserverpb.RangeRequest_SortOrder_name`, `RangeRequest_SortTarget_name`: generated
`map[int32]string` literals, names only here): fixed maps whose keys are the enumerations'
values, `NONE`, `ASCEND`, `DESCEND` (`0` to `2`) and `KEY`, `VERSION`, `CREATE`, `MOD`, `VALUE`
(`0` to `4`). Stated here rather than in `etcdserverpb`'s facts (the cache's). -/
def sortNameMaps : IProp GF :=
  iprop((∃ (mp : Loc) (M : GMap w32 GoString),
      globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest_SortOrder_name ↦□ mp ∗
      mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 2⌝) ∗
    (∃ (mp : Loc) (M : GMap w32 GoString),
      globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest_SortTarget_name ↦□ mp ∗
      mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 4⌝))

/-- **`context.Canceled` is a pointer error** (`errors.New("context canceled")`, Perennial's
`context.wp_initialize'`, whose package fact keeps only that it is a typed error): what
`errors.Is(err, context.Canceled)` (`togRPCError`) needs of its target (`errors.wp_Is`).
Stated here, an assumption about `context`'s initialization as the rest. -/
def ctxCanceledPtr : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr _root_.Perennial.context.Canceled ↦□ GoInterface.ok e ∗
    ⌜_root_.Perennial.errors.IsPointerError e⌝)

/-- The package's facts: the error map, the checks' errors, the sort-name maps and
`context.Canceled`. -/
abbrev v3rpcInit : IProp GF := iprop(grpcErrMap ∗ checkErrVars ∗ sortNameMaps ∗ ctxCanceledPtr)

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc :=
  define_is_pkg_init v3rpcInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc

end init

end Perennial
