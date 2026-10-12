/-
`v3rpc.checkIntervals` (`key.go`), over the interval tree's contract. Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvKV.lean` and `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`checkIntervals(reqs)`** of the operations `us`: as `ivCheck` computes it. On `nil`, the
map's keys are `ivCheck`'s puts and the tree (an owned `*intervalTree`) holds, in some order,
`ivCheck`'s deletes; otherwise `ErrGRPCDuplicateKey`. -/
abbrev v3rpc.checkIntervals.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (us : List v3rpc.ReqOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ sl ↦*□ ps ∗ v3rpc.reqOpsIs ps us }}
    (App (Val (@! v3rpc.checkIntervals)) (Val #sl))
  {{ (m : Loc) (t err : GoInterface), RET (PairV (PairV #m #t) #err);
      match v3rpc.ivCheck us with
      | some (puts, ds) => ⌜err = GoInterface.nil⌝ ∗
          (∃ M : GMap GoString Unit, m ↦$ M ∗ ⌜∀ k, (M !! k).isSome = true ↔ k ∈ puts⌝) ∗
          (∃ (tl : Loc) (L : List adt.Entry),
            ⌜t = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tl⌝ ∗
            adt.ownIvt tl L ∗ ⌜(L.map Prod.fst).Perm ds⌝)
      | none => txn.errVarIs v3rpc.CheckErr.duplicateKey.var err }}

end spec

end EtcdGrove
end Perennial
