/-
`(*clientv3.kv).Get(ctx, key, opts...)` (`client/v3/kv.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVService

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.Get(ctx, key, opts...)` on a `*kv` of etcd's KV `γ` (`isKv`, D43): `OpGet(key, opts...)`
(`opts`: the models of the Go options `opts...` (`WithPrevKV()`, ...), one transformer of the operation each, `optsAt`
ties the slice `opts_sl` of their closures to them; `[]` for none) (options that do not panic, keep the range type, and may need a resource `R`, given back:
`optsAtRes`; any sort option, checked against `etcdserverpb`'s
enumerations, `sortNamesOk`), then `kv.Do`, with the caller's persistent atomic read of `γ`'s
state (a read may be answered by any member, and again) or, `Q` trivial, none; the error through
`ContextError`: `R` back, and `nil` and the reply's message `m` with a state `σ` (the read
update's, `□ Q σ`, if linearizable) at whose current revision the reply's header is, the reply's
key-values and count the selection of `σ`'s store at the revision the range reads (`readRev`: the
one asked, at most the current, or the current), `σ` a well-formed small log's state (`kvLogOk`,
D47); or a client error (`kvErr`) and no reply. -/
abbrev kv.Get.spec : Prop :=
  ∀ (kv : Loc) (γ : KVNames) (dup : Bool) (ctx : GoInterfaceOk)
    (ctx_desc : context.ContextDesc (IProp GF)) (key : GoString) (opts_sl : GoSlice)
    (opts : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv kv γ dup ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAtRes opts_sl opts R ∗ R ∗
      sortNamesIf (opGetModel key opts).base.sortSet ∗
      ⌜¬ opGetPanics opts ∧ (opGetModel key opts).t = W64 1⌝ ∗
      □ (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜(rangeWireOf (opGetModel key opts)).base.serializable = false⌝ ∗
        AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>)) }}
    (App (App (App (Val (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Get")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      R ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
          (if (rangeWireOf (opGetModel key opts)).base.serializable then iprop(True) else iprop(□ Q σ)) ∗
          ⌜sint.Z (rangeWireOf (opGetModel key opts)).base.rev ≤ (σ.rev : Int) ∧
            txn.srvRangeOk (rangeWireOf (opGetModel key opts)) (σ.at (σ.readRev (rangeWireOf (opGetModel key opts)).base.rev)).kvs m.kvs m.more ∧
            m.count = txn.srvCount (rangeWireOf (opGetModel key opts)) (σ.at (σ.readRev (rangeWireOf (opGetModel key opts)).base.rev)).kvs true ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧ σ.rev + 3 < 2 ^ 63 ∧ kvLogOk σ⌝) ∨
        (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err)) }}

end spec

end EtcdGrove
end Perennial
