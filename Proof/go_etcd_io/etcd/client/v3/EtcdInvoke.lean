/-
**`ClientConn.Invoke` on an etcd client's connection** (unit P3a, 2026-10-14): the contract of a
unary call through the connection `clientv3.New` dials (one interceptor, the retry interceptor;
`isEtcdConn`), derived from grpc's generic contract (`grpc.ClientConn.Invoke.spec`, the axiom: the
interceptor chain over grpc's one-attempt `invoke`) and the interceptor's contract
(`etcdInterceptorOk`, what `Client.unaryClientInterceptor` returns, proved). It was the axiom
`grpc.ClientConn.Invoke.wp_proof` of unit C1 and the generic gRPC specification, with the retry
interceptor inside the boundary. Lean-first (no Rocq counterpart); the design:
`notes/decisions.md`, "The retry interceptor proved: the gRPC boundary below it".
-/
module

public import Spec.google_golang_org.grpc.ClientConn__Invoke
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk errCellOk)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`conn.Invoke(ctx, method, in, out, opts...)` on an etcd client's connection** (`isEtcdConn
conn addr`: the retry interceptor installed), of any unary method registered with a spec
(`isGrpcRpcs addr method Spec`), for the request `in` (the sender's message at the model `m`,
`Req.send`: marshaling writes its size cache) and a zero reply `out` (`Rep.blank`), with the
caller's `□ ▷ Spec m Φ` (persistent: the request may be delivered several times, the retry
interceptor's attempts; urpc's `wp_Client__Call_pred`). What it returns:

* `nil`: a run of the method's handler on a copy of the request answered `(resp, nil)`, and `out`
  holds the reply's copy of `resp`'s message (`Rep.recv out m'`) with the run's `Φ m'`. Other runs
  may have happened (failed attempts the retry interceptor retried: an attempt that failed with a
  gRPC `Canceled` or `DeadlineExceeded` while `ctx` is not done is retried whatever the method,
  `issues/etcd-client-retry-put-ctx-error.md`); the reply is the last one's.
* an error (a client error, `clientErr`, that grpc's `status` accepts, `statusErrOk`): nothing
  about whether, or how often, the handler ran, nor about `out`.

The request comes back (`Req.send inp m`), and the options (`callOptsOk`: none writes the caller's
memory) stay read-only. The request's encoding is below `grpcMsgMax` (`Req.wireLen`, since
2026-10-30: the attempt contract's premise, `grpcInvokerOk`). (Unit C1's axiom, with `isGrpcConn` for `isEtcdConn` and without
`statusErrOk`; now `etcdConn_Invoke`, a theorem.) -/
abbrev etcdConn.Invoke.spec : Prop :=
  ∀ (conn : Loc) (addr : List GoString) (method : GoString) (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep)
    (m : Req.M) (Φ : Rep.M → IProp GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (inp out : Loc) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isEtcdConn conn addr ∗
      isGrpcRpcs addr method Spec ∗ reqPre conn method addr vs (Spec m Φ) ∗ ctxOk ctx cd ∗ Req.send inp m ∗
      Rep.blank out ∗ opts ↦*□ vs ∗ callOptsOk vs ∗ ⌜Req.wireLen m < grpcMsgMax⌝ }}
    (App (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"Invoke"))
      (Val #(GoInterface.ok ctx))) (Val #method))
      (Val #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)))
      (Val #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface)))
      (Val #opts))
  {{ (err : GoInterface), RET #err;
      Req.send inp m ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Φ m') ∨
        (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ statusErrOk err ∗ errCellOk err)) }}

/-- **`conn.Invoke` on an etcd client's connection, for a metadata-indexed spec** (the auth plan's
E3zc): `etcdConn.Invoke.spec`'s, for a method registered with the metadata-indexed `Spec`
(`isGrpcRpcsMd`) and the caller's request precondition at every metadata an attempt of the call
may deliver (`attemptPre`: the retry interceptor's attempts are on `withVersion(ctx)`). A plain
spec's is `etcdConn.Invoke.spec` (`etcdConn_Invoke`, at `GrpcSpec.md`). -/
abbrev etcdConn.InvokeMd.spec : Prop :=
  ∀ (conn : Loc) (addr : List GoString) (method : GoString) (Req Rep : ProtoMsg GF)
    (Spec : GrpcSpecMd Req Rep) (m : Req.M) (Φ : Rep.M → IProp GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (inp out : Loc) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isEtcdConn conn addr ∗
      isGrpcRpcsMd addr method Spec ∗
      reqPre conn method addr vs (attemptPre conn (GoInterface.ok ctx) Spec m Φ) ∗ ctxOk ctx cd ∗
      Req.send inp m ∗ Rep.blank out ∗ opts ↦*□ vs ∗ callOptsOk vs ∗ ⌜Req.wireLen m < grpcMsgMax⌝ }}
    (App (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"Invoke"))
      (Val #(GoInterface.ok ctx))) (Val #method))
      (Val #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)))
      (Val #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface)))
      (Val #opts))
  {{ (err : GoInterface), RET #err;
      Req.send inp m ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Φ m') ∨
        (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ statusErrOk err ∗ errCellOk err)) }}

/-- **`Invoke` on an etcd client's connection, for a metadata-indexed spec** (`etcdConn.InvokeMd.spec`), from grpc's contract:
the chain is the one interceptor, called with an invoker that behaves as grpc's `invoke`, which
meets the attempt contract (`grpcInvokerOk_of_wp`); the interceptor's contract does the rest. -/
theorem etcdConn_InvokeMd (wp_Invoke : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)) :
    etcdConn.InvokeMd.spec (GF := GF) (hG := hG) := by
  intro conn addr method Req Rep Spec m Φ ctx cd inp out opts vs
  iintro %Ψ ⟨#Hg, #Hconn0, #Hrpc, Hpre, #Hctx, Hsend, Hblank, #Hopts, #Hok, #Hsz⟩ HΨ
  iunfold reqPre at Hpre
  icases Hpre with (#Hpre | ⟨%Hw, Hpre⟩)
  · -- any number of attempts
    iunfold isEtcdConn at Hconn0
    icases Hconn0 with ⟨%ic, #Hgc, #Hic, -⟩
    iapply (wp_Invoke conn addr [ic] [] (GoInterface.ok ctx) method
      (interface.mkOk (go.GoType.PointerType Req.ty) #inp)
      (interface.mkOk (go.GoType.PointerType Rep.ty) #out) opts vs Ψ)
    iframe #
    iintro %inv %opts' #Hinv #Hopts'
    simp only [List.nil_append, chainWP]
    iintro %inv' #Hinv'
    ihave #Hinv'' := grpcInvokerOk_of_wp conn addr inv inv' $$ [Hinv Hinv']
    · iframe #
    iunfold etcdInterceptorOk at Hic
    iapply Hic $$ [Hsend Hblank] HΨ
    iframe #
    iframe
  · -- (2026-10-21, D29) a write on a refusal-free connection, with scalar call options: never
    -- retried
    iunfold isEtcdConn at Hconn0
    icases Hconn0 with ⟨%ic, #Hgc, -, #Hic⟩
    iapply (wp_Invoke conn addr [ic] [] (GoInterface.ok ctx) method
      (interface.mkOk (go.GoType.PointerType Req.ty) #inp)
      (interface.mkOk (go.GoType.PointerType Rep.ty) #out) opts vs Ψ)
    iframe #
    iintro %inv %opts' #Hinv #Hopts'
    simp only [List.nil_append, chainWP]
    iintro %inv' #Hinv'
    ihave #Hinv'' := grpcInvokerOk_of_wp conn addr inv inv' $$ [Hinv Hinv']
    · iframe #
    iunfold etcdInterceptorOkW at Hic
    iunfold etcdInterceptorOkM at Hic
    iapply Hic $$ [Hsend Hblank Hpre] HΨ
    iframe #
    iframe
    simp only [modePre]
    iframe
    ipureintro; exact Hw

/-- **`Invoke` on an etcd client's connection** (`etcdConn.Invoke.spec`): `etcdConn_InvokeMd` at the
plain spec's metadata-indexed form (`GrpcSpec.md`, `isGrpcRpcs_md`, `attemptPre_md`). -/
theorem etcdConn_Invoke (wp_Invoke : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)) :
    etcdConn.Invoke.spec (GF := GF) (hG := hG) := by
  intro conn addr method Req Rep Spec m Φ ctx cd inp out opts vs
  iintro %Ψ ⟨#Hg, #Hconn0, #Hrpc, Hpre, #Hctx, Hsend, Hblank, #Hopts, #Hok, #Hsz⟩ HΨ
  iapply (etcdConn_InvokeMd wp_Invoke conn addr method Req Rep (GrpcSpec.md Spec) m Φ ctx cd inp out
    opts vs) $$ [Hpre Hsend Hblank] HΨ
  iframe #
  iframe
  isplitr
  · iapply (isGrpcRpcs_md addr method Spec).1 $$ Hrpc
  iapply (reqPre_mono conn method addr vs _ _ (attemptPre_md conn (GoInterface.ok ctx) Spec m Φ)) $$ Hpre

end spec

end EtcdGrove
end Perennial
