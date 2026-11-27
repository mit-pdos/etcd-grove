/-
`createHeaderFields(ctx, cc, authInfo, callHdr)` (the grpc model's `model_transport.go`, grpc-go's
`http2Client.createHeaderFields`; phase 7 S2 core, 2026-11-23, `notes/phase7-plan.md` §0a): the head
of a call's stream. Its vocabulary: `Proof/google_golang_org/grpc/InvHeader.lean`.
-/
module

public import Proof.google_golang_org.grpc.InvHeader

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`createHeaderFields(ctx, cc, authInfo, callHdr)`** for a call header `ch` without call
credentials (`Creds` `nil`: the model's `newClientStream` sets them only from a
`PerRPCCredsCallOption`), whose accepted compressors are `acc` (`""` without), on a connection with
the user agent `ua` and the per-RPC credentials `pcs`, each meeting `hdrCredsOk` with the resource
`R`, and a context with a deadline method (`ctxDeadline`) and outgoing metadata `o` as grpc's transport
reads it (`outRawIs`). It returns `R` and
* `nil` and the fields: the call header's (`callHdrFields`), the timeout's (`timeoutFieldsOk`), those
  of the maps `cms` the credentials returned, one per credential, each meeting `Q`, merged
  (`credsFieldsOk`), and the outgoing metadata's (`outFieldsOk`); the maps' fields in some order of
  their keys;
* or an error: from the credentials (theirs, or a status error made of it), a pair `ValidatePair`
  refuses, or a deadline already passed. -/
abbrev grpc.createHeaderFields.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cc : Loc) (authInfo : GoInterface) (chp : Loc)
    (ch : google_golang_org.grpc.callHdr) (dq : DFrac) (acc ua : GoString) (pcsl : GoSlice)
    (pcs : List GoInterface) (dqc : DFrac) (Ok : IProp GF → Prop)
    (Q : GMap GoString GoString → IProp GF) (R : IProp GF)
    (o : Option (GMap GoString (List GoString) × List (List GoString))),
  ch.Creds' = GoInterface.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ chp ↦{dq} ch ∗
      (⌜ch.AcceptedCompressors' = null ∧ acc = []⌝ ∨ ch.AcceptedCompressors' ↦□ acc) ∗
      structFieldRef google_golang_org.grpc.connectOptions go!"PerRPCCredentials"
        (structFieldRef google_golang_org.grpc.dialOptions go!"copts"
          (structFieldRef google_golang_org.grpc.ClientConn go!"dopts" cc)) ↦{dqc} pcsl ∗ pcsl ↦*{dqc} pcs ∗
      structFieldRef google_golang_org.grpc.connectOptions go!"UserAgent"
        (structFieldRef google_golang_org.grpc.dialOptions go!"copts"
          (structFieldRef google_golang_org.grpc.ClientConn go!"dopts" cc)) ↦{dqc} ua ∗
      ([∗list] pc ∈ pcs, hdrCredsOk (GF := GF) pc Ok Q) ∗ ⌜Ok R⌝ ∗ R ∗
      ctxDeadline (GF := GF) ctx ∗ outRawIs (GF := GF) ctx o }}
    (App (App (App (App (Val (@! google_golang_org.grpc.createHeaderFields))
      (Val #(GoInterface.ok ctx))) (Val #cc)) (Val #authInfo)) (Val #chp))
  {{ (hsl : GoSlice) (err : GoInterface), RET (PairV #hsl #err);
      chp ↦{dq} ch ∗ structFieldRef google_golang_org.grpc.connectOptions go!"PerRPCCredentials"
        (structFieldRef google_golang_org.grpc.dialOptions go!"copts"
          (structFieldRef google_golang_org.grpc.ClientConn go!"dopts" cc)) ↦{dqc} pcsl ∗
      pcsl ↦*{dqc} pcs ∗ structFieldRef google_golang_org.grpc.connectOptions go!"UserAgent"
        (structFieldRef google_golang_org.grpc.dialOptions go!"copts"
          (structFieldRef google_golang_org.grpc.ClientConn go!"dopts" cc)) ↦{dqc} ua ∗ R ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hs : List google_golang_org.grpc.headerField)
          (cms : List (GMap GoString GoString)) (tfs afs ofs : List (GoString × GoString)),
        hsl ↦* hs ∗ ownSliceCap google_golang_org.grpc.headerField hsl (DFrac.own 1) ∗
        ⌜hfPairs hs = grpcHdr.callHdrFields ch acc ua ++ tfs ++ afs ++ ofs ∧
          grpcHdr.timeoutFieldsOk tfs ∧ cms.length = pcs.length ∧
          (∀ cm ∈ cms, grpcHdr.credKeysOk cm) ∧ grpcHdr.credsFieldsOk cms afs ∧
          grpcHdr.outFieldsOk o ofs⌝ ∗
        [∗list] cm ∈ cms, □ Q cm) ∨
       ⌜err ≠ GoInterface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
