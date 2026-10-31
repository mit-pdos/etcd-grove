/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Compact.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`) and M2's S3
(`notes/m2-plan.md`): the glue over `processInternalRaftRequestOnce`'s compaction variant
(`specCompact`, the compaction form of the proposal permit), the span and the trace (`EnsureTrace`,
from a context carrying no trace), and the response's header at the store's revision.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Compact
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Tracer__Start
public import Spec.go_opentelemetry_io.otel.trace.WithAttributes
public import Spec.go_opentelemetry_io.otel.attribute.Bool
public import Spec.go_opentelemetry_io.otel.attribute.Int64
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__processInternalRaftRequestOnce
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__GetStartTime
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__SetStartTime
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__InsertStep
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__LogIfLong
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__AddField
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest__GetPhysical
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest__GetRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Rev
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- A compaction's response `Hrsp` with its header `Hhdr` (both owned): the store's revision
(`s.kv.Rev()`) into the header, the trace's field (`Hown0`), up to the deferred calls. -/
local macro "compact_ok_tail" : tactic => `(tactic| (
  -- `s.kv.Rev()`: the store's revision
  ihave %Hkvok := txn.isKV_ok _ E.s E.γ $$ Hkv
  obtain ⟨kty, kvv, Hkveq⟩ := Hkvok
  ihave ⟨#Hko0, #Hs⟩ := txn.isKV_kvOver _ E.s E.γ $$ Hkv
  ihave #Hko : mvcc.kvOver (interface.mkOk kty kvv) E.s $$ []
  · rw [← Hkveq]; iexact Hko0
  ihave #Pmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  rw [Hkveq]
  imod ownToks_0 (GF := GF) E.γ.revs with Hnone
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #Hc0
  wp_bind (App (Val #(methods kty _ kvv)) _)
  iapply mvcc.kvOver_rev_wp kty kvv E.s
  iframe Hko
  wp_apply hRevS E.s v.rv E.γ 0 [] $$ [Hrdr Hnone] as %rev ⟨Hrdr, -, %log, #Hlc, -, %Hl⟩
  · iframe #; iframe
  (try wp_auto)
  -- `trace.AddField(response_revision)`
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fs ⟨Hfs, -⟩
  (try wp_auto)
  wp_apply hAddField _ _ _ _ _ $$ [Hown0 Hfs] as ⟨Hown0, -⟩
  · iframe Hown0 Hfs
    ipureintro
    exact traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil
  (try wp_auto)))

set_option hygiene false in
/-- The return of a compaction's response (after `compact_ok_tail` and the deferred trace log, if
any): the span's `End`, then the postcondition. -/
local macro "compact_ok_post" : tactic => `(tactic| (
  wp_apply HEnd
  (try wp_auto)
  ihave ⟨Hrsp, %Hrplnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hrsp
  iStructNamed Hrsp
  iapply HΦ
  iframe Hlt Hlr Hrd Hrdr
  iunfold compactOutIs
  ileft
  isplitr
  · ipureintro; exact ⟨rfl, Hrplnn⟩
  iexists _, _, log
  iframe Hhdr Hlc
  isplitl
  · iexact Header
  ipureintro; exact ⟨Hl.2.2.1, by simp [Hl.2.2.2]⟩))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.Compact.wp_proof
    (hStart : traceutil.Tracer.Start.spec (GF := GF) (hG := hG))
    (hWithAttr : trace.WithAttributes.spec (GF := GF) (hG := hG))
    (hBool : «attribute».Bool.spec (GF := GF) (hG := hG))
    (hInt64 : «attribute».Int64.spec (GF := GF) (hG := hG))
    (hPhys : CompactionRequest.GetPhysical.spec (GF := GF) (hG := hG))
    (hRev : CompactionRequest.GetRevision.spec (GF := GF) (hG := hG))
    (hLogger : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hPIRRO : EtcdServer.processInternalRaftRequestOnce.specCompact (GF := GF) (hG := hG))
    (hGetStart : traceutil.Trace.GetStartTime.spec (GF := GF) (hG := hG))
    (hSetStart : traceutil.Trace.SetStartTime.spec (GF := GF) (hG := hG))
    (hInsert : traceutil.Trace.InsertStep.spec (GF := GF) (hG := hG))
    (hLogIfLong : traceutil.Trace.LogIfLong.spec (GF := GF) (hG := hG))
    (hRevS : mvcc.store.Rev.spec (GF := GF) (hG := hG))
    (hAddField : traceutil.Trace.AddField.spec (GF := GF) (hG := hG)) :
    EtcdServer.Compact.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr ctx cd p r Hr1
  wp_start as ⟨#Hsrv, #Hsrd, Hlt, Hlr, Hrd, Hrdr, #Hcred, #Hctx, #Htrc, #Hlb, Hreq⟩
  -- (Perennial 25bd32450) the named results are allocated before the defer frame
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, ⟨%tr, #Htr⟩, -⟩, -⟩
  iunfold compactReqIs at Hreq
  icases Hreq with ⟨%rv, Hreq, %Hrv⟩
  ihave ⟨Hreq, %Hpnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hreq
  iStructNamed Hreq
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pattr : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» $$ []
  · iPkgInit
  ihave #Potr : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply hPhys p rv.Physical' _ $$ [Physical] as Physical
  · iframe #; iframe; ipureintro; exact Hpnn
  (try wp_auto)
  wp_apply hBool as %kv1 -
  (try wp_auto)
  wp_apply hRev p rv.Revision' _ $$ [Revision] as Revision
  · iframe #; iframe; ipureintro; exact Hpnn
  (try wp_auto)
  wp_apply hInt64 as %kv2 -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨-, -⟩
  (try wp_auto)
  wp_apply hWithAttr as %opt -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨-, -⟩
  (try wp_auto)
  -- the span, over the caller's context (which carries no trace: `Htrc`, kept by `Start`)
  wp_apply hStart tr ctx cd _ _ $$ [] as %ctx1 %sp ⟨⟨%vs1, #Hctx1t, Hctx1w⟩, #Hctr1, %Hinc1, #Hsp⟩
  · iframe #; iunfold mvcc.txnCtx; iright; iexact Hctx
  ihave #Hctx1 := Hctx1w $$ Hctx
  ihave #Htrc1 := Hctr1 $$ %none Htrc
  iunfold trace.isSpan at Hsp
  icases Hsp with ⟨%si, %Hsi, #HEnd, -, -⟩
  subst Hsi
  (try wp_auto)
  wp_apply time.wp_Now as %now -
  (try wp_auto)
  -- the server's read fields: the logger's and the store's (for `Logger()` and `s.kv.Rev()`)
  ihave #Hsrd' := Hsrd
  iunfold isServerRead at Hsrd'
  icases Hsrd' with ⟨%v, #Hf⟩
  iunfold srvReadFieldsAt at Hf
  icases Hf with ⟨-, -, #HkvA, #Hkv, #HrvA, #Hrv, -, -, -, -, #Hlgf, %Hlgn, -⟩
  wp_apply hLogger s v.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgn
  (try wp_auto)
  -- the trace: a new one (the context carries none)
  wp_apply hEnsure ctx1 _ none false v.lg _ slice.nil $$ []
    as %ctx2 %trc ⟨⟨%Htrcnn, -⟩, Hown0, #Hct2, %Hinc2, %vs2, #Hctx2t, Hctx2w⟩
  · iframe Hctx1t
    isplitr
    · iexact Htrc1
    isplitr
    · unfold traceutil.ownTraceOpt; itrivial
    iapply traceutil.ownFields_nil
  ihave #Hctx2 := Hctx2w $$ Hctx1
  (try wp_auto)
  -- `&pb.InternalRaftRequest{Compaction: r}`, read-only but for its header; the request's revision,
  -- read-only from here on (the caller gave it)
  ipersist Revision
  ihave ⟨Hirr, %Hirrn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$a1»
  iStructNamed Hirr
  ipersist ID
  ipersist Range
  ipersist Put
  ipersist DeleteRange
  ipersist Txn
  ipersist Compaction
  ipersist LeaseGrant
  ipersist LeaseRevoke
  ipersist Alarm
  ipersist LeaseCheckpoint
  ipersist AuthEnable
  ipersist AuthDisable
  ipersist AuthStatus
  ipersist Authenticate
  ipersist AuthUserAdd
  ipersist AuthUserDelete
  ipersist AuthUserGet
  ipersist AuthUserChangePassword
  ipersist AuthUserGrantRole
  ipersist AuthUserRevokeRole
  ipersist AuthUserList
  ipersist AuthRoleList
  ipersist AuthRoleAdd
  ipersist AuthRoleDelete
  ipersist AuthRoleGet
  ipersist AuthRoleGrantPermission
  ipersist AuthRoleRevokePermission
  ipersist ClusterVersionSet
  ipersist ClusterMemberAttrSet
  ipersist DowngradeInfoSet
  ipersist DowngradeVersionTest
  ihave #HirrNo : irrNoHdrIs «$a1_ptr» (irrCompaction rv.Revision') $$ []
  · iunfold irrNoHdrIs
    simp only [irrCompaction, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField,
      apply.compactionIs]
    isplitr
    · ipureintro; exact Hirrn
    isplitr
    · have h0 : (W64 0 : w64) = 0 := by decide
      rw [h0]; iexact ID
    repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
    -- the compaction: the caller's request, at its revision
    isplitr
    · iexists p; iframe #; ipureintro; exact Hpnn
    repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
    iexists _; iframe #; try (ipureintro; simp)
  (try wp_auto)
  -- the proposal, in compaction mode's form (`compactPropOk`)
  -- (review round 1, S2-3) the revision reached, at the request's value
  ihave #Hlb' : srvRevLb E.γ (sint.Z rv.Revision') $$ []
  · rw [Hrv.1]; iexact Hlb
  wp_apply hPIRRO s E ρ ctx2 _ «$a1_ptr» (irrCompaction rv.Revision') rv.Revision' rfl
      (compactPropOk_irrCompaction _ (by rw [Hrv.1]; exact Hr1)) rfl $$ [Hlt Hrd Header]
      as %res %err ⟨Hlt, Hrd, Hres⟩
  · iframe # Hlt Hrd
    iexists _; iexact Header
  (try wp_auto)
  icases Hres with (⟨%Herr, Hcr⟩ | ⟨⟨%Hrn, %Hne⟩, #HaE, -⟩)
  · -- proposed: the apply thread's result, with its trace
    subst Herr
    iunfold compactResultIs at Hcr
    icases Hcr with ⟨%Hresnn, %av, #Hav, Htrr, Hbr⟩
    simp only [show decide (res = null) = false from decide_eq_false Hresnn]
    ihave Hav2 := Hav
    iStructNamed Hav2
    (try wp_auto)
    wp_if_destruct
    · -- no trace from the apply thread: the request's own (`EnsureTrace`'s)
      rw [Hrv.2]
      (try wp_auto)
      icases Hbr with (⟨%Haerr, Hresp⟩ | ⟨%Haerr, #HaE⟩)
      · -- the compaction's response
        icases Hresp with ⟨%rp, %Hrp, Hresp⟩
        rw [Haerr, Hrp]
        (try wp_auto)
        icases Hresp with (%Hrpn | ⟨%cv, Hcv, Hhd⟩)
        · subst Hrpn
          (try wp_auto)
          rename_i rpl
          irename : (rpl ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse) : IProp GF) => Hrsp
          irename : («$r0_ptr» ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader) : IProp GF) => Hhdr
          compact_ok_tail
          compact_ok_post
        · ihave ⟨Hcv, %Hrpnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hcv
          simp only [show decide (rp = null) = false from decide_eq_false Hrpnn]
          (try wp_auto)
          icases Hhd with (%Hhn | ⟨%hv, Hhv⟩)
          · -- no header: a new one
            rw [Hhn]
            (try wp_auto)
            irename : (rp ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse) : IProp GF) => Hrsp
            irename : («$r0_ptr» ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader) : IProp GF) => Hhdr
            compact_ok_tail
            compact_ok_post
          · -- its header
            ihave ⟨Hhv, %Hhnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hhv
            simp only [show decide (cv.Header' = null) = false from decide_eq_false Hhnn]
            (try wp_auto)
            irename : (rp ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse) : IProp GF) => Hrsp
            irename : (cv.Header' ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader) : IProp GF) => Hhdr
            compact_ok_tail
            compact_ok_post
      · -- the compaction's error (the store's `ErrCompacted` or `ErrFutureRev`)
        rcases hae : av.Err' with ei | _
        · ihave #HaEi : applyErrIs (GoInterface.ok ei) $$ []
          · rw [← hae]; iexact HaE
          (try wp_auto)
          wp_apply HEnd
          (try wp_auto)
          iapply HΦ
          iframe Hlt Hlr Hrd Hrdr
          iunfold compactOutIs
          iright
          isplitr
          · ipureintro; rfl
          iexact HaEi
        · exact absurd hae Haerr
    · -- the apply thread's trace: the request's from here on (`EnsureTrace`'s dropped), its log
      -- deferred
      iunfold apply.traceRes at Htrr
      icases Htrr with (%Htn | ⟨%te, Htrc⟩)
      · exact absurd Htn Hif
      wp_apply hGetStart av.Trace' te $$ [$Htrc] as %ast Htrc
      (try wp_auto)
      wp_apply hSetStart av.Trace' te _ $$ [$Htrc] as Htrc
      (try wp_auto)
      wp_apply hInsert av.Trace' te _ _ _ slice.nil $$ [$Htrc] as Htrc
      · isplitl []
        · iapply traceutil.ownFields_nil
        ipureintro; decide
      iclear Hown0
      irename : (traceutil.ownTrace av.Trace' te : IProp GF) => Hown0
      rw [Hrv.2]
      (try wp_auto)
      icases Hbr with (⟨%Haerr, Hresp⟩ | ⟨%Haerr, #HaE⟩)
      · -- the compaction's response
        icases Hresp with ⟨%rp, %Hrp, Hresp⟩
        rw [Haerr, Hrp]
        (try wp_auto)
        icases Hresp with (%Hrpn | ⟨%cv, Hcv, Hhd⟩)
        · subst Hrpn
          (try wp_auto)
          rename_i rpl
          irename : (rpl ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse) : IProp GF) => Hrsp
          irename : («$r0_ptr» ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader) : IProp GF) => Hhdr
          compact_ok_tail
          wp_apply hLogIfLong _ _ _ $$ [$Hown0]
          (try wp_auto)
          compact_ok_post
        · ihave ⟨Hcv, %Hrpnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hcv
          simp only [show decide (rp = null) = false from decide_eq_false Hrpnn]
          (try wp_auto)
          icases Hhd with (%Hhn | ⟨%hv, Hhv⟩)
          · -- no header: a new one
            rw [Hhn]
            (try wp_auto)
            irename : (rp ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse) : IProp GF) => Hrsp
            irename : («$r0_ptr» ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader) : IProp GF) => Hhdr
            compact_ok_tail
            wp_apply hLogIfLong _ _ _ $$ [$Hown0]
            (try wp_auto)
            compact_ok_post
          · -- its header
            ihave ⟨Hhv, %Hhnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hhv
            simp only [show decide (cv.Header' = null) = false from decide_eq_false Hhnn]
            (try wp_auto)
            irename : (rp ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse) : IProp GF) => Hrsp
            irename : (cv.Header' ↦ (_ : go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader) : IProp GF) => Hhdr
            compact_ok_tail
            wp_apply hLogIfLong _ _ _ $$ [$Hown0]
            (try wp_auto)
            compact_ok_post
      · -- the compaction's error (the store's `ErrCompacted` or `ErrFutureRev`)
        rcases hae : av.Err' with ei | _
        · ihave #HaEi : applyErrIs (GoInterface.ok ei) $$ []
          · rw [← hae]; iexact HaE
          (try wp_auto)
          wp_apply hLogIfLong _ _ _ $$ [$Hown0]
          (try wp_auto)
          wp_apply HEnd
          (try wp_auto)
          iapply HΦ
          iframe Hlt Hlr Hrd Hrdr
          iunfold compactOutIs
          iright
          isplitr
          · ipureintro; rfl
          iexact HaEi
        · exact absurd hae Haerr
  · -- not proposed, or no result: the error
    subst Hrn
    rw [Hrv.2]
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      wp_apply HEnd
      (try wp_auto)
      iapply HΦ
      iframe Hlt Hlr Hrd Hrdr
      iunfold compactOutIs
      iright
      isplitr
      · ipureintro; rfl
      iexact HaE
    · exact absurd rfl Hne
end proof

end EtcdGrove
end Perennial
