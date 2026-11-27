/-
**A real `*kv` meets the recipes' get contract at the server's model** (the vertical slice's unit
V2b, 2026-10-14, after slice-v2's; `InvServerKV.lean`). Lean-first, no Rocq counterpart.

`isEtcdKVTodo_of_kv`: a `*kv` over a connection to a gRPC server at `addr` where etcd's `Range` is
registered (`kvObjAt api addr`, `etcd_kv_served`) meets `isEtcdKVTodo` (`cache/v3/InvEtcdTxn.lean`)
at `v3rpc.etcdModelOfServer E`, for a non-empty prefix. The call is `kv.Get` at `context.TODO()`
(`todo_ctx`), the request handed the read side's first floor as its floor
(`floor0_of_read`), the committed index `0` and, for a linearizable get, the client's read update
(`kvAnyAu`, unit W-M3) whose result is the floor of the caller's `etcdReached lo`
(`nx_of_reached`; strict M1: the server's raft witness `E.Nx`) at the state read:
linearizability. The reply's log is small by its receipt (`srvLogCert_logOk`, at
`receiptBound GF ≤ 2 ^ 62`, a premise since strict M1: until then the read side's `storeSmall`).

* **The wire's get is the `Op`'s** (`wire_fields`, `wire_rangeSel`, `wire_sort`): the request
  `kv.Do` sends (`rangeWireOf o`) has the `Op`'s key, range, revision, limit, filters, flags; its
  sort fields are the `int32` values of the `Op`'s, the `Op`'s own for the values `getExact`
  allows, so the effective order and target are the `Op`'s.
* **The server answers as the model says** (`wire_not_cutEarly`, `wire_fastKeysOnly`,
  `wire_answer`): for a `getExact` get, `txn.srvRangeOk_rangeKvsOk` applies, the leases are not
  zeroed, and `More` is the model's.
* **A prefix get lists the state under the prefix** (`prefix_answer`, for a non-empty prefix:
  `isPrefixGet []` reads from `"\x00"` on and would leave out an empty key, which the server's
  model does not exclude; hence `pfx ≠ []`).

The pure facts (the three bullets) are in `ServerKVGetDefs.lean` (2026-11-26), for defs and proof modules.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.client.v3.LinkMembers
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas
public import Proof.go_etcd_io.etcd.client.v3.ServerKVGetDefs

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil errStrOk_of_statusErrOk)

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem sortNamesIf_of_ok (b : Bool) : sortNamesOk (GF := GF) ⊢ sortNamesIf b := by
  iintro #H
  unfold sortNamesIf
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [↓reduceIte]; iexact H

/-- **A real `*kv`'s get at the server's model** (the core of `isEtcdKVTodo_of_kv` and
`isEtcdKVE_of_kv_r`, at any context `ci` the client's contracts accept: `ctxOk`, `ctxErrClient`), for
an exact get and a non-empty prefix (see the file header). Premises: the registration of etcd's
`Range` at `addr`, the server's read side (`isServerRead`: the first floor, the KV invariants), the receipts' bound,
`etcdserverpb`'s sort enumerations if the get sorts (`sortNamesIf`, 2026-10-20), and (unit W-M3)
the client's updates at the read names at the ranges (`kvRangeAu E γr`, 2026-10-20: a linearizable get's floor is its read
update's result, at the state of the log read). -/
theorem kv_get_server_r (api : Loc) (addr : List GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (pfx : GoString) (hpfx : pfx ≠ [])
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) (lo : w64)
    (Hnp : ¬ opGetPanics gs) (Ht : (opGetModel key gs).t = W64 1)
    (Hx : (opGetModel key gs).getExact) (Hsz : opSizeOk (opGetModel key gs))
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗ kvRegs (srvsAt addr E γr cid mid) ∗
        sortNamesIf (opGetModel key gs).base.sortSet ∗ kvRangeAu E γr ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
        etcdReached (EM := v3rpc.etcdModelOfServer E γr false) lo }}
      (App (App (App (Val #(methods (kvIfaceOf api).ty go!"Get" (kvIfaceOf api).v))
        (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (
        R ∗ kvGetResultC (EM := v3rpc.etcdModelOfServer E γr false) pfx lo (opGetModel key gs) resp err ∗
        getRespMore (EM := v3rpc.etcdModelOfServer E γr false) pfx (opGetModel key gs) resp err ∗
        statusErrOk err) }} := by
  iintro %Φ ⟨#Pc, Hlt, #Hsrd, #Hkv, #Hrpc, #Hsi, #Hany, #Hctx, #Hce, #Hopts, HR, #Hlo⟩ HΦ
  -- the floor (unit W-M3): a witnessed log longer than `lo` (or `lo ≤ 0`), and, for a
  -- linearizable get, the client's read update whose result is that the state read is at least
  -- that log
  ihave #Hinvs := srvKVInvs_of_read s E γr $$ Hsrd
  ihave %HNx := srvKVInvs_nx E γr $$ Hinvs
  imod (nx_of_reached E γr lo) $$ [$Hinvs $Hlo] with ⟨%l, Hcl, %Hll⟩
  ihave ⟨%F, #HF, %HlF⟩ := floor0_of_read s E γr $$ Hsrd
  iunfold kvRangeAu at Hany
  imod Hany $$ %(rangeWireOf (opGetModel key gs)) %l Hcl with #Hau
  ihave ⟨%Q, #Hdq, #HQf⟩ : iprop(∃ Q : KVState → IProp GF,
      (⌜Q = fun _ => iprop(True)⌝ ∨
        (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) ∗
      □ (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ -∗
        ∀ σ, Q σ -∗ ⌜l.length ≤ σ.rev + 1⌝)) $$ []
  · cases hs : (rangeWireOf (opGetModel key gs)).base.serializable
    · iexists (fun σ => iprop(⌜l.length ≤ σ.rev + 1⌝))
      isplitl
      · iright
        isplitr; · ipureintro; rfl
        iapply kvOpAu_range $$ Hau
      · iintro !> - %σ H; iexact H
    · iexists (fun _ => iprop(True))
      isplitl
      · ileft; ipureintro; rfl
      · iintro !> %h; cases h
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  ihave #Hc0 : committedAtLeast γr (W64 0) $$ []
  · unfold committedAtLeast; ileft
    rw [show uint.nat (W64 0) = 0 from rfl]
    iexact H0
  ihave #Hus := rangeUpd_srvsAt addr E γr cid mid (rangeWireOf (opGetModel key gs)) Q $$ Hdq
  iapply wp_fupd
  iapply (v3.kv.wp_GetM api (srvsAt addr E γr cid mid) ci cd key sl gs R (W64 0) F Q) $$ [Hlt HR]
  · iframe #
    iframe Hlt
    iframe
    isplitl []
    · iapply isKV_srvsAt $$ [Hkv Hrpc]; iframe #
    isplitl []
    · ipureintro; exact ⟨Hnp, Ht⟩
    isplitl []; rotate_left
    · ipureintro; exact Hsz
    iapply knownAt_srvsAt $$ []
    iframe #
  inext
  iintro %resp %err ⟨Hlt, HR, Hout, -⟩
  imod rangeCallOut_persist _ _ _ $$ Hout with Hout
  imodintro
  iapply HΦ
  iframe Hlt
  iframe HR
  iunfold rangeCallOutP at Hout
  icases Hout with (⟨%Herr, %m, #Hm, #Hq⟩ | ⟨%Herr, #Hse, -⟩)
  ihave #Hq := rangeAns_srvsAt addr E γr (W64 0) cid mid F _ Q m $$ Hq
  rotate_left
  · isplitl
    · unfold kvGetResultC; ileft; ipureintro; exact Herr.1
    isplitl
    · unfold getRespMore; ileft; ipureintro; exact Herr.1
    iexact Hse
  iunfold rangeReplyOk at Hq
  icases Hq with ⟨%log, #Hcert, %Hk, %Hlog, -, #HQl⟩
  obtain ⟨h2, h3, hrev, -, -, -, -, hsrv, hFl⟩ := Hlog
  ihave %Hlok := srvLogCert_logOk E log hrb $$ Hcert
  ihave #Hkn := srvLogCert_kvNx E γr log HNx $$ Hcert
  iunfold srvLogCert at Hcert
  icases Hcert with ⟨#Hcert, -, -, -⟩
  -- the floor at the state read (a linearizable get's)
  ihave %Hfl : ⌜(opGetModel key gs).base.serializable = false →
      sint.Z lo ≤ (log.length : Int) - 1⌝ $$ []
  · by_cases hs : (rangeWireOf (opGetModel key gs)).base.serializable = false
    · ihave #Himp := HQf $$ %hs
      simp only [hs, Bool.false_eq_true, ↓reduceIte]
      icases HQl with ⟨%ltq, -, #HQl⟩
      ihave %h := Himp $$ %(kvStateOf log ltq) HQl
      ipureintro; intro _
      simp only [kvStateOf_rev, kvStateOf_kvs] at h
      omega
    · ipureintro; intro h
      exact absurd (by rw [(wire_fields _).2.2.2.2.2.2.1]; exact h) hs
  iclear HQl
  iunfold rangeRespMsg at Hm
  icases Hm with ⟨%Hrn, %h, %ksl, %ps, #Hh, #Hhf, #Hksl, #Hps, #Hkvs, #Hmore, -⟩
  iunfold hdrFull at Hhf
  icases Hhf with ⟨%Hhn, -, -, #Hrev, -, -⟩
  rw [hrev] at hsrv; rw [hrev]
  have hr : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by word
  ihave #Hreach := v3rpc.etcdReached_of_nx E γr false log (W64 ((log.length : Int) - 1)) (by omega)
    $$ Hkn
  ihave ⟨#Hst, %Hwf⟩ := v3rpc.etcdState_of_nx_last E γr false log pfx h2 h3 Hlok.1 Hlok.2.2 Hk
    $$ Hkn
  ihave #Hgr : getRespRev resp (W64 ((log.length : Int) - 1)) $$ []
  · unfold getRespRev
    iexists h
    iframe #
    ipureintro; exact Hhn
  have hst : (opGetModel key gs).base.rev = W64 0 →
      mvcc.stateAt log (sint.nat (mvcc.rangeRev (W64 ((log.length : Int) - 1))
        (rangeWireOf (opGetModel key gs)).base.rev)) = mvcc.stateAfter log := by
    intro h0
    rw [(wire_fields _).2.2.1, h0]
    simp only [mvcc.rangeRev, show sint.Z (W64 0) = 0 from rfl, Int.le_refl, ↓reduceIte]
    exact txn.stateAt_lastRev log (by intro h; simp [h] at h2) (by omega)
  generalize opGetModel key gs = o at Hx hst hsrv Hfl ⊢
  isplitl
  · unfold kvGetResultC
    iright
    isplitl; · ipureintro; exact Herr
    iexists (W64 ((log.length : Int) - 1))
    iframe Hgr Hreach
    isplitr
    · rw [show (v3rpc.etcdModelOfServer E γr false).etcdReadAt = v3rpc.srvReadAt E from rfl]
      unfold v3rpc.srvReadAt
      iexists log
      iframe Hcert
      ipureintro; omega
    isplitr
    · unfold etcdHasState
      iexists (txn.underPfx pfx (mvcc.stateAfter log))
      iexact Hst
    isplitl
    · ipureintro
      refine ⟨fun h => ?_, by omega⟩
      have := Hfl h
      omega
    ihave #Hpk := kvPtrsAt_of_kvsIs ps m.kvs $$ Hkvs
    split
    · rename_i hp
      have h0 := isPrefixGet_rev pfx o hp
      have ha := wire_answer o Hx _ _ _ hsrv
      rw [hst h0] at ha
      obtain ⟨hkv, -, -⟩ := prefix_answer pfx o hp hpfx _ _ ha.1
      iunfold txn.kvsIs at Hkvs
      icases Hkvs with ⟨%Hlen, #Hall⟩
      iexists ((m.kvs.map EtcdKv.key).zip ps)
      isplitl
      · unfold isEtcdKvs
        iexists (txn.underPfx pfx (mvcc.stateAfter log))
        iframe Hst
        isplitl
        · ipureintro
          rw [← hkv, List.map_fst_zip (by simp; omega)]
        isplitl
        · ipureintro; exact Hwf
        unfold kvValsAt
        iintro !> %i %e %w %He %Hw
        rw [← hkv] at Hw
        have h1 := zip_getElem?_snd _ _ i e He
        ihave Hkw := Hall $$ %i %e.2 %w %h1 %Hw
        iapply kvValAt_of_kvIs; iexact Hkw
      · unfold getRespKvs
        iexists ksl
        iframe Hksl
        rw [List.map_snd_zip (by simp; omega)]
        iexact Hps
    · unfold getRespRange
      split
      · rename_i hc
        have ha := wire_answer o Hx _ _ _ hsrv
        rw [hst hc.1] at ha
        iexists (txn.underPfx pfx (mvcc.stateAfter log)), ksl, ps, m.kvs
        iframe #
        ipureintro
        refine ⟨Hwf, ?_⟩
        rw [v3rpc.rangeSel_underPfx pfx _ o hc.2]
        exact ha.1
      · itrivial
  isplitl
  · unfold getRespMore
    iright
    iexists (W64 ((log.length : Int) - 1)), m.more
    iframe Hgr Hmore
    split
    · rename_i hc
      have ha := wire_answer o Hx _ _ _ hsrv
      rw [hst hc.1] at ha
      iexists (txn.underPfx pfx (mvcc.stateAfter log))
      iframe Hst
      ipureintro
      rw [v3rpc.rangeSel_underPfx pfx _ o hc.2]
      exact ha.2
    · itrivial
  rw [Herr]
  iapply statusErrOk_nil

/-- `kvGetResultC` gives `kvGetResultR` (it drops `etcdReadAt` and `etcdHasState`). -/
theorem kvGetResultC_R [EM : EtcdModel GF] (pfx : GoString) (lo : w64) (o : OpFull) (resp : Loc)
    (err : GoInterface) :
    kvGetResultC (GF := GF) pfx lo o resp err ⊢ kvGetResultR pfx lo o resp err := by
  unfold kvGetResultC kvGetResultR
  iintro (%H | ⟨%H, %r, #Hg, #Hre, -, -, %Hb, #Hc⟩)
  · ileft; ipureintro; exact H
  iright
  isplitr; · ipureintro; exact H
  iexists r
  iframe #
  ipureintro; exact Hb

/-- **A real `*kv`'s get at the server's model** (`kv_get_server_r` from `kvAnyAu`; the core of `isEtcdKVTodo_of_kv` and
`isEtcdKVE_of_kv_r`, at any context `ci` the client's contracts accept: `ctxOk`, `ctxErrClient`), for
an exact get and a non-empty prefix (see the file header). Premises: the registration of etcd's
`Range` at `addr`, the server's read side (`isServerRead`: the first floor, the KV invariants), the receipts' bound,
`etcdserverpb`'s sort enumerations (`sortNamesOk`), and (unit W-M3) the client's updates at the
read names (`kvAnyAu E γr`: a linearizable get's floor is its read update's result, at the state
of the log read). -/
theorem kv_get_server (api : Loc) (addr : List GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (pfx : GoString) (hpfx : pfx ≠ [])
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) (lo : w64)
    (Hnp : ¬ opGetPanics gs) (Ht : (opGetModel key gs).t = W64 1)
    (Hx : (opGetModel key gs).getExact) (Hsz : opSizeOk (opGetModel key gs))
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗ kvRegs (srvsAt addr E γr cid mid) ∗
        sortNamesOk ∗ kvAnyAu E γr ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
        etcdReached (EM := v3rpc.etcdModelOfServer E γr false) lo }}
      (App (App (App (Val #(methods (kvIfaceOf api).ty go!"Get" (kvIfaceOf api).v))
        (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (
        R ∗ kvGetResultC (EM := v3rpc.etcdModelOfServer E γr false) pfx lo (opGetModel key gs) resp err ∗
        getRespMore (EM := v3rpc.etcdModelOfServer E γr false) pfx (opGetModel key gs) resp err ∗
        statusErrOk err) }} := by
  iintro %Φ ⟨#Pc, Hlt, #Hsrd, #Hkv, #Hrpc, #Hsn, #Hany, #Hctx, #Hce, #Hopts, HR, #Hlo⟩ HΦ
  ihave #Hr := kvAnyAu_range E γr $$ Hany
  ihave #Hsi := sortNamesIf_of_ok (opGetModel key gs).base.sortSet $$ Hsn
  iapply (kv_get_server_r api addr s E γr cid mid pfx hpfx ci cd key sl gs R lo Hnp Ht Hx Hsz hrb)
    $$ [Hlt HR] HΦ
  iframe #; iframe

/-- **A real `*kv` meets the recipes' get contract** (`isEtcdKVTodo`) at the server's model, for a
non-empty prefix (see the file header): `kv_get_server` at `context.TODO()` (`todo_ctx`, given
that `errors.As` can take `*rpctypes.EtcdError`, `hAs`). -/
theorem isEtcdKVTodo_of_kv (api : Loc) (addr : List GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (pfx : GoString) (hpfx : pfx ≠ [])
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗ kvRegs (srvsAt addr E γr cid mid) ∗
        sortNamesOk ∗ kvAnyAu E γr ⊢
      isEtcdKVTodo (EM := v3rpc.etcdModelOfServer E γr false) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hsrd, #Hkv, #Hrpc, #Hsn, #Hany⟩
  unfold isEtcdKVTodo
  iintro !> %key %sl %gs %R %lo %Φ !> ⟨Hlt, #Hopts, HR, #Hlo, %Hpre⟩ HΦ
  obtain ⟨Hnp, Ht, Hx, -, Hsz⟩ := Hpre
  imod (todo_ctx (GF := GF) hAs) with ⟨%cd, #Hctx, #Hce⟩
  iapply (kv_get_server api addr s E γr cid mid pfx hpfx todoCtxVal cd key sl gs R lo Hnp Ht Hx Hsz hrb)
    $$ [Hlt HR] [HΦ]
  · (try iframe Hlt)
    iframe #; iframe
  inext
  iintro %resp %err ⟨Hlt, HR, #Hres, #Hmore, -⟩
  iapply HΦ
  iframe Hlt
  iframe HR Hmore
  iapply (kvGetResultC_R (EM := v3rpc.etcdModelOfServer E γr false)) $$ Hres

/-- **A real `*kv` meets the cache's get contract** (`isEtcdKVE`, K3) at the server's model, for a
non-empty prefix: `kv_get_server` at any context (`ctxErrClientAll`: its `Err()` returns client
errors), with no resource for the options; with the ranges' updates (`kvRangeAu`, 2026-10-20) and
no sort enumerations (the cache's gets do not sort, `isEtcdKVE`). -/
theorem isEtcdKVE_of_kv_r (api : Loc) (addr : List GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (pfx : GoString) (hpfx : pfx ≠ [])
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗ kvRegs (srvsAt addr E γr cid mid) ∗
        kvRangeAu E γr ∗ ctxErrClientAll ⊢
      isEtcdKVE (EM := v3rpc.etcdModelOfServer E γr false) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hsrd, #Hkv, #Hrpc, #Hany, #Hall⟩
  unfold isEtcdKVE
  iintro !> %ctx %cs %key %sl %gs %lo %Φ !> ⟨Hlt, #Hctx, #HctxO, #Hopts, #Hlo, %Hpre⟩ HΦ
  obtain ⟨Hnp, Ht, Hx, Hss, -, Hsz⟩ := Hpre
  ihave #Hsi : sortNamesIf (GF := GF) (opGetModel key gs).base.sortSet $$ []
  · rw [Hss]; unfold sortNamesIf; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  iunfold ctxErrClientAll at Hall
  ihave #Hce := Hall $$ %ctx %cs Hctx
  ihave #Hok := ctxOk_of_isContext ctx cs $$ [$Hctx $HctxO]
  ihave #Hor := optsAt_res sl gs iprop(True) $$ Hopts
  iapply (kv_get_server_r api addr s E γr cid mid pfx hpfx ctx cs key sl gs iprop(True) lo Hnp Ht Hx Hsz hrb)
    $$ [Hlt] [HΦ]
  · (try iframe Hlt)
    iframe #
  inext
  iintro %resp %err ⟨Hlt, -, #Hres, -, #Hse⟩
  iapply HΦ
  iframe Hlt
  iframe Hres
  iapply errStrOk_of_statusErrOk $$ Hse

end proofs

end client
end EtcdGrove
end Perennial
