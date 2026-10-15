/-
**A real `*kv` meets the recipes' get contract at the server's model** (the vertical slice's unit
V2b, 2026-10-14, after slice-v2's; `InvServerKV.lean`). Lean-first, no Rocq counterpart.

`isEtcdKVTodo_of_kv`: a `*kv` over a connection to a gRPC server at `addr` where etcd's `Range` is
registered (`kvObjAt api addr`, `etcd_kv_served`) meets `isEtcdKVTodo` (`cache/v3/InvEtcdTxn.lean`)
at `v3rpc.etcdModelOfServer E`, for a non-empty prefix. The call is `kv.Get` at `context.TODO()`
(`todo_ctx`), the request handed the caller's floor (`floor_of_reached`: linearizability) and the
committed index `0`.

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
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

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
open v3rpc (rangeReplyOk etcdRangeSpec)

theorem sext_small (x : w64) (h0 : 0 ≤ sint.Z x) (h1 : sint.Z x ≤ 4) :
    W64 (sint.Z (W32 (sint.Z x))) = x := by
  have : sint.Z (W32 (sint.Z x)) = sint.Z x := by word
  rw [this]; word

theorem sext_zero : W64 (sint.Z (W32 0)) = W64 0 := by word

theorem w32_zero_iff (x : w64) (h0 : 0 ≤ sint.Z x) (h1 : sint.Z x ≤ 4) :
    W32 (sint.Z x) = W32 0 ↔ x = W64 0 := by
  constructor
  · intro h
    rw [← sext_small x h0 h1, h]; word
  · intro h; subst h; word

/-- The wire's fields a get's answer reads are the `Op`'s. -/
theorem wire_fields (o : OpFull) :
    (rangeWireOf o).key = o.key ∧ (rangeWireOf o).base.rangeEnd = o.base.rangeEnd ∧
    (rangeWireOf o).base.rev = o.base.rev ∧ (rangeWireOf o).base.limit = o.base.limit ∧
    (rangeWireOf o).base.countOnly = o.base.countOnly ∧ (rangeWireOf o).keysOnly = o.keysOnly ∧
    (rangeWireOf o).base.serializable = o.base.serializable ∧
    (rangeWireOf o).base.minModRev = o.base.minModRev ∧
    (rangeWireOf o).base.maxModRev = o.base.maxModRev ∧
    (rangeWireOf o).base.minCreateRev = o.base.minCreateRev ∧
    (rangeWireOf o).base.maxCreateRev = o.base.maxCreateRev ∧ (rangeWireOf o).t = W64 1 := by
  simp [rangeWireOf, txn.rangeOpOf, OpFull.newOp, OpModel.zero]

theorem wire_rangeSel (o : OpFull) (s : List EtcdKv) : rangeSel s (rangeWireOf o) = rangeSel s o := by
  obtain ⟨h1, h2, -, -, -, -, -, h8, h9, h10, h11, -⟩ := wire_fields o
  have hf : kvFilterOk (rangeWireOf o) = kvFilterOk o := by
    funext v; unfold kvFilterOk; rw [h8, h9, h10, h11]
  simp only [rangeSel, rangeIn, h1, h2, hf]

theorem wire_sort (o : OpFull) (hx : o.getExact) :
    (rangeWireOf o).effSortOrder = o.effSortOrder ∧
      (o.effSortOrder ≠ W64 0 → (rangeWireOf o).sortTarget = o.sortTarget) ∧
      (rangeWireOf o).base.sortSet =
        decide ((rangeWireOf o).sortOrder ≠ W64 0 ∨ (rangeWireOf o).sortTarget ≠ W64 0) := by
  obtain ⟨-, -, -, ho0, ho1, ht0, ht1⟩ := hx
  have eo := sext_small o.sortOrder ho0 (by omega)
  have et := sext_small o.sortTarget ht0 ht1
  have zo := w32_zero_iff o.sortOrder ho0 (by omega)
  have zt := w32_zero_iff o.sortTarget ht0 ht1
  cases hs : o.base.sortSet
  · simp [rangeWireOf, txn.rangeOpOf, OpFull.newOp, OpModel.zero, sortOrderWire, sortTargetWire,
      OpFull.effSortOrder, hs, sext_zero]
  · simp only [rangeWireOf, txn.rangeOpOf, OpFull.newOp, OpModel.zero, sortOrderWire,
      sortTargetWire, OpFull.effSortOrder, hs, ↓reduceIte, eo, et, zo, zt]
    by_cases a : o.sortOrder = W64 0 <;> by_cases b : o.sortTarget = W64 0 <;> simp [a, b] <;>
      simp_all

theorem wire_sort_fields (o : OpFull) (hx : o.getExact) (hs : o.base.sortSet = true) :
    (rangeWireOf o).sortOrder = o.sortOrder ∧ (rangeWireOf o).sortTarget = o.sortTarget := by
  obtain ⟨-, -, -, ho0, ho1, ht0, ht1⟩ := hx
  have h1 := sext_small o.sortOrder ho0 (by omega)
  have h2 := sext_small o.sortTarget ht0 ht1
  constructor
  · show W64 (sint.Z (sortOrderWire o)) = _
    simp only [sortOrderWire, hs, ↓reduceIte]; exact h1
  · show W64 (sint.Z (sortTargetWire o)) = _
    simp only [sortTargetWire, hs, ↓reduceIte]; exact h2

theorem rangeLimit_nonpos (l : w64) (h : sint.Z l ≤ 0) :
    sint.Z (if 0 < sint.Z l ∧ sint.Z l < 2 ^ 63 - 1 then l + W64 1 else l) ≤ 0 := by
  rw [if_neg (by omega)]; exact h

theorem wire_not_cutEarly (o : OpFull) (hx : o.getExact) : ¬ txn.cutEarly (rangeWireOf o) := by
  rintro ⟨he, hlim⟩
  rw [(wire_sort o hx).1] at he
  have hc := hx.2.1
  cases hs : o.base.sortSet
  · simp [OpFull.effSortOrder, hs] at he
  obtain ⟨eo, et⟩ := wire_sort_fields o hx hs
  have el := (wire_fields o).2.2.2.1
  have key : sint.Z (if txn.isDefaultOrd (rangeWireOf o).sortTarget (rangeWireOf o).sortOrder = false ∨
      txn.hasRevFilters (rangeWireOf o) = true then W64 0 else (rangeWireOf o).base.limit) ≤ 0 := by
    rw [eo, et, el]
    unfold OpFull.effSortOrder at he
    simp only [hs, Bool.true_eq_false, ↓reduceIte] at he
    unfold txn.isDefaultOrd
    by_cases a : o.sortOrder = W64 0 <;> by_cases b : o.sortTarget = W64 0
    · simp [a, b] at he
    · have hl : ¬ 0 < sint.Z o.base.limit := fun h => hc ⟨hs, b, a, h⟩
      split
      · simp
      · omega
    · by_cases c : o.sortOrder = W64 1
      · simp [a, b, c] at he
      · rw [if_pos (Or.inl (by simp; exact ⟨a, fun _ => c⟩))]; simp
    · rw [if_pos (Or.inl (by simp; exact ⟨a, fun h => absurd h b⟩))]; simp
  have := rangeLimit_nonpos _ key
  unfold txn.rangeLimitOf at hlim
  exact absurd hlim (by simp only [] at this ⊢; omega)

theorem wire_fastKeysOnly (o : OpFull) (hx : o.getExact) : txn.fastKeysOnly (rangeWireOf o) = false := by
  simp [txn.fastKeysOnly, (wire_fields o).2.2.2.2.2.1, hx.1]

theorem wire_rangeKvsOk (o : OpFull) (hx : o.getExact) (sel kvs : List EtcdKv)
    (h : rangeKvsOk (rangeWireOf o) sel kvs) : rangeKvsOk o sel kvs := by
  obtain ⟨he, ht, -⟩ := wire_sort o hx
  obtain ⟨-, -, -, el, ec, ek, -⟩ := wire_fields o
  obtain ⟨l, hp, h0, h1, h2, hk⟩ := h
  rw [he] at h0 h1 h2
  refine ⟨l, hp, h0, fun e => ?_, fun e => ?_, ?_⟩
  · rw [← ht (by rw [e]; decide)]; exact h1 e
  · rw [← ht (by rw [e]; decide)]; exact h2 e
  · rw [hk, el, ec, ek]

/-- **The server's answer to the wire's get is the model's answer to the `Op`'s** (`getExact`):
its key-values are `rangeKvsOk` of the `Op`'s selection, and `More` is the model's. -/
theorem wire_answer (o : OpFull) (hx : o.getExact) (st kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (rangeWireOf o) st kvs more) :
    rangeKvsOk o (rangeSel st o) kvs ∧
      more = (!o.base.countOnly && decide (0 < sint.Z o.base.limit) &&
        decide (sint.Z o.base.limit < ((rangeSel st o).length : Int))) := by
  obtain ⟨-, -, -, el, ec, -⟩ := wire_fields o
  obtain ⟨kvs', hok, hk, hm⟩ := txn.srvRangeOk_rangeKvsOk (rangeWireOf o) st kvs more
    (wire_sort o hx).2.2 h (wire_not_cutEarly o hx)
  rw [wire_fastKeysOnly o hx] at hk
  have hk' : kvs = kvs' := by
    rw [hk]; conv => rhs; rw [← List.map_id kvs']
    congr 1
  subst hk'
  rw [wire_rangeSel] at hok hm
  refine ⟨wire_rangeKvsOk o hx _ _ hok, ?_⟩
  cases hco : o.base.countOnly
  · rw [ec, el, hco] at hm
    rw [hm rfl hx.2.2.1]
    simp
  · obtain ⟨l, ⟨hperm, -⟩, hmore, -⟩ := h
    have hpre : txn.srvPre (rangeWireOf o) st = [] := by
      unfold txn.srvPre; rw [ec, hco]; rfl
    rw [hpre] at hperm
    have := List.Perm.eq_nil hperm
    subst this
    rw [hmore]; simp [txn.srvMore, hco]; omega

/-- **A prefix get's answer is the state under the prefix** (a non-empty prefix: for the empty
one, `isPrefixGet` reads from `"\x00"` on, which leaves out an empty key). -/
theorem prefix_answer (pfx : GoString) (o : OpFull) (hp : o.isPrefixGet pfx = true)
    (hne : pfx ≠ []) (st kvs : List EtcdKv) (h : rangeKvsOk o (rangeSel st o) kvs) :
    kvs = txn.underPfx pfx st ∧ o.base.rev = W64 0 ∧ o.base.serializable = o.base.serializable := by
  simp only [OpFull.isPrefixGet, hne, ↓reduceIte, decide_eq_true_eq] at hp
  obtain ⟨-, hk, hc, hs, hl, hr, h1, h2, h3, h4, hkey, hre⟩ := hp
  obtain ⟨l, hperm, h0, -, -, hkv⟩ := h
  have he : o.effSortOrder = W64 0 := by simp [OpFull.effSortOrder, hs]
  rw [h0 he] at hkv
  refine ⟨?_, hr, rfl⟩
  rw [hkv, hc, hk, hl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have : (0 : Int) < sint.Z (W64 0) ↔ False := by simp
  simp only [this, ↓reduceIte, List.map_id']
  unfold rangeSel rangeIn txn.underPfx
  rw [List.filter_filter]
  apply List.filter_congr
  intro v _
  rw [hkey, hre]
  have hf : kvFilterOk o v = true := by simp [kvFilterOk, h1, h2, h3, h4]
  rw [hf, Bool.true_and]
  by_cases hv : pfx <+: v.key
  · simp [hv, (concurrency.inRange_prefix pfx v.key hne).2 hv]
  · have : inRange pfx (prefixRangeEnd pfx) v.key = false := by
      cases h' : inRange pfx (prefixRangeEnd pfx) v.key
      · rfl
      · exact absurd ((concurrency.inRange_prefix pfx v.key hne).1 h') hv
    simp [hv, this]

theorem isPrefixGet_rev (pfx : GoString) (o : OpFull) (hp : o.isPrefixGet pfx = true) :
    o.base.rev = W64 0 := by
  simp only [OpFull.isPrefixGet, decide_eq_true_eq] at hp
  exact hp.2.2.2.2.2.1

theorem zip_get_snd {α β : Type} (a : List α) (b : List β) (i : Nat) (e : α × β)
    (h : (a.zip b)[i]? = some e) : b[i]? = some e.2 := by
  rw [List.getElem?_zip_eq_some] at h; exact h.2

theorem zip_get_fst {α β : Type} (a : List α) (b : List β) (i : Nat) (e : α × β)
    (h : (a.zip b)[i]? = some e) : a[i]? = some e.1 := by
  rw [List.getElem?_zip_eq_some] at h; exact h.1

section kvs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The server's key-values (`txn.kvsIs`) are the client's (`kvPtrsAt`): the same fields. -/
theorem kvPtrsAt_of_kvsIs (ps : List Loc) (kvs : List EtcdKv) :
    txn.kvsIs (GF := GF) ps kvs ⊢ kvPtrsAt ps kvs := by
  unfold txn.kvsIs kvPtrsAt txn.kvIs kvValAt; exact .rfl

end kvs

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem sortNamesIf_of_ok (b : Bool) : sortNamesOk (GF := GF) ⊢ sortNamesIf b := by
  iintro #H
  unfold sortNamesIf
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [↓reduceIte]; iexact H

/-- **A real `*kv` meets the recipes' get contract** (`isEtcdKVTodo`) at the server's model, for a
non-empty prefix (see the file header). Premises: the registration of etcd's `Range` at `addr`,
the server's read side (`isServerRead`: the first certificate, `storeSmall`), `etcdserverpb`'s
sort enumerations (`sortNamesOk`), that `errors.As` can take `*rpctypes.EtcdError` (`hAs`). -/
theorem isEtcdKVTodo_of_kv (api : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) (pfx : GoString) (hpfx : pfx ≠ [])
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗ isGrpcRpc addr go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        sortNamesOk ⊢
      isEtcdKVTodo (EM := v3rpc.etcdModelOfServer E) (kvIfaceOf api) pfx := by
  iintro ⟨#Pc, #Hsrd, #Hkv, #Hrpc, #Hsn⟩
  unfold isEtcdKVTodo
  iintro !> %key %sl %gs %R %lo %Φ !> ⟨#Hopts, HR, #Hlo, %Hpre⟩ HΦ
  obtain ⟨Hnp, Ht, Hx⟩ := Hpre
  ihave ⟨%F, #HF, %HlF⟩ := floor_of_reached s E γr lo $$ [$Hsrd $Hlo]
  ihave #Hsm := storeSmall_of_read s E γr $$ Hsrd
  imod (todo_ctx (GF := GF) hAs) with ⟨%cd, #Hctx, #Hce⟩
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  ihave #Hc0 : committedAtLeast γr (W64 0) $$ []
  · unfold committedAtLeast
    rw [show uint.nat (W64 0) = 0 from rfl]
    iexact H0
  ihave #Hsi := sortNamesIf_of_ok (opGetModel key gs).base.sortSet $$ Hsn
  iapply (v3.kv.wp_Get api addr todoCtxVal cd key sl gs R (etcdRangeSpec E γr cid mid)
    (rangeReplyOk E γr (W64 0) F (rangeWireOf (opGetModel key gs)) cid mid (fun _ => iprop(True))))
    $$ [HR]
  · iframe #
    iframe
    isplitl []
    · ipureintro; exact ⟨Hnp, Ht⟩
    imodintro
    inext
    unfold etcdRangeSpec
    iexists (W64 0), F, (fun _ => iprop(True))
    iframe #
    isplitr
    · ileft; ipureintro; rfl
    iintro %m Hm
    iexact Hm
  inext
  iintro %resp %err ⟨HR, Hout⟩
  iapply HΦ
  iframe HR
  iunfold rangeCallOut at Hout
  icases Hout with (⟨%Herr, %m, #Hm, #Hq⟩ | ⟨%Herr, -⟩)
  rotate_left
  · isplitl
    · unfold kvGetResultR; ileft; ipureintro; exact Herr.1
    · unfold getRespMore; ileft; ipureintro; exact Herr.1
  iunfold rangeReplyOk at Hq
  icases Hq with ⟨%log, #Hcert, %Hlog, -⟩
  obtain ⟨h2, h3, hrev, -, -, -, -, hsrv, hFl⟩ := Hlog
  iunfold rangeRespMsg at Hm
  icases Hm with ⟨%Hrn, %h, %ksl, %ps, #Hh, #Hhf, #Hksl, #Hps, #Hkvs, #Hmore, -⟩
  iunfold hdrFull at Hhf
  icases Hhf with ⟨%Hhn, -, -, #Hrev, -, -⟩
  rw [hrev] at hsrv; rw [hrev]
  have hr : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by word
  have hFlen := hFl.length_le
  ihave #Hreach := v3rpc.etcdReached_of_cert E log (W64 ((log.length : Int) - 1)) (by omega) $$ Hcert
  ihave ⟨#Hst, %Hwf⟩ := v3rpc.etcdState_of_cert_last E log pfx h2 h3 $$ [$Hsm $Hcert]
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
  generalize opGetModel key gs = o at Hx hst hsrv ⊢
  isplitl
  · unfold kvGetResultR
    iright
    isplitl; · ipureintro; exact Herr
    iexists (W64 ((log.length : Int) - 1))
    iframe Hgr Hreach
    isplitl
    · ipureintro
      refine ⟨fun _ => ?_, by omega⟩
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
        have h1 := zip_get_snd _ _ i e He
        ihave Hkw := Hall $$ %i %e.2 %w %h1 %Hw
        unfold kvValAt; iunfold txn.kvIs at Hkw; iexact Hkw
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

end proofs

end client
end EtcdGrove
end Perennial
