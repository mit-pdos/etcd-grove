/- Lean-first (no Rocq counterpart). The proof of `runner.apply`: Draft, to come.

The outline: `m.ops++`, `applying.Store(i)` (the hook's counters, `memW`); by `o.kind`
(`opIs`): a put or a delete is `begin`, `m.kv.Write` (`KV.Write.contract` through `shapes.law`, the
hook at `i`: `hookOk`), `checkHook`, `Rev`, `writeRange` of the key's previous value, the put
(`pending.put`, `Txn.Put.contract`) or `writeSub` of the delete, and `end` at `tw.End` (`endCb` from
`Txn.End.contract` at the incarnation's invariant, `memberInv_live`); `txn`; a grant is
`lessor.Grant` (the lessor's contract at the member's backend, `lessorW_backend`; `csContractA` at
the hook), `checkHook`, the leases' slice appended, `Rev` unchanged; a revoke is `begin`, the keys on the lease (`onLease`), `end` at the
closure calling `lessor.Revoke` (its update through the range deleter, `mvccDeleter`), `checkHook`,
the slice filtered, `Lookup` nil; `compact`; `Commit` (`KV.Commit.contract`); a read (`KV.Read`,
`Txn.Rev`, `Txn.FirstRev`, `Txn.Range`, `history.snapshot`, `checkRangeAt`, `Txn.End`);
`checkLeases`. The model's step is `runM_succ`; the lease bucket's records (`leaseRecsOk`) follow
`Grant`'s `rbSet` and `Revoke`'s `rbDel`. The put's and the delete's trace (`traceutil.TODO()`,
`ownTrace t true`) is threaded through `writeRange`, `Txn.Put` and `writeSub`, whose specs take
and give it back.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__begin
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pending__put
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__end
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeSub
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__txn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__compact
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkLeases
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Grant
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Revoke
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.ApplyLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.LeaseRecLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriteSubLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.RevokeLemmas
public import Perennial.Spec.sync.atomic.Int64__Add

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 2000000 in
theorem runner.apply.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_begin : runner.begin.spec (GF := GF) (hG := hG))
    (wp_checkHook : runner.checkHook.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_writeRange : runner.writeRange.spec (GF := GF) (hG := hG))
    (wp_put : pending.put.spec (GF := GF) (hG := hG))
    (wp_end : runner.end.spec (GF := GF) (hG := hG))
    (wp_writeSub : runner.writeSub.spec (GF := GF) (hG := hG))
    (wp_txn : runner.txn.spec (GF := GF) (hG := hG))
    (wp_Grant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (wp_Revoke : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    (wp_Lookup : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (wp_compact : runner.compact.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG))
    (wp_checkLeases : runner.checkLeases.spec (GF := GF) (hG := hG)) :
    runner.apply.spec (GF := GF) (hG := hG) := by
  intro _ _ x ks cfg wr h γh ops i mp m f v qw nw k p o lead hov hlogOk hnw hgk h38
  haveI := isInc_persistent hpers
  haveI := hpers.1
  wp_start as ⟨Hctx, Hrd, Hop, Hmw, Hlead, Htok⟩
  ihave #Hctx := Hctx
  ihave #Hctx2 := Hctx
  iunfold writerCtx at Hctx2
  icases Hctx2 with ⟨#Hrn, #Hrcfg, %Hrmix, #Hrsh, #Hpkb, #Hpks, #Hpkl, #Hpkt, %Hkslen, ⟨%lg, #Hlg, #Hlg0⟩,
    -, -, -, #Hcrev, #Hccomp, -, -, %HOps⟩
  ihave #Hrn2 := Hrn
  iunfold rnCtx at Hrn2
  icases Hrn2 with ⟨#Hpkg, #Hpkm, #Hks, %Hksne, #HH, #Hhist, #Hcfg, -⟩
  ihave #Hop := Hop
  ihave #HopF := Hop
  iunfold memW at Hmw
  icases Hmw with ⟨Hops, ⟨%a0, %s0, Hhk, %Ha0⟩, Hmc⟩
  iunfold opIs at Hop
  icases Hop with ⟨%ov, %subs, #Hp, #Hok, #Hoe, #Hoq, #Hosubs, %Hsl, #Hsubs, %Hov⟩
  have hn38 : v.ops < 2 ^ 38 := by
    have := (List.getElem?_eq_some_iff.1 hov).1; omega
  iunfold hookPre at Hhk
  icases Hhk with ⟨Happ, Hsav, %Hsa⟩
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"applying" mp) (W64 (v.ops : Int) + W64 1)
    $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists _
  iframe Happ
  iintro Happ
  imod Hcl with -
  imodintro
  have hai : W64 (v.ops : Int) + W64 1 = W64 ((v.ops + 1 : Nat) : Int) := by push_cast; word
  rw [hai]
  have hsa : sint.Z s0 < sint.Z (W64 ((v.ops + 1 : Nat) : Int)) := by
    have : sint.Z (W64 ((v.ops + 1 : Nat) : Int)) = v.ops + 1 := by word
    omega
  wp_auto
  obtain ⟨hkind, hendNil, hval, hlease, hwrite, hshared, hid, hrev, hwait⟩ := Hov
  ihave ⟨#Hfkind, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_kind p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hfkey, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_key p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hfend, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_end p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hfval, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_val p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hflease, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_lease p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hfq, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_q p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hfid, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_id p ov
    DFrac.discard).access_strict $$ Hp
  wp_auto
  rw [hkind]
  have hvalid := hlogOk v.ops o hov
  obtain ⟨hk9, hk0', hvput, hvtxn, hvgrant, hvrev, hvcomp⟩ := hvalid
  have hvl : v.ops + 1 ≤ ops.length := (List.getElem?_eq_some_iff.1 hov).1
  have hsa' : sint.Z s0 ≤ sint.Z (W64 ((v.ops + 1 : Nat) : Int)) := by omega
  by_cases hk0 : o.kind = W64 0
  · -- a put
    simp only [hk0, _root_.decide_true]
    iunfold runnerKeys at Hks
    icases Hks with ⟨%keys, #Hkeys, #Hksl, %Hsorted, %Hksne2⟩
    ihave %Hksn := ownSlice_len $$ Hksl
    have hksl : ks.length < 2 ^ 63 := by
      have : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
      have := Hksn.1; have : sint.Z keys.len < 2 ^ 63 := by word
      omega
    obtain ⟨hlenH, hrevH, hreachH, hLok0, h63H, hmatchH, hpnH, hr40, honceH⟩ :=
      member_facts ks Hsorted ops hlogOk hksl v.ops (by omega) h38
    iunfold memCore at Hmc
    icases Hmc with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
      Hinc, Hopen, Hback, #Hhk, Hrdrs, Hbk, Hles, %HU⟩
    iunfold hookOk at HhookOk
    icases HhookOk with ⟨%Hfnil, #Hhrun⟩
    icases leadPre_lb_apply γh ks ops v.ops lead $$ Hlead with ⟨Hlead, #Hlb⟩
    -- `begin`
    rw [← σOf_rev]
    (try wp_auto)
    wp_apply (wp_begin x ks h γh i mp m v.ι v.kv qw (σOf ks ops v.ops) v.b (histAt ks ops v.ops)
      hlenH hpnH (by omega)) $$ [Hrd Hrev Hinc] as %pp ⟨Hrd, Hrev, Hinc, Hpp⟩
    · iframe; iframe #
    (try wp_auto)
    -- `m.kv.Write(…)`, the hook run at `i`
    iunfold incW at Hinc
    icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
    ihave #Hmv : isMvcc v.kv v.ι.kv $$ []
    · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H, -⟩; iexact H
    ihave %Hkvs := hsh.1 v.kv v.ι.kv $$ Hmv
    obtain ⟨kty, kvv, hkveq, -, hKW, -⟩ := Hkvs
    rw [hkveq]
    have hR1 : mvccReaders (GF := GF) v.ι.kv nw ⊣⊢ mvccReaders v.ι.kv (nw - 1) ∗ mvccReaders v.ι.kv 1 := by
      have := hRdSplit v.ι.kv (nw - 1) 1; rwa [Nat.sub_add_cancel hnw] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    wp_apply wp_traceTODO $$ [$Hpkt] as %trc ⟨%Htrn, Htrc⟩
    (try wp_auto)
    ihave Hau := write_au hpers ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops) hpnH
      $$ [Hret Hσw]
    · iframe #; iframe
    wp_apply (hKW v.ι.kv trc true 1 _ iprop(True) (hookPre mp (W64 ((v.ops + 1 : Nat) : Int)) s0)
        iprop(True ∗ hookPost mp (W64 ((v.ops + 1 : Nat) : Int))) f
        (fun σ' => iprop(⌜σ' = σOf ks ops v.ops⌝ ∗ ghostVar v.ι.ret qw () ∗
          ghostVar m.σ (1 : Qp).half (σOf ks ops v.ops))))
      $$ [Hr1 Htrc Hback Happ Hsav Hau]
      as %tw ⟨Htrc, Hback, ⟨%σ0, Htw, %Hσ0, Hret, Hσw⟩, -, Hpost⟩
    · iframe #; iframe
      isplitr; · ipureintro; exact Htrn
      isplitl; · iunfold hookPre; iframe; ipureintro; omega
      iapply Hhrun
    subst Hσ0
    icases (persistent_entails_right (hsh.2.2.1 tw v.ι.kv trc (.write (σOf ks ops v.ops) [])))
      $$ Htw with ⟨%Hsht, Htw⟩
    obtain ⟨tty, tv, rfl, hTRev, -, -, hTPut, -, -, hTEnd⟩ := Hsht
    (try wp_auto)
    iunfold hookPost at Hpost
    icases Hpost with ⟨Happ, Hsav⟩
    wp_apply wp_checkHook x mp (W64 ((v.ops + 1 : Nat) : Int)) $$ [$Hsav] as Hsav
    (try wp_auto)
    wp_apply (hTRev v.ι.kv trc (.write (σOf ks ops v.ops) [])) $$ [Htw] as Htw
    · iframe #; iframe
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp [MTxn.state, σOf_rev]
    (try wp_auto)
    -- `writeRange` of the key's previous value
    have hok0 : pendOk ks (σOf ks ops v.ops) (histAt ks ops v.ops) []
        ⟨W64 ((histAt ks ops v.ops).length : Int), lastSt (histAt ks ops v.ops), []⟩ :=
      ⟨rfl, by simpa [applyChanges] using hmatchH⟩
    ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    wp_apply (wp_writeRange x ks h γh mp v.ι.kv (interface.mkOk tty tv) trc true (σOf ks ops v.ops) []
        (histAt ks ops v.ops) pp _ { key' := ov.key', end' := slice.nil, ro' := zeroValDef }
        ⟨o.key, [], true, zeroValDef⟩ hok0 hlenH hrevH hreachH hLok0 h63H)
      $$ [Hrd Hcmp Htw Htrc Hpp] as ⟨Hrd, Hcmp, Htw, Htrc, Hpp⟩
    · iframe; iframe #
      isplitr
      · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hksne2⟩
      iunfold rangeIs; iframe #; ipureintro; simp
    (try wp_auto)
    -- `p.put(…)`, `tw.Put(…)`
    obtain ⟨hkks, hlL⟩ := hvput hk0
    wp_apply wp_bytes_to_string ov.key' o.key DFrac.discard $$ [$Hok] as -
    (try wp_auto)
    rw [hval, hlease]
    wp_apply wp_put pp _ o.key o.val o.lease $$ [$Hpp] as Hpp
    (try wp_auto)
    wp_apply wp_string_to_bytes as %vs ⟨Hvs, -⟩
    imod ownSlice_persist $$ Hvs with #Hvs
    (try wp_auto)
    try rw [hlease]
    iunfold lessorW at Hles
    icases Hles with ⟨%rd, %r, #Hlpkg, #Hlinv, #Hlcfg, #Hguard, #Hrevoc, #Hlok, Hlrd, Hlo, Hrvk, Hever,
      #Hreq, Hrdo, Hdel, Hlbe, Hrb, %Hrecs, Hstop, #Hpool⟩
    wp_apply (hTPut v.ι.kv trc true (σOf ks ops v.ops) [] ov.key' vs o.key o.val o.lease
        (leasesAfter ks ops v.ops)) $$ [Htw Htrc Hok Hvs Hlo] as ⟨Htw, Htrc, Hlo⟩
    · iframe; iframe #
      ipureintro; exact ⟨Hkslen _ hkks, hlL⟩
    (try wp_auto)
    iunfold ownPending at Hpp
    icases Hpp with ⟨%pv, Hpv, %Hprev, Hpst, Hpch, Hpcap⟩
    (try wp_auto)
    wp_apply wp_check
    · ipureintro
      simp only [PendM.put] at Hprev
      rw [Hprev, hlenH]; simp; rfl
    (try wp_auto)
    ihave Hpp : ownPending pp ((⟨W64 ((histAt ks ops v.ops).length : Int), lastSt (histAt ks ops v.ops),
        []⟩ : PendM).put o.key o.val o.lease) $$ [Hpv Hpst Hpch Hpcap]
    · iunfold ownPending; iexists pv; iframe; ipureintro; exact Hprev
    -- `end` at `tw.End`
    have hokP := pendOk_put' ks (σOf ks ops v.ops) (histAt ks ops v.ops) [] _ hok0 hlenH
      o.key o.val o.lease hkks
    have hop : opPend ks (runM ks ops v.ops) o =
        (⟨W64 ((histAt ks ops v.ops).length : Int), lastSt (histAt ks ops v.ops), []⟩ : PendM).put
          o.key o.val o.lease := by
      unfold opPend; simp only [hk0, ↓reduceIte]
    have hcr : cmpAfter ks ops (v.ops + 1) = cmpAfter ks ops v.ops :=
      (runM_succ_pd ks ops v.ops o hov (Or.inl hk0)).1
    obtain ⟨hσ1, hh1⟩ := σOf_succ_commit ks ops v.ops o hov _ (by rw [hop]; exact hokP) hcr
    rw [hop] at hh1
    obtain ⟨-, hhist1, -⟩ := logOk_hist ks Hsorted ops hlogOk (v.ops + 1) (v.ops + 1) (Nat.le_refl _) hvl
    have honce1 := logOk_once ks Hsorted ops hlogOk (v.ops + 1)
    rw [hσ1, hh1] at hhist1
    rw [hσ1] at honce1
    have hb1 : sint.Z (W64 ((σOf ks ops v.ops).rev + 1 : Int)) = (σOf ks ops v.ops).rev + 1 := by word
    have hcrle := commitSt_rev_le (σOf ks ops v.ops) ([] ++ [.put o.key o.val o.lease])
      (by rw [← hlenH]; have := runM_hs_len ks ops v.ops; unfold histAt; omega)
    ihave Hcb := endCb_txnEnd hpers hTEnd ks γh i mp m v.ι (interface.mkOk kty kvv) qw
      (σOf ks ops v.ops) (v.b.1, W64 ((σOf ks ops v.ops).rev + 1 : Int), v.b.2.2) _ _ trc 1 (etcdStorage v.bk) hpnH
      hhist1 honce1 (by simp only; rw [hb1]; omega)
    ihave Hlead := leadPre_end γh ks ops v.ops lead _ hh1 $$ Hlead
    ihave Hinc : incW ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops)
      (v.b.1, W64 ((σOf ks ops v.ops).rev + 1 : Int), v.b.2.2) $$ [Hret Hσw Hbw]
    · iunfold incW; iframe; iframe #
    wp_apply (wp_end x ks h γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops)
        (v.b.1, W64 ((σOf ks ops v.ops).rev + 1 : Int), v.b.2.2) (histAt ks ops v.ops)
        (compsAt ks ops v.ops) pp _ _ _
        iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
          mvccTxn (interface.mkOk tty tv) v.ι.kv trc
            (.write (σOf ks ops v.ops) ([] ++ [.put o.key o.val o.lease])) ∗
          mvccBackend v.ι.kv 1 (etcdStorage v.bk) iprop(True))
        (mvccBackend v.ι.kv 1 (etcdStorage v.bk) iprop(True)) lead hokP hlenH hpnH hb1 (by omega))
      $$ [Hrd Hrev Hkv Hinc Hpp Hlead Hcb Htw Hback] as ⟨Hrd, Hrev, Hkv, Hinc, Hr1, Hback, Hlead⟩
    · iframe; iframe #
    (try wp_auto)
    ihave Hrdrs := hR1.2 $$ [$Hrdrs $Hr1]
    obtain ⟨-, hlz, hgz, hcz⟩ := runM_succ_pd ks ops v.ops o hov (Or.inl hk0)
    iapply HΦ
    iframe Hrd Htok
    isplitl [Hlead]
    · iapply leadPost_end γh ks ops v.ops lead _ hh1 hcz; iexact Hlead
    rw [← hσ1, ← hkveq]
    iexists { v with ops := v.ops + 1, b := ((W64 ((σOf ks ops (v.ops + 1)).rev : Int),
      W64 ((σOf ks ops (v.ops + 1)).rev : Int), v.b.2.2) : Bnd) }, k
    isplitr
    · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, by omega⟩
    iunfold memW
    iframe Hops
    isplitl [Happ Hsav]
    · iexists _, _; iunfold hookPre; iframe; ipureintro
      have : sint.Z (W64 ((v.ops + 1 : Nat) : Int)) = v.ops + 1 := by word
      refine ⟨Int.le_refl _, by omega, by simp only; omega⟩
    iunfold memCore
    dsimp only
    rw [← σOf_rev, hcr, hlz, hgz]
    iframe Hid Hhook
    isplitr
    · iunfold hookOk; iframe #; ipureintro; exact Hfnil
    iframe Hpath Hbe Hle Hkv Hrev Hcmp Hopen Hback Hhk Hrdrs Hleases Hbk Hinc
    isplitr
    · ipureintro; exact hvl
    isplitl
    · iunfold lessorW
      iexists rd, r
      rw [hσ1, pendItems_commit]
      iframe; iframe #
      ipureintro; exact Hrecs
    ipureintro; exact HU
  simp only [hk0, _root_.decide_false]
  (try wp_auto)
  by_cases hk1 : o.kind = W64 1
  · -- a delete
    simp only [hk1, _root_.decide_true]
    iunfold runnerKeys at Hks
    icases Hks with ⟨%keys, #Hkeys, #Hksl, %Hsorted, %Hksne2⟩
    ihave %Hksn := ownSlice_len $$ Hksl
    have hksl : ks.length < 2 ^ 63 := by
      have : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
      have := Hksn.1; have : sint.Z keys.len < 2 ^ 63 := by word
      omega
    obtain ⟨hlenH, hrevH, hreachH, hLok0, h63H, hmatchH, hpnH, hr40, honceH⟩ :=
      member_facts ks Hsorted ops hlogOk hksl v.ops (by omega) h38
    iunfold memCore at Hmc
    icases Hmc with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
      Hinc, Hopen, Hback, #Hhk, Hrdrs, Hbk, Hles, %HU⟩
    iunfold hookOk at HhookOk
    icases HhookOk with ⟨%Hfnil, #Hhrun⟩
    icases leadPre_lb_apply γh ks ops v.ops lead $$ Hlead with ⟨Hlead, #Hlb⟩
    -- `begin`
    rw [← σOf_rev]
    (try wp_auto)
    wp_apply (wp_begin x ks h γh i mp m v.ι v.kv qw (σOf ks ops v.ops) v.b (histAt ks ops v.ops)
      hlenH hpnH (by omega)) $$ [Hrd Hrev Hinc] as %pp ⟨Hrd, Hrev, Hinc, Hpp⟩
    · iframe; iframe #
    (try wp_auto)
    -- `m.kv.Write(…)`, the hook run at `i`
    iunfold incW at Hinc
    icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
    ihave #Hmv : isMvcc v.kv v.ι.kv $$ []
    · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H, -⟩; iexact H
    ihave %Hkvs := hsh.1 v.kv v.ι.kv $$ Hmv
    obtain ⟨kty, kvv, hkveq, -, hKW, -⟩ := Hkvs
    rw [hkveq]
    have hR1 : mvccReaders (GF := GF) v.ι.kv nw ⊣⊢ mvccReaders v.ι.kv (nw - 1) ∗ mvccReaders v.ι.kv 1 := by
      have := hRdSplit v.ι.kv (nw - 1) 1; rwa [Nat.sub_add_cancel hnw] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    wp_apply wp_traceTODO $$ [$Hpkt] as %trc ⟨%Htrn, Htrc⟩
    (try wp_auto)
    ihave Hau := write_au hpers ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops) hpnH
      $$ [Hret Hσw]
    · iframe #; iframe
    wp_apply (hKW v.ι.kv trc true 1 _ iprop(True) (hookPre mp (W64 ((v.ops + 1 : Nat) : Int)) s0)
        iprop(True ∗ hookPost mp (W64 ((v.ops + 1 : Nat) : Int))) f
        (fun σ' => iprop(⌜σ' = σOf ks ops v.ops⌝ ∗ ghostVar v.ι.ret qw () ∗
          ghostVar m.σ (1 : Qp).half (σOf ks ops v.ops))))
      $$ [Hr1 Htrc Hback Happ Hsav Hau]
      as %tw ⟨Htrc, Hback, ⟨%σ0, Htw, %Hσ0, Hret, Hσw⟩, -, Hpost⟩
    · iframe #; iframe
      isplitr; · ipureintro; exact Htrn
      isplitl; · iunfold hookPre; iframe; ipureintro; omega
      iapply Hhrun
    subst Hσ0
    icases (persistent_entails_right (hsh.2.2.1 tw v.ι.kv trc (.write (σOf ks ops v.ops) [])))
      $$ Htw with ⟨%Hsht, Htw⟩
    obtain ⟨tty, tv, rfl, hTRev, -, -, hTPut, -, -, hTEnd⟩ := Hsht
    (try wp_auto)
    iunfold hookPost at Hpost
    icases Hpost with ⟨Happ, Hsav⟩
    wp_apply wp_checkHook x mp (W64 ((v.ops + 1 : Nat) : Int)) $$ [$Hsav] as Hsav
    (try wp_auto)
    -- `writeRange` of the range's previous values, `writeSub` of the delete
    have hok0 : pendOk ks (σOf ks ops v.ops) (histAt ks ops v.ops) []
        ⟨W64 ((histAt ks ops v.ops).length : Int), lastSt (histAt ks ops v.ops), []⟩ :=
      ⟨rfl, by simpa [applyChanges] using hmatchH⟩
    ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    wp_apply (wp_writeRange x ks h γh mp v.ι.kv (interface.mkOk tty tv) trc true (σOf ks ops v.ops) []
        (histAt ks ops v.ops) pp _ { key' := ov.key', end' := ov.end', ro' := zeroValDef }
        ⟨o.key, o.e, o.endNil, zeroValDef⟩ hok0 hlenH hrevH hreachH hLok0 h63H)
      $$ [Hrd Hcmp Htw Htrc Hpp] as ⟨Hrd, Hcmp, Htw, Htrc, Hpp⟩
    · iframe; iframe #
      isplitr
      · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hksne2⟩
      iunfold rangeIs; iframe #; ipureintro; simp [hendNil]
    (try wp_auto)
    iunfold lessorW at Hles
    icases Hles with ⟨%rd, %r, #Hlpkg, #Hlinv, #Hlcfg, #Hguard, #Hrevoc, #Hlok, Hlrd, Hlo, Hrvk, Hever,
      #Hreq, Hrdo, Hdel, Hlbe, Hrb, %Hrecs, Hstop, #Hpool⟩
    let sm : SubM := ⟨W64 1, o.key, o.e, o.endNil, [], W64 0, ⟨[], [], true, zeroValDef⟩⟩
    wp_apply (wp_writeSub x ks h γh mp v.ι.kv (interface.mkOk tty tv) trc true (σOf ks ops v.ops) []
        (histAt ks ops v.ops) pp _ _ sm (leasesAfter ks ops v.ops) hok0 hlenH hrevH hreachH hLok0 h63H
        (by simp only [List.length_nil]; have := HOps.2.2; omega)
        ⟨fun h => absurd h (show ¬ (W64 1 : w64) = W64 0 by decide), fun _ c hc => by simp at hc⟩
        (fun h => absurd h (show ¬ (W64 1 : w64) = W64 0 by decide)) Hkslen)
      $$ [Hrd Hcmp Htw Htrc Hpp Hlo] as ⟨Hrd, Hcmp, %pend', ⟨%hokP, -, -⟩, Htw, Htrc, Hpp, Hlo⟩
    · iframe; iframe #
      isplitr
      · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hksne2⟩
      iunfold subIs; iframe #
      isplitr
      · iunfold rangeIs; isplitl; · iapply ownSlice_nil
        isplitl; · iapply ownSlice_nil
        ipureintro; exact ⟨rfl, rfl⟩
      ipureintro; exact ⟨rfl, hendNil, rfl, rfl⟩
    (try wp_auto)
    -- `end` at `tw.End`
    have hop : opPend ks (runM ks ops v.ops) o = subStep ks
        (⟨W64 ((histAt ks ops v.ops).length : Int), lastSt (histAt ks ops v.ops), []⟩ : PendM) sm := by
      unfold opPend subStep
      simp only [hk1, sm, ↓reduceIte]
      rfl
    have hcr : cmpAfter ks ops (v.ops + 1) = cmpAfter ks ops v.ops :=
      (runM_succ_pd ks ops v.ops o hov (Or.inr hk1)).1
    obtain ⟨hσ1, hh1⟩ := σOf_succ_commit ks ops v.ops o hov _ (by rw [hop]; exact hokP) hcr
    rw [hop] at hh1
    obtain ⟨-, hhist1, -⟩ := logOk_hist ks Hsorted ops hlogOk (v.ops + 1) (v.ops + 1) (Nat.le_refl _) hvl
    have honce1 := logOk_once ks Hsorted ops hlogOk (v.ops + 1)
    rw [hσ1, hh1] at hhist1
    rw [hσ1] at honce1
    have hb1 : sint.Z (W64 ((σOf ks ops v.ops).rev + 1 : Int)) = (σOf ks ops v.ops).rev + 1 := by word
    have hcrle := commitSt_rev_le (σOf ks ops v.ops) ([] ++ pend')
      (by rw [← hlenH]; have := runM_hs_len ks ops v.ops; unfold histAt; omega)
    ihave Hcb := endCb_txnEnd hpers hTEnd ks γh i mp m v.ι (interface.mkOk kty kvv) qw
      (σOf ks ops v.ops) (v.b.1, W64 ((σOf ks ops v.ops).rev + 1 : Int), v.b.2.2) _ _ trc 1 (etcdStorage v.bk) hpnH
      hhist1 honce1 (by simp only; rw [hb1]; omega)
    ihave Hlead := leadPre_end γh ks ops v.ops lead _ hh1 $$ Hlead
    ihave Hinc : incW ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops)
      (v.b.1, W64 ((σOf ks ops v.ops).rev + 1 : Int), v.b.2.2) $$ [Hret Hσw Hbw]
    · iunfold incW; iframe; iframe #
    wp_apply (wp_end x ks h γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops)
        (v.b.1, W64 ((σOf ks ops v.ops).rev + 1 : Int), v.b.2.2) (histAt ks ops v.ops)
        (compsAt ks ops v.ops) pp _ _ _
        iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
          mvccTxn (interface.mkOk tty tv) v.ι.kv trc
            (.write (σOf ks ops v.ops) ([] ++ pend')) ∗
          mvccBackend v.ι.kv 1 (etcdStorage v.bk) iprop(True))
        (mvccBackend v.ι.kv 1 (etcdStorage v.bk) iprop(True)) lead hokP hlenH hpnH hb1 (by omega))
      $$ [Hrd Hrev Hkv Hinc Hpp Hlead Hcb Htw Hback] as ⟨Hrd, Hrev, Hkv, Hinc, Hr1, Hback, Hlead⟩
    · iframe; iframe #
    (try wp_auto)
    ihave Hrdrs := hR1.2 $$ [$Hrdrs $Hr1]
    obtain ⟨-, hlz, hgz, hcz⟩ := runM_succ_pd ks ops v.ops o hov (Or.inr hk1)
    iapply HΦ
    iframe Hrd Htok
    isplitl [Hlead]
    · iapply leadPost_end γh ks ops v.ops lead _ hh1 hcz; iexact Hlead
    rw [← hσ1, ← hkveq]
    iexists { v with ops := v.ops + 1, b := ((W64 ((σOf ks ops (v.ops + 1)).rev : Int),
      W64 ((σOf ks ops (v.ops + 1)).rev : Int), v.b.2.2) : Bnd) }, k
    isplitr
    · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, by omega⟩
    iunfold memW
    iframe Hops
    isplitl [Happ Hsav]
    · iexists _, _; iunfold hookPre; iframe; ipureintro
      have : sint.Z (W64 ((v.ops + 1 : Nat) : Int)) = v.ops + 1 := by word
      refine ⟨Int.le_refl _, by omega, by simp only; omega⟩
    iunfold memCore
    dsimp only
    rw [← σOf_rev, hcr, hlz, hgz]
    iframe Hid Hhook
    isplitr
    · iunfold hookOk; iframe #; ipureintro; exact Hfnil
    iframe Hpath Hbe Hle Hkv Hrev Hcmp Hopen Hback Hhk Hrdrs Hleases Hbk Hinc
    isplitr
    · ipureintro; exact hvl
    isplitl
    · iunfold lessorW
      iexists rd, r
      rw [hσ1, pendItems_commit]
      iframe; iframe #
      ipureintro; exact Hrecs
    ipureintro; exact HU
  simp only [hk1, _root_.decide_false]
  (try wp_auto)
  by_cases hk2 : o.kind = W64 2
  · -- a transaction
    simp only [hk2, _root_.decide_true]
    (try wp_auto)
    wp_apply (wp_txn x ks cfg wr h γh ops i mp m f v qw nw k p o lead
        (W64 ((v.ops + 1 : Nat) : Int)) s0 hov hk2 hlogOk hnw h38 rfl hsa)
      $$ [Hrd Hmc Happ Hsav Hlead] as ⟨Hrd, Hlead, Hhk, %v', %Hv', Hmc⟩
    · iframe; iframe #; iunfold hookPre; iframe; ipureintro; omega
    (try wp_auto)
    iapply HΦ
    iframe Hrd Hlead Htok
    iexists v', k
    isplitr
    · ipureintro; exact ⟨Hv'.1, Hv'.2, by omega⟩
    iapply memW_of_core ks γh ops i mp m f v' qw nw k v.ops s0 Hv'.2 hn38 hsa
    iframe
  simp only [hk2, _root_.decide_false]
  (try wp_auto)
  by_cases hk3 : o.kind = W64 3
  · -- a grant
    simp only [hk3, _root_.decide_true]
    obtain ⟨hid0, hidg⟩ := hvgrant hk3
    have hinv := runM_inv ks ops hlogOk v.ops
    obtain ⟨-, -, -, ⟨hLsub, -, hgpos, -⟩, -⟩ := hinv
    iunfold memCore at Hmc
    icases Hmc with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
      Hinc, Hopen, Hback, #Hhk, Hrdrs, Hbk, Hles, %HU⟩
    iunfold hookOk at HhookOk
    icases HhookOk with ⟨%Hfnil, #Hhrun⟩
    iunfold bkKeep at Hbk
    icases Hbk with ⟨%HbkP, #Hisb, #Hsc, Hbf, Hoh, HRT, Htoks, Hcen⟩
    ihave ⟨Hles, Hlbk⟩ := lessorW_backend v.ι.kv v.bk f v.lp _ v.U _ Hfnil $$ [$Hles $Hisb $Hhk]
    iunfold lessorW at Hles
    icases Hles with ⟨%rd, %r, #Hlpkg, #Hlinv, #Hlcfg, #Hguard, #Hrevoc, #Hlok, Hlrd, Hlo, Hrvk, Hever,
      #Hreq, Hrdo, Hdel, Hlbe, Hrb, %Hrecs, Hstop, #Hpool⟩
    -- one write-back token
    obtain ⟨k1, rfl⟩ : ∃ k1, k = k1 + 1 := ⟨k - 1, by have := hgk hk3; omega⟩
    icases ownToks_add_1 1 k1 v.bk.γB.wb $$ Htoks with ⟨Htoks, Hwb⟩
    ihave Hwb := (backend.wbTok_toks v.bk.γB).2 $$ Hwb
    ihave #Hgr := lease.leaseGranted_of_guard (mvccLeases v.ι.kv) (fun _ => iprop(True)) o.id $$ [Hguard]
    · iframe #; imodintro; itrivial
    wp_auto
    rw [hid]
    have hnin : o.id ∉ leasesAfter ks ops v.ops := by
      intro h; have := hidg _ (hLsub.subset h); omega
    have hninU : o.id ∉ v.U := by
      intro h; have := hidg _ (HU _ h); omega
    wp_apply (wp_Grant v.lp (mvccLeases v.ι.kv) o.id (W64 3600) (leasesAfter ks ops v.ops)
      (pendItems (σOf ks ops v.ops).log []) iprop(True) f (backend.wbTok v.bk.γB)
      (lease.lessorBeOn v.lp v.bk.be) (apply.bkRT v.bk) (backend.rbPart v.bk.γB (· = leaseName)) r
      (hookPre mp (W64 ((v.ops + 1 : Nat) : Int)) s0)
      iprop(True ∗ hookPost mp (W64 ((v.ops + 1 : Nat) : Int)))
      (hookPost mp (W64 ((v.ops + 1 : Nat) : Int))) v.U)
      $$ [Hlbk Hlo Hrvk Hwb Hlbe HRT Hrb Happ Hsav Hever]
      as %l %err ⟨HRT, Hlbe, Hres⟩
    · iframe Hlinv Hlcfg Hlbk Hlo Hrvk Hwb Hlbe HRT Hrb Hgr Hever
      isplitl [Happ Hsav]
      · iunfold srvApi.csContractA
        isplitl
        · iunfold hookPre; iframe; ipureintro; omega
        isplitl
        · iapply Hhrun
        iintro HQ
        imodintro
        iexact HQ
      iright; ipureintro; exact hninU
    icases Hres with (⟨%Hbad, -⟩ | ⟨%Hok, Hlo, Hrvk, Hpost, -, -, Hmt⟩)
    · exfalso
      rcases Hbad.2 with h | h | h
      · rw [h] at hid0; exact absurd hid0 (by decide)
      · have : sint.Z (W64 3600) = 3600 := by word
        omega
      · exact hnin h
    obtain ⟨rfl, -, -, -, -⟩ := Hok
    icases Hmt with ⟨%mt, -, -, Hrb, Hever, HreqN⟩
    wp_auto
    wp_apply wp_check
    · ipureintro; rfl
    (try wp_auto)
    iunfold hookPost at Hpost
    icases Hpost with ⟨Happ, Hsav⟩
    wp_apply wp_checkHook x mp (W64 ((v.ops + 1 : Nat) : Int)) $$ [$Hsav] as Hsav
    icases Hleases with ⟨%lsl, Hlf, Hlsl, Hlcap⟩
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hlsl $Hlcap $Hosl] as %lsl' ⟨Hlsl, Hlcap, -⟩
    (try wp_auto)
    -- the store's revision: unchanged
    iunfold incW at Hinc
    icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
    ihave #Hmv : isMvcc v.kv v.ι.kv $$ []
    · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H, -⟩; iexact H
    ihave %Hkvs := hsh.1 v.kv v.ι.kv $$ Hmv
    obtain ⟨kty, kvv, hkveq, -, -, hKRev, -⟩ := Hkvs
    ihave #Hmv' : isMvcc (interface.mkOk kty kvv) v.ι.kv $$ []
    · rw [← hkveq]; iexact Hmv
    rw [hkveq]
    have hR1 : mvccReaders (GF := GF) v.ι.kv nw ⊣⊢ mvccReaders v.ι.kv (nw - 1) ∗ mvccReaders v.ι.kv 1 := by
      have := hRdSplit v.ι.kv (nw - 1) 1; rwa [Nat.sub_add_cancel hnw] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    ihave Hau := read_au hpers ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops)
      $$ [Hret Hσw]
    · iframe #; iframe
    wp_apply (hKRev v.ι.kv (fun σ' => iprop(⌜σ' = σOf ks ops v.ops⌝ ∗ ghostVar v.ι.ret qw () ∗
        ghostVar m.σ (1 : Qp).half (σOf ks ops v.ops)))) $$ [Hr1 Hau]
      as %rv ⟨Hr1, %σr, ⟨%Hσr, Hret, Hσw⟩, %Hrv⟩
    · iframe #; iframe
    subst Hσr Hrv
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp [σOf_rev]
    (try wp_auto)
    rw [← hkveq]
    ihave Hrdrs := hR1.2 $$ [$Hrdrs $Hr1]
    obtain ⟨hg1, hg2, hg3, hg4⟩ := runM_succ_grant ks ops v.ops o hov hk3
    have hσ1 := σOf_succ_grant ks ops v.ops o hov hk3
    have hrv1 : revAfter ks ops (v.ops + 1) = revAfter ks ops v.ops := by
      unfold revAfter MSt.rev; unfold histAt at hg1; rw [hg1]
    iapply HΦ
    iframe Hrd Htok
    isplitl [Hlead]
    · unfold leadPre leadPost compsAt
      cases lead
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      · simp only [↓reduceIte]
        have hc : (runM ks ops (v.ops + 1)).comps = (runM ks ops v.ops).comps := by
          rw [runM_succ ks ops v.ops o hov]; unfold opStep; rw [hk3]; simp
        rw [hg1, hc]; iexact Hlead
    iexists { v with ops := v.ops + 1, U := v.U ++ [o.id] }, k1
    isplitr
    · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, by omega⟩
    iunfold memW
    iframe Hops
    isplitl [Happ Hsav]
    · iexists _, _; iunfold hookPre; iframe; ipureintro
      have : sint.Z (W64 ((v.ops + 1 : Nat) : Int)) = v.ops + 1 := by word
      refine ⟨Int.le_refl _, by omega, by simp only; omega⟩
    iunfold memCore
    dsimp only
    rw [hσ1, hrv1, hg2, hg3, hg4]
    have hLid : ∀ l ∈ leasesAfter ks ops v.ops, 0 ≤ sint.Z l ∧ sint.Z l < sint.Z o.id := by
      intro l hl
      have hg := hLsub.subset hl
      exact ⟨by have := hgpos _ hg; omega, hidg _ hg⟩
    have hrecs' := leaseRecsOk_grant r (leasesAfter ks ops v.ops) o.id (lease.grantTTL mt (W64 3600))
      Hrecs hLid hid0 (by have := lease.grantTTL_ge mt (W64 3600); have : sint.Z (W64 3600) = 3600 := by word
                          omega)
    ihave #HreqN := HreqN
    iframe Hid Hhook
    isplitr
    · iunfold hookOk; iframe #; ipureintro; exact Hfnil
    iframe Hpath Hbe Hle Hkv Hrev Hcmp Hopen Hback Hhk Hrdrs
    isplitl [Hlf Hlsl Hlcap]
    · iexists lsl'; iframe
    isplitr
    · ipureintro; exact hvl
    isplitl [Hret Hσw Hbw]
    · iunfold incW; iframe; iframe #
    isplitl [Hbf Hoh HRT Htoks Hcen]
    · iunfold bkKeep; iframe; iframe #; ipureintro; exact HbkP
    isplitl
    · iunfold lessorW
      iexists rd, _
      iframe
      iframe #
      isplitr
      · imodintro; iapply BigSepL.bigSepL_nil.2; itrivial
      ipureintro; exact hrecs'
    ipureintro
    intro id hid'
    rcases List.mem_append.1 hid' with h | h
    · exact List.mem_append_left _ (HU _ h)
    · exact List.mem_append_right _ h
  simp only [hk3, _root_.decide_false]
  (try wp_auto)
  by_cases hk4 : o.kind = W64 4
  · -- a revoke
    simp only [hk4, _root_.decide_true]
    have hidL : o.id ∈ leasesAfter ks ops v.ops := hvrev hk4
    obtain ⟨-, -, -, ⟨hLsub, -, hgpos, -⟩, -⟩ := runM_inv ks ops hlogOk v.ops
    have hid0 : o.id ≠ W64 0 := by
      intro h; have := hgpos _ (hLsub.subset hidL); rw [h] at this; revert this; decide
    iunfold runnerKeys at Hks
    icases Hks with ⟨%keys, #Hkeys, #Hksl, %Hsorted, %Hksne2⟩
    ihave %Hksn := ownSlice_len $$ Hksl
    have hksl : ks.length < 2 ^ 63 := by
      have : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
      have := Hksn.1; have : sint.Z keys.len < 2 ^ 63 := by word
      omega
    obtain ⟨hlenH, hrevH, hreachH, hLok0, h63H, hmatchH, hpnH, hr40, honceH⟩ :=
      member_facts ks Hsorted ops hlogOk hksl v.ops (by omega) h38
    iunfold memCore at Hmc
    icases Hmc with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
      Hinc, Hopen, Hback, #Hhk, Hrdrs, Hbk, Hles, %HU⟩
    iunfold hookOk at HhookOk
    icases HhookOk with ⟨%Hfnil, #Hhrun⟩
    icases leadPre_lb_apply γh ks ops v.ops lead $$ Hlead with ⟨Hlead, #Hlb⟩
    -- `begin`
    rw [← σOf_rev]
    (try wp_auto)
    wp_apply (wp_begin x ks h γh i mp m v.ι v.kv qw (σOf ks ops v.ops) v.b (histAt ks ops v.ops)
      hlenH hpnH (by omega)) $$ [Hrd Hrev Hinc] as %pp ⟨Hrd, Hrev, Hinc, Hpp⟩
    · iframe; iframe #
    (try wp_auto)
    iunfold ownPending at Hpp
    icases Hpp with ⟨%pv, Hpv, %Hprev, Hpst, Hpch, Hpcap⟩
    simp only at Hprev
    (try wp_auto)
    have hmatch_succ : ∀ (n : Nat) (x : GoString) (pr : GoString → Bool), ks[n]? = some x →
        (ks.take (n + 1)).filter pr = (ks.take n).filter pr ++ (if pr x then [x] else []) := by
      intro n x pr hx
      rw [List.take_add_one, hx, List.filter_append]
      cases h : pr x <;> simp [List.filter, h]
    have hkslen : ks.length = sint.nat keys.len := Hksn.1
    -- the keys on the lease, in key order
    ihave HI : (∃ (j : w64) (wsl : GoSlice) (kv0 : GoString),
        "i" ∷ i_ptr ↦ j ∗ "ks" ∷ ks_ptr ↦ wsl ∗
        "Hwl" ∷ wsl ↦* ((ks.take (sint.nat j)).filter (onLease (lastSt (histAt ks ops v.ops)) o.id)) ∗
        "Hwc" ∷ ownSliceCap GoString wsl (DFrac.own 1) ∗ "k" ∷ k_ptr ↦ kv0 ∗
        "Hpst" ∷ pv.st' ↦$ lastSt (histAt ks ops v.ops) ∗ "Hpv" ∷ pp ↦ pv ∗ "p" ∷ p_ptr ↦ pp ∗
        "o" ∷ o_ptr ↦ p ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z keys.len⌝ : IProp GF) $$ [i ks k Hpst Hpv p o]
    · iexists W64 0, slice.nil, _
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil]
      iframe
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      ipureintro; constructor <;> word
    wp_for HI
    by_cases Hlt : sint.Z j < sint.Z keys.len
    · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
      have hjl : sint.nat j < ks.length := by
        rw [hkslen]; have h1 : sint.nat j = (sint.Z j).toNat := rfl
        have h2 : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
        omega
      list_elem ks (sint.nat j) as x
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z keys.len := ⟨Hj.1, Hlt⟩
      (try wp_auto)
      (try simp only [hb, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index keys (sint.Z j) ks DFrac.discard x Hj.1 $$ [Hksl] as -
      · iframe #; ipureintro; exact Hx_lookup
      (try wp_auto)
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      wp_apply (wp_map_lookup2 go.string kvRec.ty pv.st' (lastSt (histAt ks ops v.ops)) x
        (DFrac.own 1)) $$ [$Hpst] as Hpst
      (try wp_auto)
      cases hx : (lastSt (histAt ks ops v.ops)) !! x with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, wsl, x
        rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
        simp only [onLease, hx, Bool.false_eq_true, ↓reduceIte, List.append_nil]
        iframe
        ipureintro; constructor <;> word
      | some ev =>
        simp only [Option.isSome_some, decide_true, Option.getD_some]
        (try wp_auto)
        rw [hid]
        by_cases hev : ev.lease' = o.id
        · simp only [hev, decide_true]
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %osl ⟨Hosl, -⟩
          (try wp_auto)
          wp_apply wp_slice_append $$ [$Hwl $Hwc $Hosl] as %wsl' ⟨Hwl, Hwc, -⟩
          wp_for_post
          iframe
          iexists j + W64 1, wsl', x
          rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
          simp only [onLease, hx, hev, decide_true, ↓reduceIte]
          iframe
          ipureintro; constructor <;> word
        · simp only [hev, decide_false]
          (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, wsl, x
          rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
          simp only [onLease, hx, hev, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
          iframe
          ipureintro; constructor <;> word
    rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hjk : sint.nat j = ks.length := by
      rw [hkslen]; have h1 : sint.nat j = (sint.Z j).toNat := rfl
      have h2 : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
      omega
    rw [hjk, List.take_length]
    (try wp_auto)
    -- their deletes
    generalize hKS : ks.filter (onLease (lastSt (histAt ks ops v.ops)) o.id) = KS
    ihave %Hwln := ownSlice_len $$ Hwl
    have hn : ∀ x : w64, sint.nat x = (sint.Z x).toNat := fun _ => rfl
    ihave HI2 : (∃ (j : w64) (cs : GoSlice) (kv0 : GoString),
        "i" ∷ i_ptr ↦ j ∗ "k" ∷ k_ptr ↦ kv0 ∗
        "Hpv" ∷ pp ↦ { pv with changes' := cs } ∗
        "Hpst" ∷ pv.st' ↦$ delAll (KS.take (sint.nat j)) (lastSt (histAt ks ops v.ops)) ∗
        "Hpch" ∷ cs ↦* ((KS.take (sint.nat j)).map delChange) ∗
        "Hpcap" ∷ ownSliceCap change cs (DFrac.own 1) ∗
        "Hwl" ∷ wsl ↦* KS ∗ "p" ∷ p_ptr ↦ pp ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z wsl.len⌝ : IProp GF)
      $$ [i k Hpv Hpst Hpch Hpcap Hwl p]
    · iexists W64 0, pv.changes', _
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, delAll,
        List.foldl_nil]
      iframe
      ipureintro; constructor <;> word
    wp_for HI2
    by_cases Hlt : sint.Z j < sint.Z wsl.len
    · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
      have hjl : sint.nat j < KS.length := by have := Hwln.1; rw [hn] at this ⊢; omega
      list_elem KS (sint.nat j) as x
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z wsl.len := ⟨Hj.1, Hlt⟩
      (try wp_auto)
      (try simp only [hb, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index wsl (sint.Z j) KS (DFrac.own 1) x Hj.1 $$ [Hwl] as Hwl
      · iframe; ipureintro; exact Hx_lookup
      (try wp_auto)
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have htk1 : KS.take (sint.nat j + 1) = KS.take (sint.nat j) ++ [x] := by
        rw [List.take_add_one, Hx_lookup]; rfl
      wp_apply (wp_mapDelete pv.st' _ x go.string kvRec.ty) $$ [$Hpst] as Hpst
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hpch $Hpcap $Hosl] as %cs' ⟨Hpch, Hpcap, -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, cs', x
      rw [hj1, htk1, delAll_append]
      simp only [List.map_append, List.map_cons, List.map_nil]
      iframe
      ipureintro; constructor <;> word
    rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hjK : sint.nat j = KS.length := by have := Hwln.1; rw [hn] at this ⊢; omega
    rw [hjK, List.take_length]
    (try wp_auto)
    subst hKS
    -- `end`, with the closure calling `Revoke`
    have hok := pendOk_revoke' ks Hsorted (σOf ks ops v.ops) (histAt ks ops v.ops) hmatchH o.id hid0
    have hop : opPend ks (runM ks ops v.ops) o =
        ⟨W64 ((histAt ks ops v.ops).length : Int),
          delAll (ks.filter (onLease (lastSt (histAt ks ops v.ops)) o.id)) (lastSt (histAt ks ops v.ops)),
          (ks.filter (onLease (lastSt (histAt ks ops v.ops)) o.id)).map delChange⟩ :=
      opPend_revoke ks (runM ks ops v.ops) o hk4
    obtain ⟨hcr, hlz, hgz, hcz⟩ := runM_succ_revoke ks ops v.ops o hov hk4
    obtain ⟨hσ1, hh1⟩ := σOf_succ_commit ks ops v.ops o hov _ (by rw [hop]; exact hok) hcr
    rw [hop] at hh1
    obtain ⟨-, hhist1, -⟩ := logOk_hist ks Hsorted ops hlogOk (v.ops + 1) (v.ops + 1) (Nat.le_refl _) hvl
    have honce1 := logOk_once ks Hsorted ops hlogOk (v.ops + 1)
    rw [hσ1, hh1] at hhist1
    rw [hσ1] at honce1
    have hb1 : sint.Z (W64 ((σOf ks ops v.ops).rev + 1 : Int)) = (σOf ks ops v.ops).rev + 1 := by word
    have hcrle := commitSt_rev_le (σOf ks ops v.ops) (leaseDels (stateAfter (σOf ks ops v.ops).log) o.id)
      (by rw [← hlenH]; have := runM_hs_len ks ops v.ops; unfold histAt; omega)
    have hst62 : (stateAfter (σOf ks ops v.ops).log).length ≤ 2 ^ 62 := by
      have := stMatch_length_le' ks _ _ hmatchH (stateAfter_sorted _)
      have := HOps.2.2; omega
    ihave Hpp : ownPending pp ⟨W64 ((histAt ks ops v.ops).length : Int),
        delAll (ks.filter (onLease (lastSt (histAt ks ops v.ops)) o.id)) (lastSt (histAt ks ops v.ops)),
        (ks.filter (onLease (lastSt (histAt ks ops v.ops)) o.id)).map delChange⟩
      $$ [Hpv Hpst Hpch Hpcap]
    · iunfold ownPending; iexists { pv with changes' := cs }; iframe; ipureintro; exact Hprev
    ihave Hlead := leadPre_end γh ks ops v.ops lead _ hh1 $$ Hlead
    iunfold lessorW at Hles
    icases Hles with ⟨%rd, %r, #Hlpkg, #Hlinv, #Hlcfg, #Hguard, #Hrevoc, #Hlok, Hlrd, Hlo, Hrvk, Hever,
      #Hreq, Hrdo, Hdel, Hlbe, Hrb, %Hrecs, Hstop, #Hpool⟩
    iunfold mvccDeleter at Hdel
    icases Hdel with ⟨%Hrdnn, #Hdel⟩
    iunfold bkKeep at Hbk
    icases Hbk with ⟨%HbkP, #Hisb, #Hsc, Hbf, Hoh, HRT, Htoks, Hcen⟩
    have hR1 : mvccReaders (GF := GF) v.ι.kv nw ⊣⊢ mvccReaders v.ι.kv (nw - 1) ∗ mvccReaders v.ι.kv 1 := by
      have := hRdSplit v.ι.kv (nw - 1) 1; rwa [Nat.sub_add_cancel hnw] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    have hR := wp_Revoke v.lp v.ι.kv o.id rd 1 v.bk iprop(True) f (σOf ks ops v.ops)
      (leasesAfter ks ops v.ops) r (hookPre mp (W64 ((v.ops + 1 : Nat) : Int)) s0)
      iprop(True ∗ hookPost mp (W64 ((v.ops + 1 : Nat) : Int))) (hookPost mp (W64 ((v.ops + 1 : Nat) : Int)))
      iprop(ghostVar v.ι.ret qw () ∗
        ghostVar m.σ (1 : Qp).half (commitSt (σOf ks ops v.ops) (leaseDels (stateAfter (σOf ks ops v.ops).log) o.id)) ∗
        ghostVar m.bnd (1 : Qp).half (v.b.1, W64 ((σOf ks ops v.ops).rev + 1 : Int), v.b.2.2))
    dsimp only at hR
    wp_func_lits
    wp_apply (wp_end x ks h γh i mp m v.ι v.kv qw (σOf ks ops v.ops)
        (v.b.1, W64 ((σOf ks ops v.ops).rev + 1 : Int), v.b.2.2) (histAt ks ops v.ops)
        (compsAt ks ops v.ops) pp _ (leaseDels (stateAfter (σOf ks ops v.ops).log) o.id) _
        iprop(mvccReaders v.ι.kv 1 ∗ m_ptr ↦ mp ∗ o_ptr ↦ p ∗ mF go!"le" mp ↦ lease.lessorIface v.lp ∗
          mvccBackend v.ι.kv 1 (etcdStorage v.bk) iprop(True) ∗ lease.rdOwn (mvccLeases v.ι.kv) rd ∗
          hookPre mp (W64 ((v.ops + 1 : Nat) : Int)) s0 ∗
          lease.leaseOwn (mvccLeases v.ι.kv) (leasesAfter ks ops v.ops) (pendItems (σOf ks ops v.ops).log []) ∗
          lease.leaseRevokers (mvccLeases v.ι.kv) (leasesAfter ks ops v.ops) ∗
          backend.rbPart v.bk.γB (· = leaseName) r ∗ lease.lessorBeOn v.lp v.bk.be)
        iprop(m_ptr ↦ mp ∗ o_ptr ↦ p ∗ mF go!"le" mp ↦ lease.lessorIface v.lp ∗
          mvccBackend v.ι.kv 1 (etcdStorage v.bk) iprop(True) ∗ lease.rdOwn (mvccLeases v.ι.kv) rd ∗
          hookPost mp (W64 ((v.ops + 1 : Nat) : Int)) ∗
          lease.leaseOwn (mvccLeases v.ι.kv) ((leasesAfter ks ops v.ops).filter (· != o.id))
            (leaseItemsOf (stateAfter (commitLog (σOf ks ops v.ops).log
              (leaseDels (stateAfter (σOf ks ops v.ops).log) o.id)))) ∗
          lease.leaseRevokers (mvccLeases v.ι.kv) ((leasesAfter ks ops v.ops).filter (· != o.id)) ∗
          backend.rbPart v.bk.γB (· = leaseName) (rbDel r leaseName (u64Le o.id).reverse) ∗
          lease.lessorBeOn v.lp v.bk.be) lead hok hlenH hpnH hb1 (by omega))
      $$ [Hrd Hrev Hkv Hinc Hpp Hlead Hr1 m o Hle Hback Hrdo Happ Hsav Hlo Hrvk Hrb Hlbe]
      as ⟨Hrd, Hrev, Hkv, Hinc, Hr1, ⟨m, o, Hle, Hback, Hrdo, Hpost, Hlo, Hrvk, Hrb, Hlbe⟩, Hlead⟩
    · iframe Hrd Hrev Hkv Hinc Hpp Hlead
      iframe #
      isplitr [Hr1 m o Hle Hback Hrdo Happ Hsav Hlo Hrvk Hrb Hlbe]
      · -- the closure is `end`'s callback
        iunfold endCb
        iintro %Φ' ⟨Hinc, #Hlb', Hr1, m, o, Hle, Hback, Hrdo, Hpre, Hlo, Hrvk, Hrb, Hlbe⟩ HΦ'
        iunfold incW at Hinc
        icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
        ihave Hau := revoke_au hpers ks γh i mp m v.ι v.kv qw (σOf ks ops v.ops)
          (v.b.1, W64 ((σOf ks ops v.ops).rev + 1 : Int), v.b.2.2)
          (leaseDels (stateAfter (σOf ks ops v.ops).log) o.id) _ hpnH hhist1 honce1
          (by simp only; rw [hb1]; omega) $$ [Hret Hσw Hbw]
        · iframe; iframe #
        (try wp_auto)
        rw [hid]
        wp_apply hR $$ [Hr1 Hrdo Hback Hpre Hlo Hrvk Hrb Hlbe Hau]
          as %err ⟨Hr1, Hrdo, Hback, Hlbe, Hres⟩
        · iframe Hlinv Hrevoc Hr1 Hrdo Hback Hhk Hrvk Hrb Hlbe
          isplitr
          · iunfold mvccDeleter; iframe Hdel; ipureintro; exact Hrdnn
          isplitl [Hpre]
          · iunfold srvApi.csContractA
            iframe Hpre
            isplitl
            · iapply Hhrun
            iintro HQ
            imodintro
            iexact HQ
          isplitr
          · ipureintro; exact ⟨hpnH, hst62, hreachH, h63H⟩
          isplitl [Hau]
          · simp only [hidL, decide_true, ↓reduceIte]
            iexact Hau
          isplitl [Hlo]
          · rw [← pendItems_nil]; iexact Hlo
          ipureintro; rw [HbkP.1]; exact mvccrand.rcP_lease _
        icases Hres with (⟨%Hnin, -⟩ | ⟨%Hok2, HY, Hpost, Hlo, Hrvk, Hrb⟩)
        · exact absurd hidL Hnin
        obtain ⟨-, rfl⟩ := Hok2
        (try wp_auto)
        wp_apply wp_check
        · ipureintro; simp
        (try wp_auto)
        iapply HΦ'
        icases HY with ⟨Hret, Hσw, Hbw⟩
        iframe
        iunfold incW; iframe; iframe #
      iframe
      iunfold hookPre; iframe; ipureintro; omega
    -- after `end`: the hook's check, the lease out of the member's leases, `Lookup` nil
    iunfold hookPost at Hpost
    icases Hpost with ⟨Happ, Hsav⟩
    (try wp_auto)
    wp_apply wp_checkHook x mp (W64 ((v.ops + 1 : Nat) : Int)) $$ [$Hsav] as Hsav
    icases Hleases with ⟨%lsl, Hlf, Hlsl, Hlcap⟩
    (try wp_auto)
    ihave %Hlsln := ownSlice_len $$ Hlsl
    ihave HI3 : (∃ (j : w64) (rsl : GoSlice) (id0 : w64),
        "i" ∷ i_ptr ↦ j ∗ "rest" ∷ rest_ptr ↦ rsl ∗
        "Hrl" ∷ rsl ↦* (((leasesAfter ks ops v.ops).take (sint.nat j)).filter (· != o.id)) ∗
        "Hrc" ∷ ownSliceCap w64 rsl (DFrac.own 1) ∗ "id" ∷ id_ptr ↦ id0 ∗
        "Hlsl" ∷ lsl ↦* leasesAfter ks ops v.ops ∗ "o" ∷ o_ptr ↦ p ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z lsl.len⌝ : IProp GF) $$ [i rest id Hlsl o]
    · iexists W64 0, slice.nil, _
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil]
      iframe
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      ipureintro; constructor <;> word
    wp_for HI3
    by_cases Hlt : sint.Z j < sint.Z lsl.len
    · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
      have hjl : sint.nat j < (leasesAfter ks ops v.ops).length := by
        have := Hlsln.1; rw [hn] at this ⊢; omega
      list_elem (leasesAfter ks ops v.ops) (sint.nat j) as x
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z lsl.len := ⟨Hj.1, Hlt⟩
      (try wp_auto)
      (try simp only [hb, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index lsl (sint.Z j) (leasesAfter ks ops v.ops) (DFrac.own 1) x Hj.1
        $$ [Hlsl] as Hlsl
      · iframe; ipureintro; exact Hx_lookup
      (try wp_auto)
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have htk1 : (leasesAfter ks ops v.ops).take (sint.nat j + 1) =
          (leasesAfter ks ops v.ops).take (sint.nat j) ++ [x] := by
        rw [List.take_add_one, Hx_lookup]; rfl
      rw [hid]
      by_cases hxe : x = o.id
      · subst hxe
        simp only [decide_true, Bool.not_true]
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, rsl, o.id
        rw [hj1, htk1, List.filter_append]
        simp only [bne_self_eq_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg,
          List.filter_nil, List.append_nil]
        iframe
        ipureintro; constructor <;> word
      · simp only [hxe, decide_false, Bool.not_false]
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        (try wp_auto)
        wp_apply wp_slice_append $$ [$Hrl $Hrc $Hosl] as %rsl' ⟨Hrl, Hrc, -⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, rsl', x
        rw [hj1, htk1, List.filter_append]
        have hb' : (x != o.id) = true := by simpa using hxe
        simp only [List.filter_cons, hb', ↓reduceIte, List.filter_nil]
        iframe
        ipureintro; constructor <;> word
    rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hjL : sint.nat j = (leasesAfter ks ops v.ops).length := by
      have := Hlsln.1; rw [hn] at this ⊢; omega
    rw [hjL, List.take_length]
    (try wp_auto)
    rw [hid]
    have hlog : (σOf ks ops v.ops).log = logOfHist (histAt ks ops v.ops) := rfl
    rw [← hlog]
    ihave ⟨Hlo, #Hlb0⟩ := lease.leaseOwn_lb (mvccLeases v.ι.kv) _ _ $$ Hlo
    wp_apply (wp_Lookup v.lp (mvccLeases v.ι.kv) o.id 0
        (some ((leasesAfter ks ops v.ops).filter (· != o.id),
          leaseItemsOf (stateAfter (commitLog (σOf ks ops v.ops).log
            (leaseDels (stateAfter (σOf ks ops v.ops).log) o.id))))))
      $$ [Hlrd Hlo] as %l ⟨Hlrd, -, Ho⟩
    · iframe Hlinv Hlrd Hlb0; rw [lease.lookupView_some]; iexact Hlo
    try rw [← hlog]
    ihave ⟨%Hl0, Ho⟩ : iprop(⌜l = null ↔ o.id ∉ (leasesAfter ks ops v.ops).filter (· != o.id)⌝ ∗
        ((⌜l = null⌝ ∗ lease.leaseOwn (mvccLeases v.ι.kv) ((leasesAfter ks ops v.ops).filter (· != o.id))
            (leaseItemsOf (stateAfter (commitLog (σOf ks ops v.ops).log
              (leaseDels (stateAfter (σOf ks ops v.ops).log) o.id))))) ∨
          lease.leaseOwnOpen (mvccLeases v.ι.kv) ((leasesAfter ks ops v.ops).filter (· != o.id))
            (leaseItemsOf (stateAfter (commitLog (σOf ks ops v.ops).log
              (leaseDels (stateAfter (σOf ks ops v.ops).log) o.id)))) o.id l))
      $$ [Ho]
    · rw [← lease.lookupViewAfter_some]; iexact Ho
    have hnin : o.id ∉ (leasesAfter ks ops v.ops).filter (· != o.id) := by simp
    have hlnull : l = null := Hl0.2 hnin
    ihave Hlo : lease.leaseOwn (mvccLeases v.ι.kv) ((leasesAfter ks ops v.ops).filter (· != o.id))
        (leaseItemsOf (stateAfter (commitLog (σOf ks ops v.ops).log
          (leaseDels (stateAfter (σOf ks ops v.ops).log) o.id)))) $$ [Ho]
    · icases Ho with (⟨-, Ho⟩ | Ho)
      · iexact Ho
      · iapply lease.leaseOwnOpen_close $$ Ho
    subst hlnull
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp
    (try wp_auto)
    ihave Hrdrs := hR1.2 $$ [$Hrdrs $Hr1]
    iapply HΦ
    iframe Hrd Htok
    isplitl [Hlead]
    · iapply leadPost_end γh ks ops v.ops lead _ hh1 hcz; iexact Hlead
    rw [← hσ1]
    iexists { v with ops := v.ops + 1, b := ((W64 ((σOf ks ops (v.ops + 1)).rev : Int),
      W64 ((σOf ks ops (v.ops + 1)).rev : Int), v.b.2.2) : Bnd) }, k
    isplitr
    · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, by omega⟩
    iunfold memW
    iframe Hops
    isplitl [Happ Hsav]
    · iexists _, _; iunfold hookPre; iframe; ipureintro
      have : sint.Z (W64 ((v.ops + 1 : Nat) : Int)) = v.ops + 1 := by word
      refine ⟨Int.le_refl _, by omega, by simp only; omega⟩
    iunfold memCore
    dsimp only
    rw [← σOf_rev, hcr, hlz, hgz]
    iframe Hid Hhook
    isplitr
    · iunfold hookOk; iframe #; ipureintro; exact Hfnil
    iframe Hpath Hbe Hle Hkv Hrev Hcmp Hopen Hback Hhk Hrdrs Hinc
    isplitl [Hlf Hrl Hrc]
    · iexists rsl; iframe
    isplitr
    · ipureintro; exact hvl
    isplitl [Hbf Hoh HRT Htoks Hcen]
    · iunfold bkKeep; iframe; iframe #; ipureintro; exact HbkP
    isplitl
    · iunfold lessorW
      iexists rd, _
      rw [hσ1, pendItems_nil, commitSt_log]
      iframe; iframe #
      isplitr
      · iunfold mvccDeleter; iframe Hdel; ipureintro; exact Hrdnn
      ipureintro; exact leaseRecsOk_revoke r _ o.id Hrecs
    ipureintro; exact HU
  simp only [hk4, _root_.decide_false]
  (try wp_auto)
  by_cases hk5 : o.kind = W64 5
  · -- a compaction
    simp only [hk5, _root_.decide_true]
    (try wp_auto)
    wp_apply (wp_compact x ks cfg wr h γh ops i mp m f v qw nw k p o lead
        (W64 ((v.ops + 1 : Nat) : Int)) s0 hov hk5 hlogOk h38 rfl hsa)
      $$ [Hmc Happ Hsav Hlead] as ⟨Hlead, Hhk, %v', %Hv', Hmc⟩
    · iframe; iframe #; iunfold hookPre; iframe; ipureintro; omega
    (try wp_auto)
    iapply HΦ
    iframe Hrd Hlead Htok
    iexists v', k
    isplitr
    · ipureintro; exact ⟨Hv'.1, Hv'.2, by omega⟩
    iapply memW_of_core ks γh ops i mp m f v' qw nw k v.ops s0 Hv'.2 hn38 hsa
    iframe
  simp only [hk5, _root_.decide_false]
  (try wp_auto)
  by_cases hk6 : o.kind = W64 6
  · -- a commit
    simp only [hk6, _root_.decide_true]
    iunfold memCore at Hmc
    icases Hmc with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
      Hinc, Hopen, Hback, #Hhk, Hrdrs, Hbk, Hles, %HU⟩
    iunfold incW at Hinc
    icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
    ihave #Hmv : isMvcc v.kv v.ι.kv $$ []
    · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H, -⟩; iexact H
    ihave %Hkvs := hsh.1 v.kv v.ι.kv $$ Hmv
    obtain ⟨kty, kvv, hkveq, -, -, -, -, -, -, -, -, hKCommit, -, -, -⟩ := Hkvs
    ihave #Hmv' : isMvcc (interface.mkOk kty kvv) v.ι.kv $$ []
    · rw [← hkveq]; iexact Hmv
    ihave Hkv : mF go!"kv" mp ↦{DFrac.own qw} interface.mkOk kty kvv $$ [Hkv]
    · rw [← hkveq]; iexact Hkv
    have hR1 : mvccReaders (GF := GF) v.ι.kv nw ⊣⊢ mvccReaders v.ι.kv (nw - 1) ∗ mvccReaders v.ι.kv 1 := by
      have := hRdSplit v.ι.kv (nw - 1) 1; rwa [Nat.sub_add_cancel hnw] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    wp_auto
    wp_apply (hKCommit v.ι.kv 1 _ iprop(True) iprop(True) iprop(True)) $$ [Hr1 Hback]
      as ⟨Hr1, Hback, -⟩
    · iframe #; iframe
      isplitr; · itrivial
      rw [etcdStorage_req]; iapply backend.commitReq_true
    (try wp_auto)
    ihave Hrdrs := hR1.2 $$ [$Hrdrs $Hr1]
    ihave Hkv : mF go!"kv" mp ↦{DFrac.own qw} v.kv $$ [Hkv]
    · rw [hkveq]; iexact Hkv
    ihave Hinc : incW ks γh i mp m v.ι v.kv qw (σOf ks ops v.ops) v.b $$ [Hret Hσw Hbw]
    · iunfold incW; iframe; iframe #
    iapply HΦ
    iframe Hrd Htok
    iapply apply_close_same ks γh ops i mp m f v qw nw k lead s0
      (runM_succ_same ks ops v.ops o hov (Or.inl hk6)) hvl hn38 hsa'
    iframe
    iunfold memCore; dsimp only; iframe; iframe #
    ipureintro; exact ⟨Hvops, HU⟩
  simp only [hk6, _root_.decide_false]
  (try wp_auto)
  by_cases hk7 : o.kind = W64 7
  · -- a read
    simp only [hk7, _root_.decide_true]
    iunfold runnerKeys at Hks
    icases Hks with ⟨%keys, #Hkeys, #Hksl, %Hsorted, %Hksne2⟩
    iunfold memCore at Hmc
    icases Hmc with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
      Hinc, Hopen, Hback, #Hhk, Hrdrs, Hbk, Hles, %HU⟩
    iunfold incW at Hinc
    icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
    ihave #Hmv : isMvcc v.kv v.ι.kv $$ []
    · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H, -⟩; iexact H
    ihave %Hkvs := hsh.1 v.kv v.ι.kv $$ Hmv
    obtain ⟨kty, kvv, hkveq, hKR, -⟩ := Hkvs
    obtain ⟨-, -, hreach⟩ := logOk_hist ks Hsorted ops hlogOk v.ops v.ops (Nat.le_refl _) Hvops
    obtain ⟨hl2, hc1, hcr⟩ := reach_bounds _ hreach
    have hhl : 2 ≤ (histAt ks ops v.ops).length ∧ (histAt ks ops v.ops).length ≤ v.ops + 2 :=
      runM_hs_len ks ops v.ops
    have hσl : (σOf ks ops v.ops).log.length = (histAt ks ops v.ops).length := by
      simp [σOf, logOfHist]
    have hcmpA : (σOf ks ops v.ops).crev = cmpAfter ks ops v.ops := rfl
    have hrevlt : (revAfter ks ops v.ops : Int) < 2 ^ 40 := by
      have : (σOf ks ops v.ops).rev = (σOf ks ops v.ops).log.length - 1 := rfl
      have := σOf_rev ks ops v.ops
      omega
    have hrZ : sint.Z (W64 (revAfter ks ops v.ops : Int)) = revAfter ks ops v.ops := by word
    have hcZ : sint.Z (W64 (cmpAfter ks ops v.ops)) = cmpAfter ks ops v.ops := by
      have : cmpAfter ks ops v.ops ≤ revAfter ks ops v.ops := by rw [← hcmpA, ← σOf_rev]; omega
      have : -1 ≤ cmpAfter ks ops v.ops := by rw [← hcmpA]; omega
      word
    have hR1 : mvccReaders (GF := GF) v.ι.kv nw ⊣⊢ mvccReaders v.ι.kv (nw - 1) ∗ mvccReaders v.ι.kv 1 := by
      have := hRdSplit v.ι.kv (nw - 1) 1; rwa [Nat.sub_add_cancel hnw] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    (try wp_auto)
    wp_apply wp_traceTODO $$ [$Hpkt] as %trc ⟨%Htrc, Htrco⟩
    (try wp_auto)
    ihave Hau := read_au hpers ks γh i mp m v.ι v.kv qw (σOf ks ops v.ops) $$ [Hret Hσw]
    · iframe #; iframe
    rw [hkveq]
    wp_apply (hKR v.ι.kv (W32 1) trc true (fun σ => iprop(⌜σ = σOf ks ops v.ops⌝ ∗
        ghostVar v.ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half (σOf ks ops v.ops))))
      $$ [Hr1 Htrco Hau] as %tx ⟨Htrco, %σr, Htx, %Hσr, Hret, Hσw⟩
    · iframe #; iframe; ipureintro; exact Htrc
    subst Hσr
    ihave %Htxs := hsh.2.2.1 tx v.ι.kv trc (.read (σOf ks ops v.ops)) $$ Htx
    obtain ⟨tty, tv, htx, hTRev, hTFR, hTRange, -, -, -, hTEnd⟩ := Htxs
    subst htx
    (try wp_auto)
    wp_apply (hTRev v.ι.kv trc (.read (σOf ks ops v.ops))) $$ [Htx] as Htx
    · iframe #; iframe
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp [MTxn.state, σOf_rev]
    (try wp_auto)
    wp_apply (hTFR v.ι.kv trc (.read (σOf ks ops v.ops))) $$ [Htx] as Htx
    · iframe #; iframe
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp [σOf]
    (try wp_auto)
    -- `tr.Range(…)` of the op's request
    ihave ⟨#Hqk, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.rangeReq.rangeReq_access_load_key
      (p.[op, go!"q"]) ov.q' DFrac.discard).access_strict $$ Hfq
    ihave ⟨#Hqe, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.rangeReq.rangeReq_access_load_end
      (p.[op, go!"q"]) ov.q' DFrac.discard).access_strict $$ Hfq
    ihave ⟨#Hqro, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.rangeReq.rangeReq_access_load_ro
      (p.[op, go!"q"]) ov.q' DFrac.discard).access_strict $$ Hfq
    iunfold rangeIs at Hoq
    icases Hoq with ⟨#Hqks, #Hqes, %Hqp⟩
    wp_apply wp_ctxTODO
    (try wp_auto)
    ihave #Hctxr : mvcc.rangeCtx true todoCtxVal
        ({ Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) } :
          context.ContextDesc (IProp GF)) $$ []
    · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
    wp_apply (hTRange v.ι.kv trc true (.read (σOf ks ops v.ops)) todoCtxVal _ true ov.q'.key' ov.q'.end'
        o.q.key o.q.e ov.q'.ro') $$ [Htx Htrco Hqks Hqes]
      as %rr' %err ⟨%Hrn, Htx, Htrco, Hout, -, %Hlwf⟩
    · iframe #; iframe
    (try wp_auto)
    -- `checkRangeAt(x.keys, x.h.snapshot(), …)`
    icases leadPre_lb_apply γh ks ops v.ops lead $$ Hlead with ⟨Hlead, #Hlb⟩
    iunfold runnerH at HH
    (try wp_auto)
    wp_apply wp_snapshot h γh (histAt ks ops v.ops) $$ [$Hrd $Hlb]
      as %s ⟨Hrd, %ms, %Hs', ⟨%Hpre, %H2⟩, %Hscap, #Hlb', #Hms, #Hst⟩
    ihave %Hmlen : ⌜ms.length = Hs'.length⌝ $$ [Hst]
    · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
    ihave #HstAt := apply_statesAt_hist ms Hs' $$ Hst
    have hle : (histAt ks ops v.ops).length ≤ Hs'.length := Hpre.length_le
    have hmatch := apply_hist_match ks Hsorted ops hlogOk v.ops Hvops Hs' Hpre
    have hne : (σOf ks ops v.ops).log ≠ [] := by
      intro h0; have := congrArg List.length h0; simp only [List.length_nil] at this; omega
    have hcurlt : sint.nat (W64 (revAfter ks ops v.ops : Int)) < ms.length := by
      have : sint.nat (W64 (revAfter ks ops v.ops : Int)) =
        (sint.Z (W64 (revAfter ks ops v.ops : Int))).toNat := rfl
      rw [this, hrZ]
      have : (σOf ks ops v.ops).rev = (σOf ks ops v.ops).log.length - 1 := rfl
      have := σOf_rev ks ops v.ops
      omega
    have hM : ∀ r : Nat, sint.Z (W64 (cmpAfter ks ops v.ops)) ≤ (r : Int) →
        r ≤ sint.nat (W64 (revAfter ks ops v.ops : Int)) →
        ∃ M, (Hs'.map Prod.fst)[r]? = some M ∧ stMatch ks M (stateAt (σOf ks ops v.ops).log r) := by
      intro r _ hr
      have : sint.nat (W64 (revAfter ks ops v.ops : Int)) =
        (sint.Z (W64 (revAfter ks ops v.ops : Int))).toNat := rfl
      rw [this, hrZ] at hr
      have : (σOf ks ops v.ops).rev = (σOf ks ops v.ops).log.length - 1 := rfl
      have := σOf_rev ks ops v.ops
      exact hmatch r (by omega)
    have hrr : (MTxn.read (σOf ks ops v.ops)).readRev = W64 (revAfter ks ops v.ops : Int) := by
      simp only [MTxn.readRev, σOf_rev]
    have hrl : (MTxn.read (σOf ks ops v.ops)).readLog = (σOf ks ops v.ops).log := rfl
    have hcs : (MTxn.read (σOf ks ops v.ops)).state.crev = sint.Z (W64 (cmpAfter ks ops v.ops)) := by
      rw [hcZ]; rfl
    rw [hrr, hrl, hcs] at *
    have hLog : txn.LogOk (σOf ks ops v.ops).log :=
      txn.LogOk.of_cert ⟨Hlwf.1, by omega, Hlwf.2⟩ hne
    (try wp_auto)
    wp_apply (wp_checkRangeAt keys ks DFrac.discard s DFrac.discard ms (Hs'.map Prod.fst)
        (List.replicate Hs'.length DFrac.discard) (W64 (revAfter ks ops v.ops : Int))
        (W64 (cmpAfter ks ops v.ops)) _ o.q.key o.q.e DFrac.discard DFrac.discard rr' err
        (σOf ks ops v.ops).log Hsorted hLog (by rw [hrZ]; omega) hcurlt hM)
      $$ [Hksl Hms HstAt Hout Hqks Hqes] as -
    · rw [hcZ]; iframe #; iframe; ipureintro; exact Hrn rfl
    (try wp_auto)
    wp_apply (end_readT hTEnd v.ι.kv trc (σOf ks ops v.ops)) $$ [Htx] as Hr1
    · iframe #; iframe
    (try wp_auto)
    ihave Hrdrs := hR1.2 $$ [$Hrdrs $Hr1]
    rw [← hkveq]
    ihave Hinc : incW ks γh i mp m v.ι v.kv qw (σOf ks ops v.ops) v.b $$ [Hret Hσw Hbw]
    · iunfold incW; iframe; iframe #
    iapply HΦ
    iframe Hrd Htok
    iapply apply_close_same ks γh ops i mp m f v qw nw k lead s0
      (runM_succ_same ks ops v.ops o hov (Or.inr (Or.inl hk7))) hvl hn38 hsa'
    iframe
    iunfold memCore; dsimp only; iframe; iframe #
    ipureintro; exact ⟨Hvops, HU⟩
  simp only [hk7, _root_.decide_false]
  (try wp_auto)
  -- the leases' check
  have hk8 : o.kind = W64 8 := by word
  icases leadPre_lb_apply γh ks ops v.ops lead $$ Hlead with ⟨Hlead, #Hlb⟩
  wp_apply (wp_checkLeases x ks cfg wr h γh ops i mp m f v qw nw k hlogOk) $$ [Hrd Hmc Htok]
    as ⟨Hrd, Hmc, Htok⟩
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iframe Hrd Htok
  iapply apply_close_same ks γh ops i mp m f v qw nw k lead s0
    (runM_succ_same ks ops v.ops o hov (Or.inr (Or.inr (Or.inl hk8)))) hvl hn38 hsa'
  iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
