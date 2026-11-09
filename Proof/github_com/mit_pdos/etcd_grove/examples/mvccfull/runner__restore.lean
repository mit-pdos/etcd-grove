/- Lean-first (no Rocq counterpart). The proof of `runner.restore`: Draft, to come.

The outline: as the file header, in Go's order: `buildPath`, `newMember(2, …)`, `apply` per
operation (the history's lower bound from the leader's `histW`), the builder's `inc_retire` and
`shut`; `revHi`/`cmpHi` stored (`incW` of the follower: above the builder's, `runM_mono`);
`openBackend`, `inc_open_backend`; `lessor.Recover`; `KV.Restore.contract` (its update at the
follower's incarnation invariant: `σOf … v0.ops`, `histOkM` from `logOk_hist`, `onceUpToAll` from
`logOk_once`); `SetTxPostLockInsideApplyHook`, the hook frozen; the old backend's census
(`bkCensus` with `Restore`'s `storageRest`) and `backend.Close`; the fields; `revLo`/`cmpLo`;
`KV.Rev`, `KV.Read`, `Txn.FirstRev`, `Txn.End`; `checkLeases`; the counter.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__restore
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.RestoreLemmas
public import Perennial.Spec.sync.atomic.Int64__Add
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.buildPath
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__newMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__shut
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__openBackend
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkLeases
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Recover
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SetTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Close
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO

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

theorem runner.restore.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (halloc : mvccW_alloc.law (GF := GF))
    (hopen : etcdStorage_open.law (GF := GF))
    (hrest : backendRest_open.law (GF := GF))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (wp_buildPath : buildPath.spec (GF := GF) (hG := hG))
    (wp_newMember : runner.newMember.spec (GF := GF) (hG := hG))
    (wp_apply : runner.apply.spec (GF := GF) (hG := hG))
    (wp_shut : runner.shut.spec (GF := GF) (hG := hG))
    (wp_openBackend : runner.openBackend.spec (GF := GF) (hG := hG))
    (wp_Recover : lease.lessor.Recover.spec (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_SetHook : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (wp_bClose : backend.backend.Close.spec (GF := GF) (hG := hG))
    (wp_checkLeases : runner.checkLeases.spec (GF := GF) (hG := hG)) :
    runner.restore.spec (GF := GF) (hG := hG) := by
  intro _ _ x ks cfg wr h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs hlt hlen hOps hOps38 hdbo hdbc hck hlim hcbl
  haveI : Persistent (runnerMs (GF := GF) x mp0 mp1) := by unfold runnerMs; infer_instance
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  haveI := isInc_persistent hpers
  haveI := hpers.1
  haveI : Persistent (rnCtx (GF := GF) x ks cfg h γ.h) := by
    unfold rnCtx runnerKeys runnerH ctrInv; infer_instance
  haveI : Persistent (runnerCfg (GF := GF) x cfg wr) := by
    unfold runnerCfg runnerRangeMix; infer_instance
  haveI : Persistent (rdShared (GF := GF) x) := by unfold rdShared ctrInv; infer_instance
  haveI : Persistent (runnerKeys (GF := GF) x ks) := by unfold runnerKeys; infer_instance
  haveI : Persistent (runnerH (GF := GF) x h) := by unfold runnerH; infer_instance
  wp_start as ⟨#Hctx, #Hks, #Hvoff, Htok, Hw⟩
  ihave #HctxK : writerCtx x ks cfg wr h γ.h $$ []
  · iexact Hctx
  ihave #HrnK : rnCtx x ks cfg h γ.h $$ []
  · iunfold writerCtx at Hctx; icases Hctx with ⟨#H, -⟩; iexact H
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hrn, #Hcfg, %Hmix, #Hrds, #Hpb, #Hps, #Hpl, #Hpt, %Hksl, #Hlg, #Hwo, #Hwc,
    #Hws, #Hcrev, #Hccmp, #Hcres, #Hcrst⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hpm, #Hkeys, %Hkne, #HrH, #Hhist, #Hcfgp, #Hwa, #Hwst, #Hce, #Hcp, #Hcc, #Hccn⟩
  iunfold writerOwn at Hw
  icases Hw with ⟨#Hms, #Hreg0, #Hreg1, Hlog, Hctrs, HhW, Hrd, %Hops, %Hnb, Hfiles,
    ⟨%qw0, %nw0, %k0, Hm0, %Hl0⟩, ⟨%qw1, %nw1, %k1, Hm1, %Hl1⟩, Hss0, Hss1, Hadd⟩
  iunfold logOwn at Hlog
  icases Hlog with ⟨%lsl, %lps, Hlog1, Hlog2, Hlog3, %Hlogp, Hlog4⟩
  have hlogOk := Hlogp.2
  icases histW_lb γ.h _ _ $$ HhW with ⟨HhW, #Hlb⟩
  have hnb : nb < v0.ops := by
    rcases Nat.lt_or_ge nb v0.ops with h' | h'
    · exact h'
    · exfalso; have := Hnb.2 (by omega); omega
  -- `x.builds++`
  iunfold writerCtrs at Hctrs
  icases Hctrs with ⟨%nl, Hnl, Hvals, Hbuilds, %Hnl'⟩
  ihave #Hcfgf : rF go!"cfg" x ↦□ cfg $$ []
  · iexact Hcfgp
  icases typedPointsto_split _ _ _ $$ Hcfgf with #Hcfgf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcfgf
  wp_auto
  have hnb1 : sint.Z (W64 (nb : Int) + W64 1) = (nb : Int) + 1 := by
    have : nb < 2 ^ 38 := by omega
    word
  wp_apply wp_buildPath cfg.Prefix' (W64 (nb : Int) + W64 1) (by omega)
  (try wp_auto)
  have hbn : sint.nat (W64 (nb : Int) + W64 1) = nb + 1 := by
    have : sint.nat (W64 (nb : Int) + W64 1) = (sint.Z (W64 (nb : Int) + W64 1)).toNat := rfl
    omega
  rw [hbn]
  -- the builder's file: the first unused
  have hOn : (sint.Z cfg.Ops').toNat - nb = ((sint.Z cfg.Ops').toNat - (nb + 1)) + 1 := by omega
  rw [hOn, List.range'_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hfiles with ⟨Hbf, Hfiles⟩
  have hp0 : hist0 <+: histAt ks ops ops.length := by
    have := runM_hs_prefix ks ops 0 ops.length (Nat.zero_le _)
    rwa [show histAt ks ops 0 = hist0 from rfl] at this
  wp_apply (wp_newMember x ks cfg wr h γ.h (W64 2) (buildPathM cfg.Prefix' (nb + 1)) (by decide)
      (by decide) hdbo hck hlim hcbl) $$ [Htok Hrd Hbf]
    as %mpb ⟨Htok, Hrd, %mb, %fb, %vb, %kb, %Hvb, Hmb, Hstb, #Hregb⟩
  · iframe #; iframe
    iapply (monoListLbOwn_le _ hp0); iexact Hlb
  ispecialize Hmb $$ %ops
  (try wp_auto)
  iunfold memW at Hm0
  icases Hm0 with ⟨Hops0, Hhk0, Hc0⟩
  icases Hlog4 with #Hlog4
  have hNpos : 1 ≤ mvccReaderN := by have := Hl0.1.2; have := Hl0.2.1; omega
  -- the builder applies the log up to the leader's count
  ihave HI : (∃ (vb' : MemS) (kb' : Nat),
      "b" ∷ b_ptr ↦ mpb ∗ "Hmb" ∷ memW ks γ.h ops 2 mpb mb fb vb' 1 mvccReaderN kb' ∗
      "Hrd" ∷ histRd h γ.h ∗
      "%Hvb'" ∷ ⌜vb'.ops ≤ v0.ops ∧ (sint.Z cfg.Ops').toNat ≤ kb' + vb'.ops ∧
        vb'.path = buildPathM cfg.Prefix' (nb + 1)⌝ : IProp GF) $$ [b Hmb Hrd]
  · iexists vb, kb; iframe; ipureintro; exact ⟨by omega, by omega, Hvb.2.1⟩
  wp_for HI
  iunfold memW at Hmb
  icases Hmb with ⟨Hbops, Hbhk, Hbc⟩
  wp_auto
  have hb38 : vb'.ops < 2 ^ 38 := by omega
  have h038 : v0.ops < 2 ^ 38 := by omega
  by_cases Hlt : vb'.ops < v0.ops
  · -- an iteration: `x.apply(b, x.log[b.ops], false)`
    have hlt' : sint.Z (W64 (vb'.ops : Int)) < sint.Z (W64 (v0.ops : Int)) := by word
    simp only [hlt', decide_true, ↓reduceIte]
    obtain ⟨o, ho⟩ : ∃ o, ops[vb'.ops]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨p, hp⟩ : ∃ p, lps[vb'.ops]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hz : (lps.zip ops)[vb'.ops]? = some (p, o) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hp, ho⟩
    ihave #Hop := BigSepL.bigSepL_lookup hz $$ Hlog4
    ihave %Hlsl := ownSlice_len lsl _ lps $$ Hlog2
    wp_auto
    have hb : 0 ≤ sint.Z (W64 (vb'.ops : Int)) ∧ sint.Z (W64 (vb'.ops : Int)) < sint.Z lsl.len := by
      have : sint.Z (W64 (vb'.ops : Int)) = vb'.ops := by word
      rw [this]; have h1 := Hlsl.1; have h2 := Hlogp.1
      have h3 : sint.nat lsl.len = (sint.Z lsl.len).toNat := rfl
      omega
    simp only [hb, _root_.and_self, ↓reduceIte]
    have hvz : (sint.Z (W64 (vb'.ops : Int))).toNat = vb'.ops := by
      have : sint.Z (W64 (vb'.ops : Int)) = vb'.ops := by word
      omega
    wp_apply wp_load_slice_index lsl (sint.Z (W64 (vb'.ops : Int))) lps (DFrac.own 1) p hb.1
      $$ [Hlog2] as Hlog2
    · iframe; ipureintro; rw [hvz]; exact hp
    (try wp_auto)
    have hgr : o.kind = kGrant → 1 ≤ kb' := fun _ => by omega
    wp_apply (wp_apply x ks cfg wr h γ.h ops 2 mpb mb fb vb' 1 mvccReaderN kb' p o false ho hlogOk
        hNpos hgr hlen) $$ [Hrd Hbops Hbhk Hbc] as ⟨Hrd, -, %v', %k', %Hv', Hmb⟩
    · iframe #; iframe
      isplitl
      · iunfold memW; iframe
      · iunfold leadPre; simp only [Bool.false_eq_true, ↓reduceIte]
        iapply (monoListLbOwn_le _ (runM_hs_prefix ks ops (vb'.ops + 1) ops.length (by omega)))
        iexact Hlb
    (try wp_auto)
    wp_for_post
    iframe
    iexists v', k'
    iframe
    ipureintro
    obtain ⟨⟨hpath, -⟩, hv1, hk⟩ := Hv'
    exact ⟨by omega, by omega, by rw [hpath]; exact Hvb'.2.2⟩
  · have hge : ¬ sint.Z (W64 (vb'.ops : Int)) < sint.Z (W64 (v0.ops : Int)) := by word
    simp only [hge, decide_false, intoVal_eq_iff, Bool.false_eq_true, decide_false,
      ↓reduceIte]
    have hveq : vb'.ops = v0.ops := by omega
    (try wp_auto)
    (try simp only [decide_True_any, ↓reduceIte])
    (try wp_auto)
    -- the builder retired (no reader or stream ever had a share) and shut: its file the image
    iunfold memCore at Hbc
    simp only []
    icases Hbc with ⟨#Hidb, #Hhookb, -, Hpathb, Hbeb, Hleb, Hkvb, Hrevb, Hcmpb, Hleasesb, %Hvopsb,
      Hincb, Hopenb, Hbackb, -, Hrdrsb, Hbkb, Hlesb, -⟩
    iunfold incW at Hincb
    icases Hincb with ⟨#Hisincb, Hretb, Hσwb, Hbwb⟩
    imod inc_retire hpers ks γ.h 2 mpb mb vb'.ι vb'.kv $$ [Hretb] with Hmsb
    · iframe #; iframe
    icases (memberState_split ks γ.h mpb mb vb'.ι.kv).1 $$ Hmsb with ⟨%σb, %bb, %Hlb', Hσb, Hcarry⟩
    iunfold memberCarry at Hcarry
    icases Hcarry with ⟨Hσc, -, -, -, -, -, -, -, -, -, %Hcpb⟩
    ihave %Hag := ghostVar_agree mb.σ _ _ _ _ $$ Hσwb Hσc
    subst Hag
    iunfold lessorW at Hlesb
    icases Hlesb with ⟨%rdb, %rb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Hrbb, %Hrecsb, Hstopb⟩
    wp_apply (wp_shut x ks cfg wr h γ.h mpb vb'.path vb'.bk vb'.lp vb'.kv vb'.ι.kv
        (σOf ks ops vb'.ops) (leasesAfter ks ops vb'.ops) rb kb' hdbc rfl Hrecsb)
      $$ [Hkvb Hleb Hbeb Hopenb Hrdrsb Hbackb Hσb Hbkb Hstopb Hrbb]
      as ⟨-, -, -, %D, %u, Hfile, Himg, %HrecD⟩
    · iframe #; iframe
      iunfold isInc at Hisincb; icases Hisincb with ⟨-, #H⟩; iexact H
    (try wp_auto)
    -- the follower's bounds raised to the builder's (`revHi`, `cmpHi`), in its incarnation
    iunfold memW at Hm1
    icases Hm1 with ⟨Hops1, Hhk1, Hc1⟩
    iunfold memCore at Hc1
    simp only []
    icases Hc1 with ⟨#Hid1, #Hhook1, HhookOk1, Hpath1, Hbe1, Hle1, Hkv1, Hrev1, Hcmp1, Hleases1,
      %Hvops1, Hinc1, Hopen1, Hback1, HhookIs1, Hrdrs1, Hbk1, Hles1, %HU1⟩
    iunfold incW at Hinc1
    icases Hinc1 with ⟨#Hisinc1, Hret1, Hσw1, Hbw1⟩
    have hrb : revAfter ks ops vb'.ops < 2 ^ 39 := by
      have := runM_hs_len ks ops vb'.ops; unfold revAfter MSt.rev; omega
    have hrbZ : sint.Z (W64 (revAfter ks ops vb'.ops : Int)) = revAfter ks ops vb'.ops := by word
    have hrf := revAfter_mono ks ops v1.ops vb'.ops (by omega)
    have hlenf : (σOf ks ops v1.ops).log.length = revAfter ks ops v1.ops + 1 := by
      rw [← σOf_rev]; unfold MvccState.rev
      have := runM_hs_len ks ops v1.ops
      simp only [σOf, logOfHist, List.length_map]; unfold histAt at this ⊢; omega
    wp_apply_core sync.atomic.Int64.wp_Store (mF go!"revHi" mp1)
      (W64 (revAfter ks ops vb'.ops : Int)) $$ [] [-]
    · iPkgInit
    imod bnd_acc hpers ks γ.h 1 mp1 γ.m1 v1.ι v1.kv qw1 (σOf ks ops v1.ops) v1.b
      $$ [Hret1 Hσw1 Hbw1] with ⟨%Hlf, %Hokf, Hrl, Hrh, Hcl, Hch, Hcls⟩
    · iframe #; iframe
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(memberN 1) from Std.LawfulSet.empty_subset)
    iintro Hcl2
    inext
    iexists _
    iframe Hrh
    iintro Hrh
    imod Hcl2 with -
    let b1 : Bnd := (v1.b.1, W64 (revAfter ks ops vb'.ops : Int), v1.b.2.2.1, v1.b.2.2.2)
    have hok1 : bndOk ks (σOf ks ops v1.ops) b1 Hlf := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hokf
      refine ⟨h1, h2, ?_, ?_, ?_, h6, h7, h8, h9, h10⟩
      · show ((σOf ks ops v1.ops).rev : Int) ≤ sint.Z (W64 (revAfter ks ops vb'.ops : Int))
        rw [hrbZ, σOf_rev]; omega
      · show sint.Z (W64 (revAfter ks ops vb'.ops : Int)) < 2 ^ 62
        rw [hrbZ]; omega
      · show (((σOf ks ops v1.ops).notifiedLog.length : Nat) : Int) ≤
          sint.Z (W64 (revAfter ks ops vb'.ops : Int)) + 1
        rw [hrbZ, σOf_notified, hlenf]; omega
    imod Hcls $$ %b1 %hok1 Hrl Hrh Hcl Hch with ⟨Hret1, Hσw1, Hbw1⟩
    imodintro
    (try wp_auto)
    have hcb1 : -1 ≤ cmpAfter ks ops vb'.ops := Hcpb.2.2.2.2.2.2.2.1
    have hcb2 : cmpAfter ks ops vb'.ops ≤ sint.Z bb.2.2.2 := Hcpb.2.2.2.2.2.2.1
    have hcbZ : sint.Z (W64 (cmpAfter ks ops vb'.ops)) = cmpAfter ks ops vb'.ops := by word
    have hcf := cmpAfter_mono ks ops v1.ops vb'.ops (by omega)
    wp_apply_core sync.atomic.Int64.wp_Store (mF go!"cmpHi" mp1)
      (W64 (cmpAfter ks ops vb'.ops)) $$ [] [-]
    · iPkgInit
    imod bnd_acc hpers ks γ.h 1 mp1 γ.m1 v1.ι v1.kv qw1 (σOf ks ops v1.ops) b1
      $$ [Hret1 Hσw1 Hbw1] with ⟨%Hlf2, %Hokf2, Hrl, Hrh, Hcl, Hch, Hcls⟩
    · iframe #; iframe
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(memberN 1) from Std.LawfulSet.empty_subset)
    iintro Hcl2
    inext
    iexists _
    iframe Hch
    iintro Hch
    imod Hcl2 with -
    let b2 : Bnd := (b1.1, b1.2.1, b1.2.2.1, W64 (cmpAfter ks ops vb'.ops))
    have hok2 : bndOk ks (σOf ks ops v1.ops) b2 Hlf2 := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hokf2
      refine ⟨h1, h2, h3, h4, h5, h6, ?_, h8, h9, h10⟩
      show (σOf ks ops v1.ops).crev ≤ sint.Z (W64 (cmpAfter ks ops vb'.ops))
      rw [hcbZ]; exact hcf
    imod Hcls $$ %b2 %hok2 Hrl Hrh Hcl Hch with ⟨Hret1, Hσw1, Hbw1⟩
    imodintro
    (try wp_auto)
    -- `newbe := x.openBackend(b.path)`: a fresh registration, the builder's file
    imod halloc with ⟨%gx, Hreg, HW⟩
    wp_apply (wp_openBackend x ks cfg wr h γ.h vb'.path D (fun _ => mvccW gx) (fun _ => iprop(True))
        backend.bFresh hdbo hlim) $$ [Hfile Htok HW] as %rnb ⟨Htok, %bnb, %γB, %Hrnb, Hnew, Hbfn⟩
    · iframe #; iframe
      iintro %γ ⟨-, Hf⟩
      imodintro
      iframe
    subst Hrnb
    (try wp_auto)
    -- the snapshot's backend opened for the store, at the image (`inc_open_backend`)
    have hRB : receiptBound GF ≤ 2 ^ 38 := ReceiptBoundLe.receiptBound_le
    have hk : receiptBound GF + ((sint.Z cfg.Ops').toNat + 1) + 4 ≤ backend.wbInit := by
      unfold backend.wbInit; omega
    imod inc_open_backend hopen hrest hCR γB bnb gx (limOf cfg) vb'.path D
        (σOf ks ops vb'.ops).log (σOf ks ops vb'.ops).crev u ((sint.Z cfg.Ops').toNat + 1) hk
      $$ [Hreg Himg Hbfn Hnew] with ⟨Hsf, Hbkn, Hplh, Hrbn, Hwb1, Hwb2⟩
    · iframe #; iframe
    sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
