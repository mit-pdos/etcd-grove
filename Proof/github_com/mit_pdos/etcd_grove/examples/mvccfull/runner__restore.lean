/- Lean-first (no Rocq counterpart). The proof of `runner.restore` (Probe: proved).

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

set_option maxHeartbeats 1600000 in
theorem runner.restore.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (_hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (halloc : mvccW_alloc.law (GF := GF))
    (hopen : etcdStorage_open.law (GF := GF))
    (hrest : backendRest_open.law (GF := GF))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
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
    iunfold bkKeep at Hbkb
    icases Hbkb with ⟨%HbkbP, #Hbkb1, #Hbkb2, Hbkb3, Hbkb4, Hbkb5, Hbkb6, Hbkb7⟩
    wp_apply (wp_shut x ks cfg wr h γ.h mpb vb'.path vb'.bk vb'.lp vb'.kv vb'.ι.kv
        (σOf ks ops vb'.ops) (leasesAfter ks ops vb'.ops) rb kb' hdbc rfl Hrecsb)
      $$ [Hkvb Hleb Hbeb Hopenb Hrdrsb Hbackb Hσb Hbkb3 Hbkb4 Hbkb5 Hbkb6 Hbkb7 Hstopb Hrbb]
      as ⟨-, -, -, %D, %u, Hfile, Himg, %HrecD⟩
    · iframe #; iframe
      isplitr
      · iunfold isInc at Hisincb; icases Hisincb with ⟨-, #H⟩; iexact H
      iunfold bkKeep; iframe #; iframe; ipureintro; exact HbkbP
    rw [HbkbP.1] at HrecD
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
    -- `f.le.Recover(newbe, func() lease.TxnDelete { return kv.Write(traceutil.TODO()) })`
    obtain ⟨recs, hrecs1, hrecs2, hrecs3⟩ := HrecD
    iunfold lessorW at Hles1
    icases Hles1 with ⟨%rd0, %r1, #Hlpkg, #Hlinv, #Hlcfg, #Hguard, #Hrevoc, #HlBack, #HapplyOk,
      Hlrd, HlOwn, HlRevk, HlEver, #HreqU, HrdOwn, -, HbeOn, -, -, Hstop1⟩
    iunfold bkKeep at Hbkn
    icases Hbkn with ⟨%HnP, #Hnisb, #Hnsc, Hnbf, Hnoh, HnRT, Hntoks, Hncen⟩
    simp only [mvccrand.rcKB_P]
    ihave Hwb2' : ownToks γB.wb 2 $$ [Hwb1 Hwb2]
    · ihave Hwb1 := (backend.wbTok_toks γB).1 $$ Hwb1
      ihave Hwb2 := (backend.wbTok_toks γB).1 $$ Hwb2
      iapply (ownToks_add 1 1 γB.wb).2; iframe
    ihave HEv : (if recs = [] then iprop(True) else lease.leaseEver (mvccLeases v1.ι.kv) v1.U) ∗
        (if recs = [] then lease.leaseEver (mvccLeases v1.ι.kv) v1.U else iprop(True)) $$ [HlEver]
    · split <;> iframe
    icases HEv with ⟨HEv, HEvk⟩
    ihave #HreqR := bigSepL_mem_or v1.U (fun x : w64 × w64 × w64 => x.1)
      (fun id => lease.leaseReqIs (mvccLeases v1.ι.kv) id (W64 3600)) recs $$ HreqU
    ihave #HgrR := granted_list (mvccLeases v1.ι.kv) (recs.map (·.1)) $$ Hguard
    wp_func_lits
    generalize hrd : (func.mk BAnon BAnon _ : GoFunc) = rd
    -- the closure's deleter triple (the captured cell `kv`, read-only from here on)
    ipersist kv
    ihave #Hmv1 : isMvcc v1.kv v1.ι.kv $$ []
    · iunfold isInc at Hisinc1; icases Hisinc1 with ⟨-, #H⟩; iexact H
    ihave %Hkvs := hsh.1 v1.kv v1.ι.kv $$ Hmv1
    obtain ⟨kty, kvv, hkveq, hKR, hKW, hKRev, hKFR, -, -, -, -, -, hKRest, -, -⟩ := Hkvs
    haveI : ∀ rd γ, Persistent (mvccDeleter (GF := GF) rd γ) := by
      intro rd γ; unfold mvccDeleter; infer_instance
    ihave #Hdel : mvccDeleter rd v1.ι.kv $$ []
    · iunfold mvccDeleter
      isplitr
      · ipureintro; rw [← hrd]; nofun
      iintro !> %q' %B %P %Pre %Q %fh %R
      wp_start_folded as ⟨Hr, Hb, #Hhk, Hpre, Hrun, Hau⟩
      rw [← hrd]
      wp_auto
      wp_apply wp_traceTODO as %tr ⟨%Htr, Htrc⟩
      (try wp_auto)
      rw [hkveq]
      (try wp_auto)
      wp_apply (hKW v1.ι.kv tr true q' B P Pre Q fh R) $$ [Hr Htrc Hb Hpre Hrun Hau]
        as %t ⟨-, Hb, Htx, HQ⟩
      · iframe #; iframe; rw [← hkveq]; iframe #; ipureintro; exact Htr
      (try wp_auto)
      iapply HΦ
      iframe
    have hL' : recs.map (·.1) = leasesAfter ks ops v0.ops := by rw [hrecs2, hveq]
    have hUL : ∀ id ∈ recs.map (·.1), id ∈ v1.U → id ∈ leasesAfter ks ops v1.ops := by
      intro id hid hU
      exact logOk_recover ks ops hlogOk v1.ops v0.ops (by omega) id (by rw [← hL']; exact hid)
        (HU1 id hU)
    have hreq : ∀ x ∈ recs, sint.Z ((fun _ : w64 => W64 3600) x.1) ≤ sint.Z x.2.1 := by
      intro x hx; have := hrecs3 x hx
      have h36 : sint.Z (W64 3600) = 3600 := by decide
      simp only []; rw [h36]; exact this
    wp_apply (wp_Recover v1.lp (mvccLeases v1.ι.kv) v1.bk.be (mvccrand.rcKB γB bnb gx (limOf cfg))
        (mvccW gx) iprop(True) (1 : Qp).half (· = leaseName)
        (backend.rbData (mvccrand.rcP (limOf cfg)) D) rd rd0 (leasesAfter ks ops v1.ops)
        (pendItems (σOf ks ops v1.ops).log []) false recs v1.U (fun _ => W64 3600)
        (leasesAfter ks ops v0.ops) rfl (mvccrand.rcP_lease _) hrecs1 (fun h => absurd h (by decide))
        hUL hreq (by rw [hL']))
      $$ [HEv HbeOn HlOwn HlRevk HrdOwn Hnoh Hwb2' Hrbn]
      as ⟨HbeOn, HlOwn, HEv, #HreqN, HlRevk, HrdOwn, Hnoh, Hrbn, -⟩
    · iframe #; iframe
      simp only [mvccrand.rcKB_P, mvccrand.rcKB_γB, mvccrand.rcKB_be, mvccrand.rcKB_gx]
      iexact Hnisb
    (try wp_auto)
    -- `check(f.kv.Restore(newbe) == nil)`: the follower's incarnation, at the builder's state
    iunfold runnerKeys at Hkeys
    icases Hkeys with ⟨%keys, -, -, %Hsorted, -⟩
    have hσb := logOk_hist ks Hsorted ops hlogOk v0.ops ops.length (by omega) (by omega)
    rw [hveq]
    have hmono := runM_mono ks ops v1.ops v0.ops (by omega)
    have hbndb : bndOk ks (σOf ks ops v0.ops) b2 (histAt ks ops ops.length) := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hokf2
      have hrf' : revAfter ks ops v1.ops ≤ revAfter ks ops v0.ops := revAfter_mono ks ops _ _ (by omega)
      have hcf' := cmpAfter_mono ks ops v1.ops v0.ops (by omega)
      have hlen0 : (σOf ks ops v0.ops).log.length = revAfter ks ops v0.ops + 1 := by
        rw [← σOf_rev]; unfold MvccState.rev
        have := runM_hs_len ks ops v0.ops
        simp only [σOf, logOfHist, List.length_map]; unfold histAt at this ⊢; omega
      rw [hveq] at hrbZ hcbZ hcb1
      refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, hcb1, hσb.2.1, logOk_once ks Hsorted ops hlogOk _⟩
      · rw [σOf_rev]; have := h2; rw [σOf_rev] at this
        show sint.Z b1.1 ≤ ((revAfter ks ops v0.ops : Nat) : Int); omega
      · show ((σOf ks ops v0.ops).rev : Int) ≤ sint.Z (W64 (revAfter ks ops vb'.ops : Int))
        rw [hveq, hrbZ, σOf_rev]; exact Int.le_refl _
      · show sint.Z (W64 (revAfter ks ops vb'.ops : Int)) < 2 ^ 62
        rw [hveq, hrbZ]; have := runM_hs_len ks ops v0.ops; unfold revAfter MSt.rev; omega
      · show (((σOf ks ops v0.ops).notifiedLog.length : Nat) : Int) ≤
          sint.Z (W64 (revAfter ks ops vb'.ops : Int)) + 1
        rw [hveq, hrbZ, σOf_notified, hlen0]; omega
      · have := h6; show sint.Z b1.2.2.1 ≤ cmpAfter ks ops v0.ops
        exact Int.le_trans this hcf'
      · show cmpAfter ks ops v0.ops ≤ sint.Z (W64 (cmpAfter ks ops vb'.ops))
        rw [hveq, hcbZ]; exact Int.le_refl _
    have hitems := (logOk_leases ks Hksl ops hlogOk v0.ops).2.2
    ihave Hau := restore_au hpers ks γ.h 1 mp1 γ.m1 v1.ι v1.kv qw1 (σOf ks ops v1.ops)
      (σOf ks ops v0.ops) b2 (histAt ks ops ops.length) rfl rfl hbndb ⟨hmono.2.2, hmono.2.1⟩
      $$ [Hret1 Hσw1 Hbw1]
    · iframe #; iframe
    rw [hkveq]
    (try wp_auto)
    ihave #Hreq : storageReq (etcdStorage (mvccrand.rcKB γB bnb gx (limOf cfg))) iprop(True)
        iprop(True) iprop(True) $$ []
    · rw [etcdStorage_req]; iapply backend.commitReq_true
    have hRst := hKRest v1.ι.kv (etcdStorage v1.bk) (etcdStorage (mvccrand.rcKB γB bnb gx (limOf cfg)))
        iprop(True) iprop(True) (σOf ks ops v0.ops) u (leasesAfter ks ops v0.ops)
        (DFrac.own (1 : Qp).half) func.nil iprop(True) iprop(True) iprop(True) iprop(True)
        iprop(True) (fun _ => iprop(ghostVar v1.ι.ret qw1 () ∗
          ghostVar γ.m1.σ (Qp.half 1) (σOf ks ops v0.ops) ∗ ghostVar γ.m1.bnd (Qp.half 1) b2))
    rw [etcdStorage_val, mvccrand.rcKB_be] at hRst
    wp_apply hRst $$ [Hopen1 Hback1 Hsf Hplh HlOwn Hau]
    · iframe #; iframe
      isplitr
      · ipureintro; exact ⟨hσb.2.2, rfl⟩
      isplitl [Hplh]
      · rw [etcdStorage_hook]; iexact Hplh
      isplitr
      · ipureintro; left; rfl
      isplitr
      · iunfold api.hookRun; simp only [↓reduceIte]; iintro _; imodintro; itrivial
      isplitr
      · iintro _; itrivial
      ipureintro; exact hitems
    clear hRst
    iintro ⟨Hopen1, Hback1, Hrest0, Hplh, -, HlOwn, %σq, Hret1, Hσw1, Hbw1⟩
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp
    (try wp_auto)
    -- `newbe.SetTxPostLockInsideApplyHook(f.hook)`, the hook frozen
    icases ownToks_add_1 1 ((sint.Z cfg.Ops').toNat) γB.wb $$ Hntoks with ⟨Hntoks, Hw1⟩
    rw [etcdStorage_hook] at *
    wp_apply (wp_SetHook γB (mvccrand.rcP (limOf cfg)) (mvccW gx) iprop(True) bnb (1 : Qp).half
        func.nil f1) $$ [Hnoh Hplh Hw1] as ⟨Hnoh, Hplh⟩
    · iframe #; iframe; iapply (backend.wbTok_toks γB).2; iexact Hw1
    imod backend.plHook_persist γB f1 $$ Hplh with #HhkRO
    (try wp_auto)
    -- the old backend: its census (`Restore` gave the store's rest back), `Close`
    iunfold bkKeep at Hbk1
    icases Hbk1 with ⟨%HoP, #Hoisb, #Hosc, -, Hooh, HoRT, -, Hocen⟩
    icases (apply.bkRT_eq _).1 $$ HoRT with ⟨-, Hoor⟩
    iunfold bkCensus at Hocen
    imod Hocen $$ Hoor Hooh Hrest0 with Hone
    ihave #Horeq : backend.commitReq v1.bk.γB v1.bk.P iprop(True) v1.bk.be iprop(True) iprop(True) $$ []
    · iapply backend.commitReq_true
    wp_apply (wp_bClose v1.bk.γB v1.bk.P (mvccW v1.bk.gx) iprop(True) v1.bk.be iprop(True)
        iprop(True)) $$ [Hone] as %oerr ⟨-, %Do, -, Hocl⟩
    · iframe #; iframe
    icases Hocl with (⟨%Herr, -⟩ | %Hbad)
    rotate_left
    · exact absurd hdbc Hbad
    subst Herr
    (try wp_auto)
    wp_apply (wp_check true go!"the old backend's close failed") $$ []
    · iframe #; ipureintro; rfl
    (try wp_auto)
    -- `f.leases = append([]int64(nil), b.leases...)`
    icases Hleasesb with ⟨%lslb, Hlfb, Hlslb, Hlcapb⟩
    icases Hleases1 with ⟨%lsl1, Hlf1, -, -⟩
    (try wp_auto)
    wp_apply (wp_slice_append (V := w64) slice.nil [] lslb (leasesAfter ks ops v0.ops) (DFrac.own 1))
      $$ [Hlslb] as %lsln ⟨Hlsln, Hlcapn, -⟩
    · iframe
      isplitl
      · iapply (ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1))
      · iapply (ownSliceCap_nil (V := w64) (GF := GF))
    (try wp_auto)
    -- `f.revLo.Store(f.rev)`, `f.cmpLo.Store(f.cmp)`: the bounds' floors at the restored state
    have hr0 : 1 ≤ revAfter ks ops v0.ops := by
      have := runM_hs_len ks ops v0.ops; unfold revAfter MSt.rev; omega
    rw [hveq] at hrbZ hcbZ hcb1 hcb2
    wp_apply_core sync.atomic.Int64.wp_Store (mF go!"revLo" mp1)
      (W64 (revAfter ks ops v0.ops : Int)) $$ [] [-]
    · iPkgInit
    imod bnd_acc hpers ks γ.h 1 mp1 γ.m1 v1.ι (interface.mkOk kty kvv) qw1 (σOf ks ops v0.ops) b2
      $$ [Hret1 Hσw1 Hbw1] with ⟨%Hlf3, %Hokf3, Hrl, Hrh, Hcl, Hch, Hcls⟩
    · iframe #; iframe
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(memberN 1) from Std.LawfulSet.empty_subset)
    iintro Hcl2
    inext
    iexists _
    iframe Hrl
    iintro Hrl
    imod Hcl2 with -
    let b3 : Bnd := (W64 (revAfter ks ops v0.ops : Int), b2.2.1, b2.2.2.1, b2.2.2.2)
    have hok3 : bndOk ks (σOf ks ops v0.ops) b3 Hlf3 := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hokf3
      refine ⟨?_, ?_, h3, h4, h5, h6, h7, h8, h9, h10⟩
      · show 1 ≤ sint.Z (W64 (revAfter ks ops v0.ops : Int)); rw [hrbZ]; omega
      · show sint.Z (W64 (revAfter ks ops v0.ops : Int)) ≤ ((σOf ks ops v0.ops).rev : Int)
        rw [hrbZ, σOf_rev]; exact Int.le_refl _
    imod Hcls $$ %b3 %hok3 Hrl Hrh Hcl Hch with ⟨Hret1, Hσw1, Hbw1⟩
    imodintro
    (try wp_auto)
    wp_apply_core sync.atomic.Int64.wp_Store (mF go!"cmpLo" mp1)
      (W64 (cmpAfter ks ops v0.ops)) $$ [] [-]
    · iPkgInit
    imod bnd_acc hpers ks γ.h 1 mp1 γ.m1 v1.ι (interface.mkOk kty kvv) qw1 (σOf ks ops v0.ops) b3
      $$ [Hret1 Hσw1 Hbw1] with ⟨%Hlf4, %Hokf4, Hrl, Hrh, Hcl, Hch, Hcls⟩
    · iframe #; iframe
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(memberN 1) from Std.LawfulSet.empty_subset)
    iintro Hcl2
    inext
    iexists _
    iframe Hcl
    iintro Hcl
    imod Hcl2 with -
    let b4 : Bnd := (b3.1, b3.2.1, W64 (cmpAfter ks ops v0.ops), b3.2.2.2)
    have hok4 : bndOk ks (σOf ks ops v0.ops) b4 Hlf4 := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hokf4
      refine ⟨h1, h2, h3, h4, h5, ?_, h7, h8, h9, h10⟩
      show sint.Z (W64 (cmpAfter ks ops v0.ops)) ≤ (σOf ks ops v0.ops).crev
      rw [hcbZ]; exact Int.le_refl _
    imod Hcls $$ %b4 %hok4 Hrl Hrh Hcl Hch with ⟨Hret1, Hσw1, Hbw1⟩
    imodintro
    (try wp_auto)
    -- `check(f.kv.Rev() == f.rev)`
    have hR1' : mvccReaders (GF := GF) v1.ι.kv nw1 ⊣⊢
        mvccReaders v1.ι.kv (nw1 - 1) ∗ mvccReaders v1.ι.kv 1 := by
      have := hRdSplit v1.ι.kv (nw1 - 1) 1; rwa [Nat.sub_add_cancel Hl1.2.1] at this
    icases hR1'.1 $$ Hrdrs1 with ⟨Hrdrs1, Hr1⟩
    ihave Hau := read_au hpers ks γ.h 1 mp1 γ.m1 v1.ι (interface.mkOk kty kvv) qw1
      (σOf ks ops v0.ops) $$ [Hret1 Hσw1]
    · iframe #; iframe
    wp_apply (hKRev v1.ι.kv (fun σ => iprop(⌜σ = σOf ks ops v0.ops⌝ ∗ ghostVar v1.ι.ret qw1 () ∗
        ghostVar γ.m1.σ (1 : Qp).half (σOf ks ops v0.ops)))) $$ [Hr1 Hau] as %rv ⟨Hr1, %σr, ⟨%Hσr, Hret1, Hσw1⟩, %Hrv⟩
    · iframe #; iframe
    subst Hσr Hrv
    (try wp_auto)
    rw [σOf_rev]
    wp_apply wp_check
    · ipureintro; simp
    (try wp_auto)
    -- `tr := f.kv.Read(…)`; `check(tr.FirstRev() == f.cmp)`; `tr.End()`
    wp_apply wp_traceTODO as %trc ⟨%Htrc, Htrco⟩
    (try wp_auto)
    ihave Hau := read_au hpers ks γ.h 1 mp1 γ.m1 v1.ι (interface.mkOk kty kvv) qw1
      (σOf ks ops v0.ops) $$ [Hret1 Hσw1]
    · iframe #; iframe
    wp_apply (hKR v1.ι.kv (W32 1) trc true (fun σ => iprop(⌜σ = σOf ks ops v0.ops⌝ ∗
        ghostVar v1.ι.ret qw1 () ∗ ghostVar γ.m1.σ (1 : Qp).half (σOf ks ops v0.ops))))
      $$ [Hr1 Htrco Hau] as %tx ⟨-, %σr, Htx, %Hσr, Hret1, Hσw1⟩
    · iframe #; iframe; ipureintro; exact Htrc
    subst Hσr
    ihave %Htxs := hsh.2.2.1 tx v1.ι.kv trc (.read (σOf ks ops v0.ops)) $$ Htx
    obtain ⟨tty, tv, htx, hTRev, hTFR, -, -, -, -, hTEnd⟩ := Htxs
    subst htx
    (try wp_auto)
    wp_apply (hTFR v1.ι.kv trc (.read (σOf ks ops v0.ops))) $$ [Htx] as Htx
    · iframe #; iframe
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp [σOf]
    (try wp_auto)
    wp_apply (hTEnd v1.ι.kv trc (.read (σOf ks ops v0.ops)) 1 (etcdStorage v1.bk) iprop(True)
      iprop(True)) $$ [Htx] as ⟨Hr1, -⟩
    · iframe #; iframe
    (try wp_auto)
    -- the restored follower's `memCore`: the lessor on the new backend (`lessorApplyOk`)
    obtain ⟨U', hU'⟩ : ∃ U' : List w64, U' = if recs = [] then v1.U else v1.U ++ recs.map (·.1) :=
      ⟨_, rfl⟩
    have hU'g : ∀ id ∈ U', id ∈ grantedAfter ks ops v0.ops := by
      intro id hid
      have hrg := (logOk_leases ks Hksl ops hlogOk v0.ops).2.1
      have hold : ∀ id ∈ v1.U, id ∈ grantedAfter ks ops v0.ops := fun id h =>
        grantedAfter_mono ks ops v1.ops v0.ops (by omega) id (HU1 id h)
      by_cases hre : recs = []
      · simp only [hre, ↓reduceIte] at hU'; subst hU'; exact hold id hid
      · simp only [hre, ↓reduceIte] at hU'; subst hU'
        rcases List.mem_append.1 hid with h | h
        · exact hold id h
        · rw [hL'] at h; exact (hrg id h).2
    ihave HEvU : lease.leaseEver (mvccLeases v1.ι.kv) U' $$ [HEv HEvk]
    · by_cases hre : recs = []
      · simp only [hre, ↓reduceIte] at hU' ⊢; subst hU'; iexact HEvk
      · simp only [hre, ↓reduceIte] at hU' ⊢; subst hU'; iexact HEv
    ihave #HreqU' : □ ([∗list] id ∈ U', lease.leaseReqIs (mvccLeases v1.ι.kv) id (W64 3600)) $$ []
    · by_cases hre : recs = []
      · simp only [hre, ↓reduceIte] at hU'; subst hU'; iexact HreqU
      · simp only [hre, ↓reduceIte] at hU'; subst hU'
        imodintro
        iapply BigSepL.bigSepL_append.2
        isplitl
        · iexact HreqU
        · have e := BigSepL.bigSepL_map (PROP := IProp GF) (fun x : w64 × w64 × w64 => x.1)
            (Φ := fun _ id => lease.leaseReqIs (mvccLeases v1.ι.kv) id (W64 3600)) (l := recs)
          rw [e]; iexact HreqN
    iunfold hookOk at HhookOk1
    icases HhookOk1 with ⟨%Hf1, #Hf1run⟩
    ihave #HlBackN : lease.lessorBackend v1.lp iprop(True) #f1
        (backend.wbTok (mvccrand.rcKB γB bnb gx (limOf cfg)).γB)
        (lease.lessorBeOn v1.lp (mvccrand.rcKB γB bnb gx (limOf cfg)).be)
        (apply.bkRT (mvccrand.rcKB γB bnb gx (limOf cfg)))
        (backend.rbPart (mvccrand.rcKB γB bnb gx (limOf cfg)).γB (· = leaseName)) $$ []
    · have hln : leaseName = go!"lease" := rfl
      rw [hln]
      iunfold lessorApplyOk at HapplyOk
      iapply HapplyOk $$ %(mvccrand.rcKB γB bnb gx (limOf cfg)) %(mvccW gx) %iprop(True) %f1
        %(lease.lessorBeOn v1.lp (mvccrand.rcKB γB bnb gx (limOf cfg)).be)
      · simp only [mvccrand.rcKB_P, mvccrand.rcKB_γB, mvccrand.rcKB_be]; iexact Hnisb
      · simp only [mvccrand.rcKB_γB]; iexact HhkRO
      · ipureintro; exact Hf1
      · iunfold rwLens; iintro !> H; iframe H; iintro H; iexact H
    ihave Hrbn' := backend.rbOwnIn_part γB _ _ $$ Hrbn
    ihave Hc1n : memCore ks γ.h ops 1 mp1 γ.m1 f1
        ⟨vb'.path, v1.lp, v1.kv, v0.ops, mvccrand.rcKB γB bnb gx (limOf cfg), v1.ι, U', b4⟩ qw1 nw1
        (sint.Z cfg.Ops').toNat $$ [Hpath1 Hbe1 Hle1 Hkv1 Hrev1 Hcmp1 Hlf1 Hlsln Hlcapn Hret1 Hσw1
          Hbw1 Hopen1 Hback1 Hrdrs1 Hr1 Hnbf Hnoh HnRT Hntoks Hncen Hlrd HlOwn HlRevk HEvU HrdOwn
          HbeOn Hrbn' Hstop1]
    · iunfold memCore
      dsimp only
      rw [hkveq]
      iframe #; iframe
      isplitr
      · iunfold hookOk; iframe #; ipureintro; exact Hf1
      isplitl [Hlsln]
      · simp only [List.nil_append] at *; iexact Hlsln
      isplitr
      · ipureintro; omega
      isplitl [Hret1 Hσw1 Hbw1]
      · iunfold incW; iframe #; iframe
      isplitr
      · rw [etcdStorage_hookIs]; simp only [mvccrand.rcKB_γB]; iexact HhkRO
      isplitl [Hrdrs1 Hr1]
      · iapply hR1'.2; iframe
      isplitl [Hnbf Hnoh HnRT Hntoks Hncen]
      · iunfold bkKeep
        isplitr
        · ipureintro; exact HnP
        simp only [mvccrand.rcKB_P, mvccrand.rcKB_γB, mvccrand.rcKB_be, mvccrand.rcKB_gx]
        iframe #; iframe
      isplitl
      · iunfold lessorW
        iexists rd, _
        iframe #; iframe
        ipureintro
        exact leaseRecsOk_insert _ _ ⟨recs, hrecs1, hL', hrecs3⟩
      · ipureintro; exact hU'g
    -- `x.checkLeases(f)`; `x.restores.Add(1)`
    wp_apply (wp_checkLeases x ks cfg wr h γ.h ops 1 mp1 γ.m1 f1
        ⟨vb'.path, v1.lp, v1.kv, v0.ops, mvccrand.rcKB γB bnb gx (limOf cfg), v1.ι, U', b4⟩ qw1 nw1
        (sint.Z cfg.Ops').toNat hlogOk) $$ [Hrd Hc1n] as ⟨Hrd, Hc1n⟩
    · iframe #; iframe
      dsimp only; rw [Hops.1]; iexact Hlb
    (try wp_auto)
    wp_apply_core sync.atomic.Int64.wp_Add (rF go!"restores" x) (W64 1) $$ [] [-]
    · iPkgInit
    iunfold ctrInv at Hcres
    iinv Hcres with ⟨%a, >Ha⟩ Hclose
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(readersN .@ "restores") from
      Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iexists a
    iframe
    iintro Ha
    imod Hcl with -
    imod Hclose $$ [Ha] with -
    · inext; iexists _; iframe
    imodintro
    (try wp_auto)
    -- the writer between steps, one more build, the follower at the leader's count
    iapply HΦ
    iframe Htok
    iexists ⟨vb'.path, v1.lp, v1.kv, v0.ops, mvccrand.rcKB γB bnb gx (limOf cfg), v1.ι, U', b4⟩
    isplitr
    · ipureintro; exact ⟨rfl, rfl, hkveq, rfl⟩
    iunfold writerOwn
    dsimp only
    rw [hkveq]
    iframe #
    iframe HhW Hrd Hss0 Hss1 Hadd
    isplitl [Hlog1 Hlog2 Hlog3]
    · iunfold logOwn; iexists lsl, lps; iframe; iframe #; ipureintro; exact Hlogp
    isplitl [Hnl Hvals Hbuilds]
    · iunfold writerCtrs; iexists nl
      have hb1 : W64 (nb : Int) + W64 1 = W64 ((nb + 1 : Nat) : Int) := by word
      rw [hb1]; iframe; ipureintro; exact Hnl'
    isplitr
    · ipureintro; exact ⟨Hops.1, Nat.le_refl _⟩
    isplitr
    · ipureintro; exact ⟨by omega, fun _ => rfl⟩
    isplitl [Hfiles]
    · iexact Hfiles
    isplitl [Hops0 Hhk0 Hc0]
    · iexists qw0, nw0, k0; iunfold memW; iframe; ipureintro; exact Hl0
    · iexists qw1, nw1, (sint.Z cfg.Ops').toNat
      iunfold memW; iframe
      isplitl
      · icases Hhk1 with ⟨%a1, %s1, Hpre1, %Ha1⟩
        iexists a1, s1; iframe; ipureintro
        exact ⟨Ha1.1, by show sint.Z a1 ≤ ((v0.ops : Nat) : Int); omega⟩
      · ipureintro
        exact ⟨Hl1.1, Hl1.2.1, by show _ ≤ (sint.Z cfg.Ops').toNat + v0.ops; omega⟩

end proof

end mvccfull
end EtcdGrove
end Perennial
