/- Lean-first (no Rocq counterpart). The proof of `runner.open`: proved.

The outline (the chain's step 3): `openBackend` (the opener's `K := bFresh`, `W := mvccW gx` of
`mvccW_alloc.law`), `inc_open_backend` at `k = Ops` (its `receiptBound + Ops + 4 ≤ wbInit` from
`ReceiptBoundLe 2 ^ 38` and `writerCtx`'s `Ops < 2 ^ 38`; the post's `Ops ≤ k`); `lease.NewLessor.spec` over the records (`GA := True`,
`reqOf := 3600`, the ids the live leases, `logOk_leases`; `noCluster`'s `clusterOk` from
`noCluster.Version.spec`); `mvcc.api.New.spec` at `σ` (the lessor's owner part at the live leases,
`logOk_leases`' items; the resumed compaction at `u` with the unset hook, `Pre := True`, the commit
request `True`); `SetTxPostLockInsideApplyHook` and the hook frozen (`hookIs`); `inc_alloc` with
the carried parts; the checks by `KV.Rev`, `KV.Read`, `Txn.Rev`, `Txn.FirstRev`, `Txn.End` at the new
invariant; `checkLeases`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__open
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__openBackend
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkLeases
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SetTxPostLockInsideApplyHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.noCluster__Version
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.OpenLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterShares
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorContract
public import Proof.go_etcd_io.etcd.server.v3.lease.RdPool
public import Spec.go_etcd_io.etcd.server.v3.lease.NewLessor
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLaws

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

theorem runner.open.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (_hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (halloc : mvccW_alloc.law (GF := GF))
    (hopen : etcdStorage_open.law (GF := GF))
    (hrest : backendRest_open.law (GF := GF))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (wp_openBackend : runner.openBackend.spec (GF := GF) (hG := hG))
    (wp_Version : noCluster.Version.spec (GF := GF) (hG := hG))
    (wp_NewLessor : lease.NewLessor.spec (GF := GF) (hG := hG))
    (wp_mNew : mvcc.api.New.spec (GF := GF) (hG := hG))
    (wp_SetHook : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_checkLeases : runner.checkLeases.spec (GF := GF) (hG := hG))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_GetLease : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (wp_Attach : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (wp_Detach : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (wp_SRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG)) :
    runner.open.spec (GF := GF) (hG := hG) := by
  intro _ _ x ks cfg wr h γh ops i mp m f n path D u b Hl obe ole okv hlog hn hlen hdbo hck hlim hcbl
  intro σ
  haveI := hpers.1
  haveI := isInc_persistent hpers
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  haveI : Persistent (rnCtx (GF := GF) x ks cfg h γh) := by
    unfold rnCtx runnerKeys runnerH ctrInv; infer_instance
  haveI : Persistent (runnerKeys (GF := GF) x ks) := by unfold runnerKeys; infer_instance
  wp_start as ⟨#Hctx, #Hvoff, Htok, Hrd, #Hlb, #Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv,
    Hrev, Hcmp, Hleases, Hfile, Himg, %Hrec, Hcarry, Hσw, Hbw⟩
  ihave #HctxK : writerCtx x ks cfg wr h γh $$ []
  · iexact Hctx
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hrn, #Hcfg, %Hmix, #Hrds, #Hpb, #Hps, #Hpl, #Hpt, %Hksl, ⟨%lg, #Hlg, #Hlgn⟩,
    -, -, -, -, -, -, -, %HOpsB⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hpm, #Hkeys, %Hkne, #HrH, #Hhist, #Hcfgp, -⟩
  wp_auto
  imod halloc with ⟨%gx, Hreg, HW⟩
  wp_apply (wp_openBackend x ks cfg wr h γh path D (fun _ => mvccW gx) (fun _ => iprop(True))
      backend.bFresh hdbo hlim) $$ [Hfile Htok HW] as %rnb ⟨Htok, %bnb, %γB, %Hrnb, Hnew, Hbfn⟩
  · iframe #; iframe
    iintro %γ ⟨-, Hf⟩
    imodintro
    iframe
  subst Hrnb
  (try wp_auto)
  have hRB : receiptBound GF ≤ 2 ^ 38 := ReceiptBoundLe.receiptBound_le
  have hk : receiptBound GF + (sint.Z cfg.Ops').toNat + 4 ≤ backend.wbInit := by
    rw [backend.wbInit_val]; omega
  imod inc_open_backend hopen hrest hCR γB bnb gx (limOf cfg) path D σ.log σ.crev u
      (sint.Z cfg.Ops').toNat hk
    $$ [Hreg Himg Hbfn Hnew] with ⟨Hsf, Hbkn, Hplh, Hrbn, Hwb1, Hwb2⟩
  · iframe #; iframe
  -- `m.le = lease.NewLessor(x.lg, m.be, noCluster{}, lease.LessorConfig{MinLeaseTTL: 1})`
  ihave #Hcl : lease.clusterOk (GF := GF) (interface.mkOk noCluster.ty #(noCluster.mk)) $$ []
  · iunfold lease.clusterOk
    iexists _
    isplitr
    · ipureintro; rfl
    iintro !> %Φ' !> - HΦ'
    wp_apply wp_Version as %v %Hv
    iapply HΦ'
    ileft; ipureintro; exact Hv
  obtain ⟨recs, hrecs1, hrecs2, hrecs3⟩ := Hrec
  iunfold bkKeep at Hbkn
  icases Hbkn with ⟨%HnP, #Hnisb, #Hnsc, Hnbf, Hnoh, HnRT, Hntoks, Hncen⟩
  simp only [mvccrand.rcKB_P]
  have hreq : ∀ x ∈ recs, sint.Z ((fun _ : w64 => W64 3600) x.1) ≤ sint.Z x.2.1 := by
    intro x hx; have := hrecs3 x hx
    have h36 : sint.Z (W64 3600) = 3600 := by decide
    simp only []; rw [h36]; exact this
  wp_apply (wp_NewLessor lg _ _ (mvccrand.rcKB γB bnb gx (limOf cfg)) (mvccW gx) iprop(True)
      (1 : Qp).half (fun _ => iprop(True)) (· = leaseName)
      (backend.rbData (mvccrand.rcP (limOf cfg)) D) false recs (fun _ => W64 3600)
      (leasesAfter ks ops n) rfl (mvccrand.rcP_lease _) hrecs1 hreq (by rw [hrecs2]))
    $$ [Hnoh Hwb1 Hrbn]
    as %l ⟨Hnoh, Hrbn, %lp, %γl, %Hl, #Hlinv, #Hmode, #Hlcfg, -, -, #Hguard, Hlrds, Hlown, Hever,
      Hrvk, Hrdo, -, Hbeon, #Happly, Hstop, #HreqN, -, -⟩
  · rw [mvccrand.rcKB_P, mvccrand.rcKB_γB, mvccrand.rcKB_be]
    iframe #; iframe
    isplitr
    · ipureintro; exact hck
    isplitr
    · ipureintro; simp only; exact Int.le_refl _
    imodintro
    iapply (BigSepL.bigSepL_intro (P := (iprop(emp) : IProp GF)) (fun _ _ _ => BI.true_intro))
    iempintro
  subst Hl
  (try wp_auto)
  -- the model's facts at `n`
  iunfold runnerKeys at Hkeys
  icases Hkeys with ⟨%keys, -, -, %Hsorted, -⟩
  have hσh := logOk_hist ks Hsorted ops hlog n n (Nat.le_refl _) hn
  have hitems := (logOk_leases ks Hksl ops hlog n).2.2
  -- two of the lessor's reader slots: the store's, the writer's
  obtain ⟨nl, hnl⟩ : ∃ nl, Int.toNat sync.rwmutex.actualMaxReaders = 2 + nl :=
    ⟨Int.toNat sync.rwmutex.actualMaxReaders - 2, by have := sync.actualMaxReaders_ge_2; omega⟩
  rw [hnl]
  icases (backend.bigSepL_replicate_add _ 2 nl).1 $$ Hlrds with ⟨Hlrd2, Hlrdp⟩
  -- the rest: the lessor's reader pool (`lessorW`'s, `checkLeases`' `Leases()`)
  have hTB : threadBound GF ≤ nl + 1 := by
    have h1 : threadBound GF ≤ 2 ^ 28 := ThreadBoundLe.le_of (2 ^ 28) (Nat.le_refl _)
    have h2 := hnl
    rw [sync.rwmutex.actualMaxReaders_unseal] at h2
    omega
  imod lease.lessorRdPool_init γl ⊤ nl hTB $$ Hlrdp with #Hpool
  rw [List.replicate_succ, List.replicate_one]
  icases BigSepL.bigSepL_cons.1 $$ Hlrd2 with ⟨Hlrd1, Hlrd2⟩
  ihave Hlrd2 := (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hlrd2
  ihave #HisL := lease.isLessor_of_lessorInv wp_GetLease wp_Attach wp_Detach wp_SRD lp γl $$ [Hlinv]
  · iframe Hlinv; iPkgInit
  -- the hook's half: lent to `New` if a compaction resumes, kept otherwise
  ihave Hpl2 : (if u then iprop(True) else backend.plHook γB func.nil) ∗
      (if u then backend.plHook γB func.nil else iprop(True)) $$ [Hplh]
  · cases u <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iframe
  icases Hpl2 with ⟨Hpl1, Hpl2⟩
  -- `scfg`
  ihave #Hcfgf : rF go!"cfg" x ↦□ cfg $$ []
  · iexact Hcfgp
  icases typedPointsto_split _ _ _ $$ Hcfgf with #Hcfgf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcfgf
  wp_auto
  have hW0 : sint.Z (W64 0) = 0 := rfl
  by_cases hb : 0 < sint.Z cfg.CompactionBatchLimit' <;>
    simp only [hW0, hb, decide_true, decide_false] <;> wp_auto
  all_goals
    -- `m.kv = mvcc.New(x.lg, m.be, m.le, scfg)`
    -- (premise fixes 6) the runner's logger, a zap logger
    ihave #Hlgo := zapLoggerOk_orNil lg $$ Hlgn
    rw [show (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #bnb : GoInterface) = storageVal (etcdStorage (mvccrand.rcKB γB bnb gx (limOf cfg))) by
        rw [etcdStorage_val, mvccrand.rcKB_be]]
    wp_apply (wp_mNew lg _ _ (etcdStorage (mvccrand.rcKB γB bnb gx (limOf cfg))) iprop(True) γl
        func.nil σ u (leasesAfter ks ops n) (DFrac.own (1 : Qp).half) func.nil iprop(True)
        iprop(True) iprop(True) iprop(True) iprop(True)) $$ [Hsf Hlrd1 Hrdo Hlown Hpl2]
      as %wsl ⟨%γk, %Hγl, #Hkvm, Hσ, Hopn, Hmb, Hrdrs, ⟨%rd, Hrdo, Hdel⟩, Hlown, -, Hhkp⟩
    · iframe #; iframe
      isplitr
      · ipureintro
        refine ⟨?_, hσh.2.2, rfl⟩
        first
          | (unfold cblOf at hcbl; simp only [hb, ↓reduceIte] at hcbl; exact hcbl)
          | (simp only [cblOf, hb, ↓reduceIte] at hcbl; exact hcbl)
      isplitr
      · ipureintro; exact hitems
      cases u <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · itrivial
      · ihave Hhr : api.hookRun (GF := GF) iprop(True) func.nil iprop(True) iprop(True) $$ []
        · iapply (api.hookRun_nil _ _ _).2; iintro _; imodintro; itrivial
        ihave Hwd : (iprop(True) ={⊤}=∗ (iprop(True) ∗ iprop(True) : IProp GF)) $$ []
        · iintro -; imodintro; isplit <;> itrivial
        ihave Hcq : backend.commitReq (GF := GF) γB (mvccrand.rcP (limOf cfg)) iprop(True) bnb
            iprop(True) iprop(True) $$ []
        · iapply backend.commitReq_true
        rw [etcdStorage_hook, etcdStorage_req]
        simp only [mvccrand.rcKB_P, mvccrand.rcKB_γB, mvccrand.rcKB_be]
        iframe
        ipureintro; simp
    ihave Hplh : backend.plHook γB func.nil $$ [Hpl1 Hhkp]
    · cases u <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · iexact Hpl1
      · rw [etcdStorage_hook]; icases Hhkp with ⟨Hh, -⟩; iexact Hh
    (try wp_auto)
    rw [etcdStorage_val, mvccrand.rcKB_be]
    (try wp_auto)
    -- `m.be.SetTxPostLockInsideApplyHook(m.hook)`, the hook frozen
    wp_apply (wp_SetHook γB (mvccrand.rcP (limOf cfg)) (mvccW gx) iprop(True) bnb (1 : Qp).half
        func.nil f) $$ [Hnoh Hplh Hwb2] as ⟨Hnoh, Hplh⟩
    · iframe #; iframe
    imod backend.plHook_persist γB f $$ Hplh with #HhkRO
    (try wp_auto)
    subst Hγl
    -- `check(m.kv.Rev() == m.rev)`, at the state the writer holds
    ihave %Hkvs := hsh.1 _ γk $$ Hkvm
    obtain ⟨kty, kvv, hkveq, hKR, -, hKRev, -, -, -, -, -, -, -, -, -⟩ := Hkvs
    obtain ⟨rfl, rfl⟩ : _ = kty ∧ _ = kvv := by
      simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at hkveq; exact hkveq
    have hN1 : 1 ≤ mvccReaderN := by
      rw [mvccReaderN_eq]; have := backend.rdStockN_val; omega
    have hR1 : mvccReaders (GF := GF) γk mvccReaderN ⊣⊢
        mvccReaders γk (mvccReaderN - 1) ∗ mvccReaders γk 1 := by
      have := hRdSplit γk (mvccReaderN - 1) 1; rwa [Nat.sub_add_cancel hN1] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    have hσrev : σ.rev = revAfter ks ops n := σOf_rev ks ops n
    have hσcrev : σ.crev = cmpAfter ks ops n := rfl
    ihave Hau := own_au γk σ $$ Hσ
    wp_apply (hKRev γk (fun σ' => iprop(⌜σ' = σ⌝ ∗ mvccState γk σ))) $$ [Hr1 Hau]
      as %rv ⟨Hr1, %σr, ⟨%Hσr, Hσ⟩, %Hrv⟩
    · iframe #; iframe
    subst Hσr Hrv
    (try wp_auto)
    rw [hσrev]
    wp_apply wp_check
    · ipureintro; simp
    (try wp_auto)
    -- `tr := m.kv.Read(…)`; `check(tr.Rev() == m.rev && tr.FirstRev() == m.cmp)`; `tr.End()`
    wp_apply wp_traceTODO as %trc ⟨%Htrc, Htrco⟩
    (try wp_auto)
    ihave Hau := own_au γk σ $$ Hσ
    wp_apply (hKR γk (W32 1) trc true (fun σ' => iprop(⌜σ' = σ⌝ ∗ mvccState γk σ)))
      $$ [Hr1 Htrco Hau] as %tx ⟨-, %σr, Htx, %Hσr, Hσ⟩
    · iframe #; iframe; ipureintro; exact Htrc
    subst Hσr
    ihave %Htxs := hsh.2.2.1 tx γk trc (.read σ) $$ Htx
    obtain ⟨tty, tv, htx, hTRev, hTFR, -, -, -, -, hTEnd⟩ := Htxs
    subst htx
    (try wp_auto)
    wp_apply (hTRev γk trc (.read σ)) $$ [Htx] as Htx
    · iframe #; iframe
    (try wp_auto)
    rw [show (MTxn.read σ).state = σ from rfl, hσrev]
    (try wp_auto)
    wp_apply (hTFR γk trc (.read σ)) $$ [Htx] as Htx
    · iframe #; iframe
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp [hσcrev]
    (try wp_auto)
    wp_apply (hTEnd γk trc (.read σ) 1 (etcdStorage (mvccrand.rcKB γB bnb gx (limOf cfg))) iprop(True) iprop(True)) $$ [Htx]
      as ⟨Hr1, -⟩
    · iframe #; iframe
    (try wp_auto)
    -- the new incarnation, with the carried parts
    imod inc_alloc ks γh i mp m γk (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl) σ b Hl ⟨wsl, rfl⟩
      $$ [Hkvm Hσ Hcarry] with ⟨%ι, %Hι, #Hinc, Hret⟩
    · iframe #; iframe
    subst Hι
    -- the member's `memCore` at the new store, backend and lessor
    have hrecsOk : leaseRecsOk ((backend.rbData (mvccrand.rcP (limOf cfg)) D).insert go!"lease"
        (((backend.rbData (mvccrand.rcP (limOf cfg)) D).lookup go!"lease").getD ∅))
        (leasesAfter ks ops n) :=
      leaseRecsOk_insert _ _ ⟨recs, hrecs1, hrecs2, hrecs3⟩
    have hUg : ∀ id ∈ recs.map (·.1), id ∈ grantedAfter ks ops n := by
      intro id hid; rw [hrecs2] at hid; exact ((logOk_leases ks Hksl ops hlog n).2.1 id hid).2
    ihave Hlrd := lessorRd_of' lp (mvccLeases ι.kv) $$ [Hlrd2]
    · iframe #; iframe
    ihave Hrbp := backend.rbOwnIn_part γB _ _ $$ Hrbn
    ihave #HreqU : □ ([∗list] id ∈ recs.map (·.1), lease.leaseReqIs (mvccLeases ι.kv) id (W64 3600))
      $$ []
    · imodintro
      have e := BigSepL.bigSepL_map (PROP := IProp GF) (fun x : w64 × w64 × w64 => x.1)
        (Φ := fun _ id => lease.leaseReqIs (mvccLeases ι.kv) id (W64 3600)) (l := recs)
      rw [e]; iexact HreqN
    ihave Hc : memCore ks γh ops i mp m f ⟨path, lp, interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl, n,
        mvccrand.rcKB γB bnb gx (limOf cfg), ι, recs.map (·.1), b⟩ 1 mvccReaderN
        (sint.Z cfg.Ops').toNat $$ [HhookOk Hpath Hbe Hle Hkv Hrev Hcmp Hleases Hret Hσw Hbw Hopn Hmb
          Hrdrs Hr1 Hnbf Hnoh HnRT Hntoks Hncen Hlrd Hlown Hrvk Hever Hrdo Hdel Hbeon Hrbp Hstop]
    · iunfold memCore
      dsimp only
      try simp only [mvccrand.rcKB_be]
      iframe #; iframe
      isplitr
      · ipureintro; exact hn
      isplitl [Hret Hσw Hbw]
      · iunfold incW; iframe #; iframe
      isplitr
      · rw [etcdStorage_hookIs]; simp only [mvccrand.rcKB_γB]; iexact HhkRO
      isplitl [Hrdrs Hr1]
      · iapply hR1.2; iframe
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
        ipureintro; exact hrecsOk
      · ipureintro; exact hUg
    -- `x.checkLeases(m)`
    wp_apply (wp_checkLeases x ks cfg wr h γh ops i mp m f ⟨path, lp, interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl, n,
        mvccrand.rcKB γB bnb gx (limOf cfg), ι, recs.map (·.1), b⟩ 1 mvccReaderN
        (sint.Z cfg.Ops').toNat hlog) $$ [Hrd Hc Htok] as ⟨Hrd, Hc, Htok⟩
    · iframe #; iframe
    (try wp_auto)
    iapply HΦ
    iframe Htok Hrd
    iexists ⟨path, lp, interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl, n,
        mvccrand.rcKB γB bnb gx (limOf cfg), ι, recs.map (·.1), b⟩, (sint.Z cfg.Ops').toNat
    iframe Hc
    ipureintro; exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩

end proof

end mvccfull
end EtcdGrove
end Perennial
