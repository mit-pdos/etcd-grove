/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__start.lean`, over its callees'
specs (`HarnessStart.lean`'s lemmas): a fresh node's disk is empty, so in a bootstrapped run the
boot write is made (`disk.save` of `HardState{Term: 1}` and the boot entry: the disk is then the
view's, `fresh_dur`); its `MemoryStorage` from the disk (`memoryOf`), the Go fields set; the `boot`
report (`report_upd` at `antSim_boot`'s step: the view running); the `bootStorage` registered
(`antStor_register`) and raft restarted on it (`NewRawNode.restartAtApiSpec`, its storage premise
`ant_restartStorage`); the boot drain and `alone`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__start
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.disk__save
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.u64p
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootData
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.memoryOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.copyHardState
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__storeBase
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__storeConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__emit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__drain
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__alone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Name
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.idNames
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVoters
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import Perennial.Spec.sync.atomic.StoreUint64
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessStart
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.AntStorageStart
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessLogger
public import Proof.go_etcd_io.raft.v3.RawNodeStartApi
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] antStorageModelNC


theorem node.start.wp_proof
    (wp_save : disk.save.spec (GF := GF) (hG := hG))
    (wp_u64p : u64p.spec (GF := GF) (hG := hG))
    (wp_bootData : bootData.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_memoryOf : memoryOf.spec (GF := GF) (hG := hG))
    (wp_copyHardState : copyHardState.spec (GF := GF) (hG := hG))
    (wp_StoreUint64 : sync.atomic.StoreUint64.spec (GF := GF) (hG := hG))
    (wp_storeBase : node.storeBase.spec (GF := GF) (hG := hG))
    (wp_storeConf : node.storeConf.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_Name : Name.spec (GF := GF) (hG := hG))
    (wp_idNames : idNames.spec (GF := GF) (hG := hG))
    (wp_GetVoters : raftpb.ConfState.GetVoters.spec (GF := GF) (hG := hG))
    (wp_GetVotersOutgoing : raftpb.ConfState.GetVotersOutgoing.spec (GF := GF) (hG := hG))
    (wp_emit : node.emit.spec (GF := GF) (hG := hG))
    (wp_bsInitialState : bootStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_bsSnapshot : bootStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_bsLastIndex : bootStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_bsFirstIndex : bootStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_bsTerm : bootStorage.Term.spec (GF := GF) (hG := hG))
    (wp_bsEntries : bootStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_NewRawNode : NewRawNode.restartAtApiSpec (GF := GF) (hG := hG))
    (wp_Infof : nodeLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (wp_drain : node.drain.spec (GF := GF) (hG := hG))
    (wp_alone : node.alone.spec (GF := GF) (hG := hG))
    (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (h_rso : raftState_open_rn.law (GF := GF)) :
    node.start.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v q
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok, %Hb1⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, %Hmr, -, -, #Hcro, -, -, -, -, -, -, %Hfits, -, -,
    #Hsinv, -⟩
  iunfold clusterRO at Hcro
  icases Hcro with ⟨%nsl, %ivl, -, -, -, #Hmode, #Hivl, #Hivs⟩
  ihave #Hn' := Hn
  iunfold nodeRO at Hn'
  icases Hn' with ⟨%ch, %d', #Nc, #Nid, #Nname, -, -, -, #Nlog⟩
  iunfold nodeOwn at Hown
  icases Hown with ⟨%d, %rn, %ms0, %hsl0, %cl, %csl0, %role0, %app0, #Nd, Hmem, Nrn, Nstore, Nrole,
    Nhs, Ncause, Napp, Nconf, Hv, Hl, %Hnorm, ⟨%Hfresh, %Hby⟩, Hdisk, Hdr⟩
  obtain ⟨Hscope, Hrun⟩ := Hmr
  have Hboot : γ.R.boot = γ.mode.Boot' := Hrun.2.2.1
  have Hdur : v.dur = startDur γ.R := fresh_dur Hfresh
  iunfold nodeMemB1 at Hmem
  icases Hmem with ⟨%mhs0, %rhs0, Nitems, Nmhs, Nrhs, Nwrites, Ninfl, Napps, Napplying, Nrest, Nwip,
    Naip, Nconfs, NconfBase, Hemit⟩
  iunfold emitOk at Hemit
  icases Hemit with ⟨Ndead, Nfuse⟩
  wp_auto
  -- the boot write: in a bootstrapped run, on the empty disk; after it the disk is the view's
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun x => iprop(⌜x = executeVal⌝ ∗ d_ptr ↦ d ∗ diskOwn d v.dur)))
    $$ [d Hdisk]
  · rw [Hdur]
    cases hb : γ.mode.Boot'
    · try wp_auto
      rw [← startDur_noboot γ.R (Hboot.trans hb)]
      iframe d Hdisk
      ipureintro; rfl
    · have hbR : γ.R.boot = true := Hboot.trans hb
      iunfold diskOwn at Hdisk
      icases Hdisk with ⟨%hsl, %esl, Dhs, #Dhsro, Dsnap, Dents, #Dels, Dcap⟩
      iunfold entsPts at Dels
      icases Dels with ⟨%els, #Dels, #Dbig⟩
      ihave %Hels := BigSepL2.bigSepL2_nil_inv_right $$ Dbig
      subst Hels
      ihave %Hlen := ownSlice_len $$ Dels
      have Hl0 : esl.len = W64 0 := by
        obtain ⟨h1, h2⟩ := Hlen
        simp only [List.length_nil] at h1
        word
      try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_apply wp_IsEmptyHardState hsl _ $$ [$Hraft]
        · iunfold hsOpt; iright; iexact Dhsro
        iintro -
        wp_if_destruct
        · try wp_auto
          wp_apply wp_u64p (W64 1) $$ [$Hpkg] as %lt Hlt
          try wp_auto
          wp_apply wp_u64p (W64 1) $$ [$Hpkg] as %lt1 Hlt1
          try wp_auto
          wp_apply wp_u64p (W64 1) $$ [$Hpkg] as %li1 Hli1
          try wp_auto
          wp_apply wp_bootData $$ [$Hpkg] as %bsl Hbsl
          try wp_auto
          wp_apply ant_wp_slice_literal_ex (V := Loc)
          wp_alloc l0 as Hl0
          wp_auto
          iexists [l0]
          isplitr
          · ipureintro; rfl
          iintro %slp ⟨Hsl, -⟩
          have Hsz : go.arrayLiteralSize [KeyedElement none (ElementLiteralValue
              [KeyedElement (some (KeyField go!"Term")) (ElementExpression go.uint64.PointerType #lt1),
                KeyedElement (some (KeyField go!"Index")) (ElementExpression go.uint64.PointerType #li1),
                KeyedElement (some (KeyField go!"Data")) (ElementExpression go.byte.SliceType #bsl)])] = 1 := rfl
          simp only [Hsz]
          imod ownSlice_persist $$ Hsl with #Hsl
          imod bootEnt_entRO l0 lt1 li1 bsl (⟨zero_val _, lt1, li1, null, bsl, slice.nil, 0⟩ : raftpb.Entry) ⊤
              rfl rfl rfl rfl rfl $$ [Hl0 Hlt1 Hli1 Hbsl] with #He
          · iframe Hl0 Hlt1 Hli1 Hbsl
          imod bootHs_hsRO «$a0_ptr» lt (⟨zero_val _, lt, null, null, slice.nil, 0⟩ : raftpb.HardState) ⊤
              rfl rfl rfl rfl $$ [«$a0» Hlt] with #Hh1
          · iframe «$a0» Hlt
          ihave Hdisk : diskOwn d ⟨W64 0, W64 0, W64 0, []⟩ $$ [Dhs Dsnap Dents Dcap]
          · iunfold diskOwn
            iexists hsl, esl
            iframe Dhs Dhsro Dsnap Dents Dcap
            iunfold entsPts
            iexists []
            iframe Dels
            iexact Dbig
          have Hok : SaveOk ⟨W64 0, W64 0, W64 0, []⟩ [AntSim.bootEnt] := by
            intro e he
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
            subst he
            simp only [AntSim.bootEnt, List.length_nil]
            constructor <;> word
          try wp_auto
          wp_apply wp_save d _ «$a0_ptr» (some (HardStateM.mk (W64 1) (W64 0) (W64 0))) _ [l0]
              [AntSim.bootEnt] Hok $$ [$Hpkg $Hdisk] as Hdisk
          · iframe Hsl
            isplitl []
            · iapply hsOptRO_of_hsRO $$ Hh1
            iapply BigSepL2.bigSepL2_singleton.2; iexact He
          try wp_auto
          rw [startDur_boot γ.R hbR]
          iframe d Hdisk
          ipureintro; rfl
        · exfalso; simp at Hif
      · exfalso; simp [Hl0] at Hif
  iintro %x ⟨%hx, d, Hdisk⟩
  subst hx
  try wp_auto
  -- the `MemoryStorage` of the disk
  have Hidx : ∀ (i : Nat) (e : EntryM), v.dur.log[i]? = some e → uint.nat e.Index' = 1 + i := by
    rw [Hdur]; exact bootLog_index γ.R
  have Hll : 1 + v.dur.log.length ≤ 2 ^ 61 := by
    have := bootLog_length γ.R
    rw [Hdur]; simp only [startDur]; omega
  wp_apply wp_memoryOf d v.dur Hidx Hll $$ [$Hpkg $Hdisk]
    as %ms ⟨Hdisk, %γs, #Hlock, Hmeta, Hlog1, #Hlog0, Hend, Hsnap, Hfresh, %Hsz⟩
  try wp_auto
  iunfold diskOwn at Hdisk
  icases Hdisk with ⟨%hsl, %esl, Dhs, #Dhsro, Dsnap, Dents, #Dels, Dcap⟩
  try wp_auto
  wp_apply wp_copyHardState hsl (some (HardStateM.mk v.dur.term v.dur.vote v.dur.commit))
    $$ [$Hpkg] as %hp Hhp
  · iapply hsOptRO_of_hsRO $$ Dhsro
  ihave #Hhs := hsOptRO_some $$ Hhp
  try wp_auto
  -- `autoLeft`, in the logger's invariant
  wp_apply_core wp_StoreUint64 $$ [] [-Hat]
  · iexact Hat
  iinv Nlog with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%x, Hx⟩
  iexists x
  iframe Hx
  iintro Hx
  imod Hmask with -
  imod Hclose $$ [Hx] with -
  · inext; iexists (W64 0); iexact Hx
  imodintro
  -- the storage's base and configuration (each resolution from here to `emit` gives a receipt)
  wp_take_receipt as R1
  wp_apply +noauto wp_storeBase n ms γs _ memSnapEmpty rfl $$ [$Hpkg $Nstore $Hlock $Hmeta $Hfresh]
    as ⟨Nstore, Hmeta, Hfresh⟩
  wp_take_receipt as R2
  wp_apply +noauto wp_storeConf c γ n j ms γs _ memSnapEmpty rfl $$ [$Hpkg $Hc $Hn $Nstore $Hlock $Hmeta $Hfresh]
    as %cs ⟨Nstore, Hmeta, Hfresh, #Hcs⟩
  wp_take_receipt as R3
  wp_apply +noauto wp_LastIndex ms γs (1 + v.dur.log.length) $$ [$Hraft $Hlock $Hend] as %li ⟨Hend, %Hli⟩
  ihave #Hinit := isInitialized_access $$ Hraft
  iNamed Hinit
  wp_take_receipt as R4
  -- the last entry's term: `0` (the dummy entry) or the boot entry's `1`; not compacted (fresh)
  wp_bind (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Term")) (Val _))
  iapply (wp_wand (Φ := fun x => iprop(⌜x = PairV #(W64 (if γ.R.boot then 1 else 0)) #interface.nil⌝ ∗
      memLog γs 1 (DFrac.own 1) v.dur.log ∗ memStorFresh ms γs 0 memSnapEmpty)))
    $$ [Hlog1 Hfresh]
  · rw [Hdur] at Hli ⊢
    cases hbR : γ.R.boot
    · have Hli0 : li = W64 0 := by
        simp only [startDur, AntSim.bootLog, hbR] at Hli
        simp at Hli; word
      subst Hli0
      wp_apply +noauto wp_Term ms γs 0 DFrac.discard [zero_val EntryM] (W64 0) errCompacted
        $$ [$Hraft $Hlock $Hlog0 $ErrCompacted] as %t %err ⟨-, Hres⟩
      · ipureintro; simp
      icases Hres with (%Hok | ⟨%_, #Hbad⟩)
      · obtain ⟨he, ht⟩ := Hok
        subst he
        simp at ht
        subst ht
        iframe Hlog1 Hfresh
        ipureintro; rfl
      · icases memStorFresh_compacted ms γs _ _ _ $$ [$Hfresh $Hbad] with ⟨%hbad, -⟩
        exfalso; word
    · have Hli1 : li = W64 1 := by
        simp only [startDur, AntSim.bootLog, hbR] at Hli
        simp at Hli; word
      subst Hli1
      simp only [startDur, AntSim.bootLog, hbR, ↓reduceIte, ite_true]
      wp_apply +noauto wp_Term ms γs 1 (DFrac.own 1) [AntSim.bootEnt] (W64 1) errCompacted
        $$ [$Hraft $Hlock $Hlog1 $ErrCompacted] as %t %err ⟨Hlog1, Hres⟩
      · ipureintro; simp
      icases Hres with (%Hok | ⟨%_, #Hbad⟩)
      · obtain ⟨he, ht⟩ := Hok
        subst he
        simp at ht
        subst ht
        iframe Hlog1 Hfresh
        ipureintro; rfl
      · icases memStorFresh_compacted ms γs _ _ _ $$ [$Hfresh $Hbad] with ⟨%hbad, -⟩
        exfalso; word
  iintro %x ⟨%hx, Hlog1, Hfresh⟩
  subst hx
  -- the `boot` report's fields
  wp_take_receipt as R5
  wp_apply +noauto wp_GetTerm.1 hp _ $$ [$Hpb $Hhs]
  wp_take_receipt as R6
  wp_apply +noauto wp_GetVote.1 hp _ $$ [$Hpb $Hhs]
  wp_take_receipt as R7
  wp_apply +noauto wp_Name _ $$ [$Hpkg]
  wp_take_receipt as R8
  wp_apply +noauto wp_GetCommit.1 hp _ $$ [$Hpb $Hhs]
  wp_take_receipt as R9
  wp_apply +noauto wp_GetVoters cs DFrac.discard _ $$ [$Hpb] as %vsl ⟨#Hvsl, -⟩
  · iunfold csOpt; iright; iexact Hcs
  wp_take_receipt as R10
  wp_apply +noauto wp_idNames vsl DFrac.discard _ $$ [$Hpkg $Hvsl] as %vout ⟨-, #Hvout⟩
  wp_take_receipt as R11
  wp_apply +noauto wp_GetVotersOutgoing cs DFrac.discard _ $$ [$Hpb] as %osl ⟨#Hosl, -⟩
  · iunfold csOpt; iright; iexact Hcs
  wp_take_receipt as R12
  wp_apply +noauto wp_idNames osl DFrac.discard _ $$ [$Hpkg $Hosl] as %oout ⟨-, #Hoout⟩
  wp_take_receipt as R13
  -- the `boot` report: its event, its receipts, the report's update (the view running)
  have Hterm : v.dur.term = W64 (if γ.R.boot then 1 else 0) := by rw [Hdur]; rfl
  have Hvote : v.dur.vote = W64 0 := by rw [Hdur]; rfl
  have Hcommit : v.dur.commit = W64 0 := by rw [Hdur]; rfl
  have Hli' : li = W64 (if γ.R.boot then 1 else 0) := by
    rw [Hdur] at Hli
    simp only [startDur, AntSim.bootLog] at Hli
    rcases Bool.eq_false_or_eq_true γ.R.boot with hb | hb <;> simp [hb] at Hli ⊢ <;> word
  subst Hli'
  ihave Hev : eventOwn «$a0_ptr» (evBootM γ.R) $$ [«$a0»]
  · iunfold eventOwn
    iexists _
    iframe «$a0»
    simp only [evBootM, AntSim.evBoot, AntCheck.fieldRO]
    isplitr
    · ipureintro
      simp only [Hterm, Hvote, Hcommit]
      rcases Bool.eq_false_or_eq_true γ.R.boot with hb | hb <;>
        simp only [hb, Bool.false_eq_true, ↓reduceIte, ite_true, ite_false] <;>
        simp only [AntCheck.fieldRel, AntCheck.fieldIs, AntCheck.fieldZ, AntCheck.hasBit, AntCheck.fB,
          AntCheck.fA, AntCheck.fBy, AntCheck.fRole, AntCheck.fTerm, AntCheck.fVote, AntCheck.fCommit,
          AntCheck.fFirst, AntCheck.fLastIndex, AntCheck.fLastTerm, AntCheck.fApplied, AntCheck.fSnap,
          AntCheck.fW, AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx, AntSim.nameOf] <;>
        and_intros <;> first | rfl | decide
    isplitr
    · ipureintro; simp only [AntCheck.hasBit, AntCheck.fEntries]; decide
    isplitr
    · isplitr
      · ipureintro; simp only [AntCheck.hasBit, AntCheck.fVoters]; decide
      iExactEq Hvout
      try simp only []
      rw [voters_names]
    isplitr
    · isplitr
      · ipureintro; simp only [AntCheck.hasBit, AntCheck.fOutgoing]; decide
      iExactEq Hoout
      rfl
    isplitr
    · ipureintro; simp only [AntCheck.hasBit, AntCheck.fMsg]; decide
    ipureintro; simp only [AntCheck.hasBit, AntCheck.fCause]; decide
  ihave Hr := receipt_succ 1 $$ [$R1 $R2]
  ihave Hr := receipt_succ _ $$ [$Hr $R3]
  ihave Hr := receipt_succ _ $$ [$Hr $R4]
  ihave Hr := receipt_succ _ $$ [$Hr $R5]
  ihave Hr := receipt_succ _ $$ [$Hr $R6]
  ihave Hr := receipt_succ _ $$ [$Hr $R7]
  ihave Hr := receipt_succ _ $$ [$Hr $R8]
  ihave Hr := receipt_succ _ $$ [$Hr $R9]
  ihave Hr := receipt_succ _ $$ [$Hr $R10]
  ihave Hr := receipt_succ _ $$ [$Hr $R11]
  ihave Hr := receipt_succ _ $$ [$Hr $R12]
  ihave Hr := receipt_succ _ $$ [$Hr $R13]
  have HK : (AntSim.evBoot γ.R (AntSim.nodeId j)).weight ≤ 13 := by
    rw [evBoot_weight]; have := γ.R.hK; omega
  ihave Hw := receipt_le _ 13 HK $$ Hr
  imod (monoListLbOwn_nil (GF := GF) (A := Msg) γ.sent) with #Hlb0
  imod (monoListLbOwn_nil (GF := GF) (A := XMsg) γ.xsent) with #Hxlb0
  ihave #Hlb : sentLb γ [] $$ []
  · iunfold sentLb; iexact Hlb0
  ihave #Hxlb : xsentLb γ [] $$ []
  · iunfold xsentLb; iexact Hxlb0
  ihave #Hfx := factsExt_none (GF := GF) γ
  wp_apply wp_emit c γ n j «$a0_ptr» (evBootM γ.R)
      (iprop(viewFrag γ j { v with alive := true } ∗ nodeLive γ j ∗
        ∃ (net : List Msg) (xnet : List XMsg), sentLb γ net ∗ xsentLb γ xnet ∗
          ⌜[] <+: net ∧ (∀ m ∈ ([] : List Msg), m ∈ net) ∧ [] <+: xnet ∧
            ∀ x ∈ ([] : List XMsg), x ∈ xnet⌝))
    $$ [$Hpkg $Hc $Hn Ndead Nfuse $Hev Hw Hv Hl] as ⟨Hemit, Hv, Hl, Hsent⟩
  · isplitl [Ndead Nfuse]
    · iunfold emitOk; iframe Ndead Nfuse
    rw [atNode_evBootM]
    iapply report_upd h_vu h_lo c γ j v { v with alive := true } (AntSim.evBoot γ.R (AntSim.nodeId j))
      [] [] [] [] (fun G0 G => G = G0) _ (evBoot_nums _ _) (evBoot_chg _ _)
      (boot_hstep γ.R γ.dec j v Hfresh [] [])
    iframe Hc Hlb Hxlb Hfx Hw Hv Hl
    iintro H; iexact H
  try wp_auto
  -- the storage raft reads: the `bootStorage` registered; raft's restart premise
  iStructNamedPrefix «$v3» "S"
  ipersist Svoters
  imod antStor_register «$v3_ptr» ms γs ⊤ CoPset.subseteq_top Hsz $$ Hsinv Sms with #Hsrec
  have HKv : uint.nat γ.mode.Voters' = γ.R.K := Hrun.2.1.symm
  ihave #Hbrec : bootStorRec «$v3_ptr» ms ((List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1)) $$ []
  · iunfold bootStorRec
    iexists ivl
    iframe Svoters
    isplitr
    · iapply antStorRec_ms $$ Hsrec
    rw [← HKv]; iexact Hivs
  ihave #Hbr := antNC_bridge «$v3_ptr» ms γs $$ Hsrec
  iunfold nodeDownRaft at Hdr
  icases Hdr with ⟨Hvac, Hrs, Hconf, ⟨%Nr, Hcl, Hrfit⟩, %Hdrp⟩
  obtain ⟨Hns, Htr, Hmd, Hbl, Hrt, Hrc, Hrmd, Hrb, HrN⟩ := Hdrp
  have Hlen63 : v.dur.log.length < 2 ^ 63 := by
    have := bootLog_length γ.R
    rw [Hdur]; simp only [startDur]; omega
  ihave Hrst := ant_restartStorage wp_bsInitialState wp_bsSnapshot wp_bsLastIndex wp_bsFirstIndex wp_bsTerm
      wp_bsEntries «$v3_ptr» ms _ γs γ.raft
      (fun K => iprop(memStorMeta ms γs (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) ∗
        memStorInvP ms γs (antJ γ.raft K)))
      (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) v.dur.log Hlen63 Htr Hmd
      $$ Hpkg Hsrec Hbrec Hlock Hlog0 Hlog1 Hend Hmeta Hfresh []
  · iintro %K Hm Hi; iframe Hm Hi
  -- the logger, a `Logger`
  iStructNamedPrefix «$v11» "L"
  ipersist LquietLogger
  ipersist Ln
  ihave #Hlogger := nodeLogger_isLogger wp_Infof wp_Debugf wp_Warningf wp_Errorf «$v11_ptr» n _
    $$ Hpkg LquietLogger Ln Nlog
  -- `NewRawNode`, restarting on the boot storage, at the run's mask
  imod nodeVacant_arm γ.raft (AntSim.nodeId j) ⊤ $$ Hvac with ⟨%x, Hvac, -⟩
  have HmdR : γ.R.md = scopeMd γ.scope := Hrun.2.2.2.2.1
  have Hsn : γ.R.md.snapshots = false := by rw [HmdR]; exact Hb1.2.2.2.2.2.2.1
  have Hcc : γ.R.md.confChanges = false := by rw [HmdR]; exact Hb1.2.2.2.2.2.2.2.1
  have Hasy : γ.R.md.async = false := by rw [HmdR]; exact Hb1.2.2.2.2.2.2.2.2.2
  have Hmi := inScope_inflight Hscope
  have HN9 : γ.R.N ≤ 9 := γ.R.hK.2.2
  have Hsh := start_storageHolds γ.R v.dur Hdur
  have Hlast := start_last γ.R (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) v.dur Hdur
  have Hcv := startConfig_valid γ.mode j HN9 «$v3_ptr» «$v11_ptr» Hmi
  have Hb0 : max (bootContents (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) v.dur.log).b
      (uint.nat (startConfig γ.mode (AntSim.nodeId j) «$v3_ptr» «$v11_ptr»).Applied') ≤ 0 := by
    simp [StorContents.b, bootContents, base0]
  have Hbl' : γ.raft.bootLen ≤
      (bootContents (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) v.dur.log).last := by
    rw [Hbl, Hlast]; exact Nat.le_refl _
  have Hcsi := start_confStateIs γ.R
  have Hrso := start_restartScope γ j «$v3_ptr» «$v11_ptr»
    (bootContents (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) v.dur.log) Hscope Hrun Hrc rfl
  have HNR := wp_NewRawNode γ.R.md Hsn Hcc γ.raft Nr «$a0_ptr»
      (startConfig γ.mode (AntSim.nodeId j) «$v3_ptr» «$v11_ptr»)
      ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.nodeLogger.ty,
        #«$v11_ptr»⟩
      ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty,
        #«$v3_ptr»⟩
      (bootContents (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) v.dur.log)
      (bootConfState ((List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1)) memSnapEmpty) 0
      (Membership.simple γ.R.voters0) (downDur γ.R)
      (fun K => iprop(memStorMeta ms γs (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) ∗
        memStorInvP ms γs (antJ γ.raft K))) (snapshotValid γ.raft)
      (fun _ => .rfl) Hcv rfl rfl (inflight_lt Hmi) rfl rfl rfl
      (Or.inl (by show W64 1048576 ≠ W64 0; decide)) (Hb1.2.1.trans Hasy.symm) (fun h => absurd Hmd h) (Or.inl rfl)
      Hb0 (Nat.zero_le _) Hbl' Hcsi Hns TraceLoggerOk_nil Htr Hsh Hrso x
  wp_apply HNR
    $$ [«$a0» Hrst Hvac Hrs Hconf Hcl Hrfit] as %rn' %err ⟨%Herr, %l, %sn, %g, %K, Hrn, Hcmt, %Hl, Hgv,
      Hsf, Hrs, HF⟩
  · iframe Hlogger Hcl Hrfit Hvac Hrs Hconf
    isplitl [«$a0»]
    · iExactEq «$a0»; rfl
    isplitl [Hrst]
    · iExactEq Hrst; rfl
    iapply antStor_storCapF
  subst Herr
  try wp_auto
  -- the node at the drain's loop head: the view's state, nothing reached yet
  have Hr := restartR_fresh γ.R v Hfresh
    (max (bootContents (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) v.dur.log).b
      (uint.nat (startConfig γ.mode (AntSim.nodeId j) «$v3_ptr» «$v11_ptr»).Applied')) (Nat.le_zero.mp Hb0)
  obtain ⟨HP, Hdel, -, -, -, Hconf0, -, Hpre, Hrd0, -, Hidle, -⟩ := Hfresh
  have Hl0 : l = [] := List.eq_nil_of_length_eq_zero (by rw [Hl.1]; simp [StorContents.b, bootContents, base0])
  subst Hl0
  icases (h_rso γ.raft (AntSim.nodeId j) (downDur γ.R)).1 $$ Hrs with ⟨Hdg, Htlb, Hbud⟩
  icases HF with ⟨Hmeta, -⟩
  ihave Hown : nodeOwn c γ j n { v with alive := true } (.loop [] [] v.r []) $$
      [Nrn Nstore Nrole Nhs Ncause Napp Nconf Nitems Nmhs Nrhs Nwrites Ninfl Napps Napplying Nrest Nwip
        Naip Nconfs NconfBase Hemit Hv Hl Dhs Dsnap Dents Dcap Hmeta Hrn Hgv Hsf Hdg Htlb Hbud]
  · iunfold nodeOwn
    iexists d, rn', ms, hp, null, cs, go!"follower", W64 0
    iframe Nd Nrn Nstore Nrole Nhs Ncause Napp Nconf Hv Hl
    isplitl [Nitems Nmhs Nrhs Nwrites Ninfl Napps Napplying Nrest Nwip Naip Nconfs NconfBase Hemit]
    · iunfold nodeMemB1
      iexists hp, hp
      iframe Nitems Nmhs Nrhs Nwrites Ninfl Napps Napplying Nrest Nwip Naip Nconfs NconfBase Hemit
    isplitr
    · ipureintro; exact Hnorm
    isplitl [Dhs Dsnap Dents Dcap]
    · iunfold diskOwn
      iexists hsl, esl
      iframe Dhs Dhsro Dsnap Dents Dcap Dels
    iexists «$v3_ptr», _, [], _, _
    iframe Hrn
    isplitl [Hmeta]
    · iunfold nodeStor
      iframe Hbrec
      iexists γs
      iframe Hlock Hmeta
      isplitr
      · rw [show (GoInterface.ok ⟨go.GoType.PointerType
            github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #«$v3_ptr»⟩ : Storage) =
            antStorIface «$v3_ptr» from rfl]
        iexact Hbr
      ipureintro; exact Hsz
    isplitr
    · ipureintro; rfl
    isplitl [Hgv Hsf Hdg Htlb Hbud]
    · iunfold nodeRaft
      iexists x, g
      iframe Hgv Hsf
      isplitl [Hdg]
      · iExactEq Hdg; rfl
      isplitl [Htlb]
      · iExactEq Htlb; rfl
      isplitl [Hbud]
      · iexact Hbud
      ipureintro; exact ⟨Hrt, Hrc, Hrmd, Hrb, HrN⟩
    isplitr
    · ipureintro
      refine ⟨⟨rfl, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
      · show (downDur γ.R).ents = v.dur.log
        rw [Hdur]; unfold downDur startDur
        rcases Bool.eq_false_or_eq_true γ.R.boot with hb | hb <;> simp [hb, RaftState.init, AntSim.bootLog]
      · show ([] : List EntryM) = v.delivered ++ v.ce
        rw [Hdel, Hidle.2.2.2.1]; rfl
      · -- (group E's S2) the reported role: the fresh node's follower
        show roleStr _ = AntSim.roleStr v.pre v.r.p.role
        rw [Hpre, HP.2.2.2.1]; rfl
      · -- (group D) raft's durable ghost's term the disk's
        show (downDur γ.R).term = v.dur.term
        rw [Hterm]; unfold downDur
        rcases Bool.eq_false_or_eq_true γ.R.boot with hb | hb <;> simp [hb, RaftState.init]
      · show go!"follower" = AntSim.roleStr v.pre v.r.p.role
        rw [Hpre, HP.2.2.2.1]; rfl
      · show uint.nat (W64 0) = v.delivered.length
        rw [Hdel]; rfl
      · show cfgK (startConfig γ.mode (AntSim.nodeId j) «$v3_ptr» «$v11_ptr») = γ.R.k j
        rw [Hrun.2.2.2.1 j]; rfl
    iframe Hhs Hcs
    isplitr
    · -- (group D) no pending read
      iunfold readsOwn
      simp only [Hrd0]
      iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitr
    · ipureintro; exact Hconf0
    isplitr
    · ipureintro
      refine ⟨Hr, AntSim.Reach.stay _ Hidle (Or.inl Hby), rfl, ?_, Or.inl Hby⟩
      show (bootContents (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) v.dur.log).b +
        (bootContents (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) v.dur.log).ents.length =
        lcpLen v.r.p.log v.r.p.log
      rw [HP.2.2.2.2.2.2.2.1, Hdur]
      rcases Bool.eq_false_or_eq_true γ.R.boot with hb | hb <;>
        simp [hb, startDur, AntSim.bootLog, bootContents, StorContents.b, base0, lcpLen]
    iframe Hlb Hxlb
    iunfold causeOwn
    rw [if_neg (by rw [Hby]; intro h; exact absurd h.1 (by decide))]
    iunfold pendingCause
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  -- the boot drain, then `alone`
  rw [show (go!"boot" : GoString) = ({ v with alive := true } : AntSim.NodeView).byE from Hby.symm]
  wp_apply wp_drain c γ n j { v with alive := true } [] [] v.r [] q $$ [$Hpkg $Hc $Hn $Hown $Had $Htok]
    as %v'' ⟨Hown, Had, Htok, %Hby''⟩
  · ipureintro; exact Hb1
  wp_apply wp_alone c γ n j $$ [$Hpkg $Hc $Hn]
  · ipureintro; exact Hb1.1
  try wp_auto
  iapply HΦ
  iframe Hown Had Htok
  ipureintro; rw [Hby'']

end proof

end AntHarness
end EtcdGrove
end Perennial
