/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__spill.lean` (U9q, `notes/bbolt-proof-plan.md`; U9n's
design): the root bucket's spill. Its loop over the cached children (`wp_map_for_range_gen`, the
invariant `loopP`: `Spill/BktLoopInv`'s `RInv` with the resources), each child spilled
(`Bucket.spill.specC`, `Spill/BktChild`) or freed and written inline, its value put into the root
bucket's leaf (`seek`, `Cursor.node`, `node.put`); then the root bucket's root node spilled (top
case), `b.rootNode = root()`, `SetRootPage`, as `Spill/BktChild`'s tail; the post from
`rinv_end`/`rinv_end_nil`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktChild
public import Proof.go_etcd_io.bbolt.Spill.BktLoopInv
public import Spec.go_etcd_io.bbolt.Bucket__spill
public import Proof.go_etcd_io.bbolt.Rebalance.BktRbl
public import Proof.go_etcd_io.bbolt.Read.WOpenH
public import Proof.go_etcd_io.bbolt.Read.WCtx
public import Proof.go_etcd_io.bbolt.Spill.Inlineable
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_i
public import Spec.go_etcd_io.bbolt.Cursor__seek_w
public import Spec.go_etcd_io.bbolt.Cursor__node
public import Spec.go_etcd_io.bbolt.node__put
public import Spec.go_etcd_io.bbolt.Bucket__free
public import Spec.go_etcd_io.bbolt.Bucket__write
public import Perennial.Spec.bytes.Equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill
section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The frozen spec's post (what `Φ` is given at `return`). -/
def spillPost (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ (X' : WX) (w' : WDb), wtxW K tx r m X' ∗ wdbW K tx X'.v w' ∗
        ⌜spillOK X X' w.C w.fl w'.fl w.wtxid ∧ w'.C = w.C ∧
          derefPre X' ∧ liveFresh X' ∧ liveReach X' ∧
          X'.t.mv.pgid'.toNat * 4096 ≤ mapLen w'.ms ∧ flViewU X' w'.fl⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ ∃ (X' : WX) (w' : WDb) (st : List FLStep),
        ⌜w'.C = w.C ∧ w'.fl = w.fl.applySteps w.wtxid st ∧
          X'.v.pages = X.v.pages⌝ ∗
        ((wtxW K tx r m X' ∗ wdbW K tx X'.v w') ∨ (wtxLost K tx r m X' ∗ wdbLost K tx X'.v w'))))

/-- **The root loop's invariant** with its resources: the post's continuation, the locals, the
records (the map's points-to apart) and the writer side. -/
def loopP (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (B0 : BRec)
    (Φ : val → IProp GF) (res bp cp np : Loc) (keys : List GoString) (i : Nat)
    (m' : GMap GoString Loc) : IProp GF :=
  iprop(⌜m' = B0.bm⌝ ∗ (∀ err, spillPost K tx r m X w err -∗ Φ #err) ∗ res ↦ GoInterface.nil ∗
    bp ↦ X.rl ∗ (∃ cv : Loc, cp ↦ cv) ∗ (∃ nv : GoString, np ↦ nv) ∗
    ∃ (X' : WX) (w' : WDb) (st : List FLStep) (Lroot : List Nat) (Dc : GoString → List Nat)
      (ks : GoString → KSt),
      (B0.bv.buckets' ↦$ B0.bm -∗ wtxW K tx r m X') ∗ wdbW K tx X'.v w' ∗
      ⌜RInv X w B0 keys Lroot X' w' st Dc ks ∧ ksAt keys i ks⌝)

theorem _root_.Perennial.EtcdGrove.bbolt.Bucket.spill.wp_proof (hNS : node.spill.spec' (GF := GF) (hG := hG))
    (hRoot : node.root.spec (GF := GF) (hG := hG))
    (hPgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hSRP : internal.common.InBucket.SetRootPage.spec (GF := GF) (hG := hG)) :
    Bucket.spill.spec (GF := GF) (hG := hG) := by
  intro K tx r m X w Hpre Hreach Hml Hfv
  iintro %Φ ⟨Hw, Hdb⟩ HΦ
  icases wtxW_open K tx r m X $$ Hw with ⟨#Hpk, #Hcore, #Hreg, Hh, Hv, Hst, Hclose⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  ihave Hw := Hclose $$ %X [] Hh Hv Hst
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨B0, HB0⟩ : ∃ B0, X.t.bs !! X.rl = some B0 := Option.isSome_iff_exists.1 Hpre.1.1.2.2.2.2.1
  rw [show tx.[Tx, go!"root"] = X.rl from Hok.1.symm]
  icases wtxW_buckets_fld K tx r m X X.rl B0 HB0 $$ Hw with ⟨Hbf, Hwb⟩
  wp_method_call
  wp_call
  try wp_auto
  ihave Hw := Hwb $$ Hbf
  icases wtxW_bm_acc K tx r m X X.rl B0 HB0 _ _ rfl rfl $$ Hw with ⟨Hbm, Hwb⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (loopP K tx r m X w B0 Φ «$res0_ptr» b_ptr child_ptr name_ptr) $$ Hbm
  iintro %keys ⟨%Hkset, %Hklen, %Hknd⟩
  isplitl [HΦ «$res0» b child name Hwb Hdb]
  · unfold wdbW
    icases Hdb with ⟨Hdl, %Hwf⟩
    obtain ⟨Lroot, Dc, HI⟩ := rinv_start Hpre Hreach Hml Hfv Hwf HB0 keys
      (fun k => Hkset k) Hknd
    unfold loopP
    isplitr
    · ipureintro; rfl
    iframe
    iexists w
    iexists ([] : List FLStep)
    iexists Lroot
    iexists Dc
    iexists (fun _ => KSt.todo)
    iframe
    unfold wdbW
    isplitl
    · iframe; ipureintro; exact Hwf
    ipureintro
    exact ⟨HI, fun j k _ => ⟨fun h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  isplitr
  · iintro !> %i %key %c %m' ⟨%Hkey, %Hc⟩ HP Hbm
    sorry
  isplitr
  · iintro !> %i %key %m' ⟨%Hkey, %Hc⟩ HP
    unfold loopP
    icases HP with ⟨%Hm, -⟩
    subst Hm
    have h := (Hkset key).1 (List.mem_of_getElem? Hkey)
    rw [Hc] at h; cases h
  iintro %m' HP Hbm
  unfold loopP
  icases HP with ⟨%Hm, HΦ, Hres, Hb, Hc, Hn, %X1, %w1, %st, %Lroot, %Dc, %ks, Hwb, Hdb, %HI⟩
  subst Hm
  ihave Hw := Hwb $$ Hbm
  obtain ⟨HI, Hks⟩ := HI
  obtain ⟨B, HB, -, -⟩ := HI.root
  have Hrl : X1.rl = X.rl := HI.rl
  have Hlive1 : X.rl ∈ X1.liveB := HI.rootOK.1.1
  icases wtxW_open K tx r m X1 $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hclose⟩
  icases wtxHeap_bkt_peek tx _ X1 X.rl B HB Hlive1 $$ Hh with ⟨Ho, Hhb⟩
  unfold objOwn
  icases Ho with ⟨Hib, Htx, Hbk, Hpg, Hrn, Hnd, Hibv, Hnm, Hbm, Hpo⟩
  try wp_auto
  have HwX : w1.wtxid = w.wtxid := wtxid_of_C HI.C
  by_cases Hnull : B.bv.rootNode' = null
  · rw [decide_eq_true Hnull]
    try wp_auto
    ihave Hh := Hhb $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo]
    · dsimp only; iframe
    ihave Hw := Hclose $$ %X1 [] Hh Hv Hst
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    obtain ⟨Hok1, Hfv1⟩ := rinv_end_nil Hpre Hreach Hfv HB0 Hkset HI Hks HB Hnull
    have HG := HI.G
    iapply HΦ
    unfold spillPost
    ileft
    isplitr
    · ipureintro; rfl
    iexists X1, w1
    iframe
    ipureintro
    exact ⟨Hok1, HI.C, HG.2.2.1, HG.2.2.2.1, HG.2.2.2.2.1, HG.2.1, Hfv1⟩
  rw [decide_eq_false Hnull]
  try wp_auto
  ihave Hh := Hhb $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo]
  · dsimp only; iframe
  ihave Hw := Hclose $$ %X1 [] Hh Hv Hst
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨rn, h, F, D, N, E, Hun, Hsp, Hfin⟩ := rinv_end Hpre Hreach Hfv HB0 Hkset HI Hks HB Hnull
  wp_apply hNS K tx r m X1 w1 X.rl B.bv.rootNode' rn [] none none h F D N E .top Hsp $$ [Hw Hdb]
    as %err Hpost
  · iframe
  try wp_auto
  unfold spPost
  icases Hpost with (⟨%he, %X2, %w2, %st2, Hw, Hdb, %Hdone⟩ | ⟨%hne, #HeOk, %X2, %w2, %st2, %Hst2, Hcase⟩)
  · subst he
    try wp_auto
    have Hdone' := Hdone
    obtain ⟨Hstep, Hc⟩ := Hdone
    rcases Hc with ⟨Hsp1, -, -⟩ | ⟨-, T, D', Hfr, -, Hsi', HD1, HD2, -, rt, rr, S, h', Hrt, Hrtl,
      Hrsp, Hrpar, ⟨B1, HB1, Hroot⟩, HsT, HD', HEls⟩
    · rw [Hun] at Hsp1; cases Hsp1
    obtain ⟨B2, HB2, Hsim, -⟩ := Hfr.2.2.2.2.2.2.2.2.2.2.2.2.2.1 B HB
    rw [HB1] at HB2; cases HB2
    have Hlive2 : X.rl ∈ X2.liveB := by rw [Hfr.2.2.2.1]; exact Hlive1
    have Hbv : B1.bv = B.bv := Hsim.1
    rw [← Hbv] at Hroot
    icases wtxW_open K tx r m X2 $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hclose⟩
    icases wtxHeap_bkt_peek tx _ X2 X.rl B1 HB1 Hlive2 $$ Hh with ⟨Ho, Hhb⟩
    unfold objOwn
    icases Ho with ⟨Hib, Htx, Hbk, Hpg, Hrn, Hnd, Hibv, Hnm, Hbm, Hpo⟩
    try wp_auto
    ihave Hh := Hhb $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo]
    · dsimp only; iframe
    wp_apply hRoot tx (DFrac.own 1) X2 X.rl B1 B1.bv.rootNode' rt HB1 Hroot $$ [Hh] as Hh
    · iframe
    try wp_auto
    obtain ⟨B3, HB3, Hrr⟩ := bk_node_of_bs Hrt
    rw [HB1] at HB3; cases HB3
    ihave %Hok2 := wtxHeap_heapOK tx (DFrac.own 1) X2 $$ Hh
    have hbtx : B1.bv.tx' = tx := Hok2.2.2.1 X.rl B1 HB1
    icases wtxHeap_setBkt_acc tx (DFrac.own 1) X2 X.rl B1 [rt] (fun _ => rr) HB1 (nodup_one rt)
      (by intro l hl; rw [List.mem_singleton.1 hl]; exact Hrr) $$ Hh
      with ⟨⟨Hn, -⟩, Hbo, Hf, Hrf, Hback⟩
    rw [decide_eq_true Hrtl, decide_eq_true Hlive2]
    icases objOwn_node_ptr_acc X2.v rt (DFrac.own 1) true X.rl rr $$ Hn with ⟨Hn, Hnback⟩
    unfold objOwn
    icases Hbo with ⟨Hib, Htx, Hbk, Hpg, Hrn, Hnd, Hibv, Hnm, Hbm, Hpo⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    iStructNamed Hn
    ihave Htxf : (∃ dqb : DFrac, X.rl.[Bucket, go!"tx"] ↦{dqb} tx ∗
        (X.rl.[Bucket, go!"tx"] ↦{dqb} tx -∗
          if X.rl = B1.bv.tx'.[Tx, go!"root"] then X.rl.[Bucket, go!"tx"] ↦ B1.bv.tx'
          else X.rl.[Bucket, go!"tx"] ↦□ B1.bv.tx') : IProp GF) $$ [Htx]
    · rw [hbtx]
      by_cases hroot : X.rl = tx.[Tx, go!"root"]
      · rw [if_pos hroot]
        iexists DFrac.own 1
        iframe
        iintro H; iexact H
      · rw [if_neg hroot]
        icases Htx with #Htx
        iexists DFrac.discard
        isplitr
        · iexact Htx
        · iintro _; iexact Htx
    icases Htxf with ⟨%dqb, Htx, Htxb⟩
    unfold txFields
    icases Hf with ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩
    try wp_auto
    wp_apply hPgid X2.t.t.meta' X2.t.mv (DFrac.own 1) $$ [Hmv] as Hmv
    · iframe
    have Hlt : rr.nv.pgid'.toNat < X2.t.mv.pgid'.toNat := by
      cases HsT.wf with | page _ _ _ hlt _ _ _ _ => exact hlt
    try wp_auto
    rw [decide_eq_false (by word)]
    try wp_auto
    wp_method_call
    try wp_call
    try wp_auto
    wp_apply hSRP B1.bv.InBucket' B1.ib rr.nv.pgid' $$ [Hibv] as Hibv
    · iframe
    try wp_auto
    ihave Hn : (rt ↦ rr.nv : IProp GF)
      $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hn := Hnback $$ Hn
    ihave Htx := Htxb $$ Htx
    have Hrt0 : rt ≠ null := by
      intro h0; rw [h0, (Hstep.2.2.2.1.2.2.1.2.2.1 X.rl B1 HB1).2] at Hrr; cases Hrr
    ihave Hh := Hback $$ %(bkRooted B1 rt rr.nv.pgid') %(fun _ => rr) [] [Hn] [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo] [Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs] Hrf
    · ipureintro
      refine ⟨?_, fun _ _ => rfl, rfl, ?_⟩
      · intro l hl; rw [List.mem_singleton.1 hl]; exact Hrr
      · intro l hl; rw [List.mem_singleton.1 hl, Hrpar]; exact Ne.symm Hrt0
    · iapply BigSepL.bigSepL_singleton.2; rw [decide_eq_true Hrtl]; iexact Hn
    · dsimp only [bkRooted]
      iframe
    · iframe
    ihave Hw := Hclose $$ %(X2.setBkt X.rl (bkRooted B1 rt rr.nv.pgid')) [] Hh Hv Hst
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    try wp_auto
    obtain ⟨Hok', Hfv'⟩ := Hfin X2 w2 st2 B1 rt rr Hdone' HB1 Hrr Hrtl Hrsp Hrpar Hroot
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := Hstep
    have HG' := spG_bkRooted (fl := w2.fl) rr.nv.pgid' s4 HB1 Hrr Hrpar Hrtl Hroot
    rw [HwX] at HG'
    iapply HΦ
    unfold spillPost
    ileft
    isplitr
    · ipureintro; rfl
    iexists X2.setBkt X.rl (bkRooted B1 rt rr.nv.pgid'), w2
    iframe
    ipureintro
    exact ⟨Hok', s1.trans HI.C, HG'.2.2.1, HG'.2.2.2.1, HG'.2.2.2.2.1, s5, Hfv'⟩
  · cases err with
    | nil => exact absurd rfl hne
    | ok ii =>
    try wp_auto
    iapply HΦ
    unfold spillPost
    iright
    isplitr
    · ipureintro; exact hne
    isplitr
    · iexact HeOk
    iexists X2, w2, st ++ st2
    isplitr
    · ipureintro
      refine ⟨Hst2.1.trans HI.C, ?_, Hst2.2.2.trans HI.pages⟩
      rw [Hst2.2.1, HI.fl, HwX, applySteps_append]
    iexact Hcase

end proof
end Spill
end bbolt
end EtcdGrove
end Perennial
