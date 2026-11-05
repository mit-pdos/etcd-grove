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
public import Proof.go_etcd_io.bbolt.Spill.BktLoopStep
public import Proof.go_etcd_io.bbolt.Spill.BktEnd
public import Proof.go_etcd_io.bbolt.Spill.BktEndPend
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailWp
public import Proof.go_etcd_io.bbolt.Spill.BktLoopHeap
public import Proof.go_etcd_io.bbolt.Spill.BktPm
public import Proof.go_etcd_io.bbolt.Commit.AssembleAcc
public import Proof.go_etcd_io.bbolt.Read.WOpenOK
public import Spec.go_etcd_io.bbolt.Bucket__spill
public import Proof.go_etcd_io.bbolt.Rebalance.BktRbl
public import Proof.go_etcd_io.bbolt.Read.WCtx
public import Proof.go_etcd_io.bbolt.Read.WOpenH
public import Proof.go_etcd_io.bbolt.Spill.Inlineable
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_i
public import Spec.go_etcd_io.bbolt.Cursor__seek_w
public import Spec.go_etcd_io.bbolt.Cursor__node
public import Spec.go_etcd_io.bbolt.node__put
public import Spec.go_etcd_io.bbolt.Bucket__free
public import Spec.go_etcd_io.bbolt.Bucket__write
public import Perennial.Spec.bytes.Equal
public import Proof.go_etcd_io.bbolt.Inv.WAccess

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
          X'.t.mv.pgid'.toNat * 4096 ≤ mapLen w'.ms ∧
          spillBufs X' w.C w'.fl ∧
          X'.t.t = X.t.t ∧ X'.rl = X.rl ∧ (X'.t.bs !! X'.rl).isSome ∧
          X'.t.mv = { X.t.mv with pgid' := X'.t.mv.pgid' } ∧
          (∀ s ∈ treeSlots (spillC X' w.C.pages), s ∉ pendSlots w'.fl) ∧
          markCov X' w.C.hwm ∧
          ∀ s ∈ bufSlots X'.t.bufs, W64 s ∈ w.fl.free ∨ w.C.hwm ≤ s⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ ∃ (X' : WX) (w' : WDb) (st : List FLStep),
        ⌜w'.C = w.C ∧ w'.fl = w.fl.applySteps w.wtxid st ∧
          X'.v.pages = X.v.pages ∧ X'.t.t = X.t.t ∧ X'.rl = X.rl ∧ (X'.t.bs !! X'.rl).isSome ∧
          X'.t.mv = { X.t.mv with pgid' := X'.t.mv.pgid' }⌝ ∗
        ((wtxW K tx r m X' ∗ wdbW K tx X'.v w') ∨ (wtxLost K tx r m X' ∗ wdbLost K tx X'.v w'))))

/-- The loop's records are an error's (`spErr`) from the start. -/
theorem rinv_spErr {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) : spErr X0 X w0 w st := by
  refine ⟨hI.C, by rw [hI.fl], hI.pages, hI.tt, hI.rl, fun _ => ?_, hI.mvEq⟩
  obtain ⟨B, hB, -⟩ := hI.root
  rw [hI.rl, hB]; rfl

/-- The spec's error facts from `spErr` (the root bucket present at the start). -/
theorem errFacts_of_spErr {X X' : WX} {w w' : WDb} {st : List FLStep} (h : spErr X X' w w' st)
    (hr : (X.t.bs !! X.rl).isSome) :
    w'.C = w.C ∧ w'.fl = w.fl.applySteps w.wtxid st ∧
      X'.v.pages = X.v.pages ∧ X'.t.t = X.t.t ∧ X'.rl = X.rl ∧ (X'.t.bs !! X'.rl).isSome ∧
      X'.t.mv = { X.t.mv with pgid' := X'.t.mv.pgid' } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1 hr, h.2.2.2.2.2.2⟩

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
    (hSRP : internal.common.InBucket.SetRootPage.spec (GF := GF) (hG := hG))
    (hInl : Bucket.inlineable.spec (GF := GF) (hG := hG))
    (hCur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hSeek : Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hNode : Cursor.node.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG))
    (hFree : Bucket.free.spec (GF := GF) (hG := hG))
    (hWrite : Bucket.write.spec (GF := GF) (hG := hG)) :
    Bucket.spill.spec (GF := GF) (hG := hG) := by
  intro K tx r m X w Hpre Hreach Hml Hfv HsOK Htx Hmc
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
  · icases keep_pure (Q := wdbW K tx X.v w)
      (P := wdbOK w ∧ w.ms = some (X.v.base, mapLen w.ms) ∧ X.v = View.ofC X.v.base w.C)
      (by unfold wdbW; iintro ⟨-, %H⟩; ipureintro; exact H) $$ Hdb with ⟨Hdb, %Hwf⟩
    icases keep_pure (Q := wdbW K tx X.v w) (P := mapLen w.ms ≤ 0xFFFFFFFFFFFF)
      (wdbW_mapLen_le K tx X.v w) $$ Hdb with ⟨Hdb, %Hl⟩
    icases keep_pure (Q := wdbW K tx X.v w) (P := w.fl.WF ∧ w.C.hwm < 2 ^ 48)
      (cm_wdbW_bounds K tx X.v w) $$ Hdb with ⟨Hdb, %Hfwf⟩
    obtain ⟨Lroot, Dc, HI⟩ := rinv_start Hpre Hreach Hml Hfv Hwf HB0 keys
      (fun k => Hkset k) Hknd Hl HsOK Hfwf.1
    unfold loopP
    isplitr
    · ipureintro; rfl
    isplitl [HΦ]
    · unfold spillPost; iintro %err Hpost; iapply HΦ; iexact Hpost
    iframe «$res0» b
    isplitl [child]
    · iexists _; iexact child
    isplitl [name]
    · iexists _; iexact name
    iexists X
    iexists w
    iexists ([] : List FLStep)
    iexists Lroot
    iexists Dc
    iexists (fun _ => KSt.todo)
    iframe
    iframe
    ipureintro
    exact ⟨HI, fun j k _ => ⟨fun h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  isplitr
  · iintro !> %i %key %c %m' ⟨%Hkey, %Hc⟩ HP Hbm
    unfold loopP
    icases HP with ⟨%Hm, HΦ, Hres, Hb, ⟨%cv, Hcp⟩, ⟨%nv, Hnp⟩, %X1, %w1, %st, %Lroot, %Dc, %ks, Hwb, Hdb, %HI⟩
    subst Hm
    ihave Hw := Hwb $$ Hbm
    obtain ⟨HI, Hks⟩ := HI
    have Hkm : key ∈ keys := List.mem_of_getElem? Hkey
    have Htodo := ksAt_todo Hks Hkey
    obtain ⟨C, HC, HcL, HCbm, Hcne, HcLoc, HcRt, HcEnts, HcNil, HcTree⟩ := rinv_todo HI Htodo Hc
    icases wtxW_heapOK' K tx r m X1 $$ Hw with ⟨Hw, %Hok1⟩
    have Hctx : C.bv.tx' = tx := (Hok1.2.2.1 c C HC).1
    have Hcr : c ≠ C.bv.tx'.[Tx, go!"root"] := by
      rw [Hctx, show tx.[Tx, go!"root"] = X1.rl from Hok1.1.symm]; exact Hcne
    wp_auto
    obtain ⟨nv0, ins0, Hn0, Hrn0⟩ : ∃ (nv0 : node) (ins0 : List Inode),
        (C.bv.rootNode' = null → ins0 = []) ∧
        (C.bv.rootNode' ≠ null → ∃ rn, C.ns !! C.bv.rootNode' = some rn ∧ rn.nv = nv0 ∧
          rn.ins = ins0 ∧ C.bv.rootNode' ∈ X1.live ∧ wsLive rn.ws ∧
          ∀ w ∈ rn.ws, w.key.length + w.value.length ≤ bboltEntryMax) := by
      by_cases hn : C.bv.rootNode' = null
      · exact ⟨zero_val node, [], fun _ => rfl, fun h => absurd hn h⟩
      · obtain ⟨rn, -, hns, hl, hlv, hbd⟩ := rinv_inlPre HI Htodo Hc HC hn
        exact ⟨rn.nv, rn.ins, fun h => absurd h hn, fun _ => ⟨rn, hns, rfl, rfl, hl, hlv, hbd⟩⟩
    icases wtxW_inl_acc K tx r m X1 c C nv0 ins0 HC HcL Hcr Hn0 Hrn0 $$ Hw
      with ⟨#H2, H5, Hnd, Hdbf, #Hps, %Hlens, Hwb⟩
    rw [Hctx]
    wp_apply hInl c C.bv.rootNode' nv0 ins0 tx K.db (DFrac.own 1) (DFrac.own 1)
      (DFrac.own 1) DFrac.discard (DFrac.own (txDbQ 1)) (fun it hit _ => Hlens it hit)
      $$ [H5 Hnd Hdbf] as ⟨H5, Hnd, -, Hdbf⟩
    · iframe; iframe #
    ihave Hw := Hwb $$ H5 Hnd Hdbf
    by_cases Hinl : C.bv.rootNode' ≠ null ∧ nv0.isLeaf' = true ∧ inlineIns ins0
    · rw [decide_eq_true Hinl]
      try wp_auto
      obtain ⟨Hnn0, Hleaf0, Hinl0⟩ := Hinl
      obtain ⟨rn, Hrnx, Hrns, Hlrn, Hwlrn, -⟩ := rinv_inlPre HI Htodo Hc HC Hnn0
      obtain ⟨rn', Hrns', Hnv, Hins, -⟩ := Hrn0 Hnn0
      rw [Hrns] at Hrns'; cases Hrns'
      subst Hnv Hins
      icases wtxW_lens K tx r m X1 c C.bv.rootNode' rn Hrnx Hlrn Hwlrn $$ Hw with ⟨Hw, %Hlens⟩
      icases wdbW_ofC K tx X1.v w1 $$ Hdb with ⟨Hdb, %HvC1⟩
      wp_apply hFree K tx r m X1 w1 c C HC HcL (rinv_freePre HI Htodo Hc HC Hrnx Hleaf0)
        $$ [Hw Hdb] as ⟨%X2, %w2, Hw, Hdb, %Hfr⟩
      · iframe
      obtain ⟨C1, rn1, st', HC1, Hroot1, Hrn1, Hl1, HcL1, Hv12, Hleaf1, Hwl1, Hlen1, Hfit1, Hsz1,
        Hsz31, HI2⟩ := rinv_inline HI Htodo Hc HC Hrnx Hleaf0 Hinl0 Hlens Hknd
          (congrArg View.pages HvC1) Hfr
      rw [← Hv12]
      try wp_auto
      icases wtxW_bkt_root_acc K tx r m X2 c C1 C.bv.rootNode' rn1 HC1 HcL1 Hrn1 Hl1 $$ Hw
        with ⟨%Hbase2, Ho, Hno, Hcells, Hdbf, -, Hwb2⟩
      isimp only [objOwn] at Ho
      icases Ho with ⟨G1, G2, G3, G4, G5, G6, G7, G8, G9, G10⟩
      icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
      icases Hws with #Hws
      icases wOwns_write_acc X2.v Hbase2 rn1.ins rn1.ws wq Hwl1 $$ [Hws Hcells]
        with ⟨%qk, %qv, Hib, Hibback⟩
      · iframe; iexact Hws
      rw [← Hroot1]
      wp_apply hWrite c C1.bv.InBucket' C1.ib C1.bv.rootNode' rn1.nv rn1.ins (wsMs rn1.ws)
          (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) qk qv Hleaf1 Hlen1 Hfit1 Hsz1 Hsz31
        $$ [G1 G7 G5 Hn Hins Hib] as %val ⟨Hval, Hvcap, G1, G7, G5, Hn, Hins, Hib⟩
      · iframe; iframe #; unfold insBytes; iframe
      try wp_auto
      ihave Hcells := Hibback $$ [Hib]
      · unfold insBytes; iexact Hib
      rw [Hroot1]
      ihave Hno := (objOwn_live_node X2.v C.bv.rootNode' (DFrac.own 1) c rn1).2
        $$ [Hn Hins Hcap Hch Hchcap Hkey]
      · iframe; iexact Hws
      ihave Hw := Hwb2 $$ [G1 G2 G3 G4 G5 G6 G7 G8 G9 G10] [Hno] Hcells Hdbf
      · isimp only [objOwn]; rw [Hroot1]; iframe
      · iexact Hno
      rw [show encode C1.ib ++ encode (hdrWritten ⟨W64 0, W16 0, W16 0, W32 0⟩ true
          (wsMs rn1.ws).length) ++ pageBody true (wsMs rn1.ws) = inlineVal C1.ib rn1.ws from rfl]
      rw [decide_eq_false Hnn0]
      try wp_auto
      have Hv2 := Hv12
      obtain ⟨Br, HBr, -, -⟩ := HI2.root
      icases wtxW_cursor_acc K tx r m X2 X.rl Br HBr $$ Hw with ⟨-, -, Hst, %dt, Htx, Hwbc⟩
      wp_apply hCur K tx r m 1 X.rl dt $$ [Hst Htx] as %cur ⟨%stk, Hcu, Hs, Hscap, Hst, Htx⟩
      · iframe; iframe #
      ihave Hw := Hwbc $$ Hst Htx
      try wp_auto
      wp_apply wp_string_to_bytes key as %ksl ⟨Hksl, Hkcap⟩
      imod ownSlice_persist ksl _ _ $$ Hksl with #Hksl
      have HlocR : bktLocalOK X2 X.rl := HI2.rootOK.1
      wp_apply hSeek K tx r m X2 X.rl cur stk [] ksl key (KeyR.heap DFrac.discard) HlocR
        (pmFresh_of_spG HI2.G) $$ [Hw Hcu Hs Hscap]
        as %k %vl %fl ⟨%stk', %els, %pids, Hw, Hcu, Hs, Hscap, Hkey, %Hrt, Hkv⟩
      · iframe; unfold keyR; iexact Hksl
      obtain ⟨Hp, Hr⟩ := Hrt
      obtain ⟨p, ws, ⟨j, hpj⟩, hL, hle⟩ := WOpen.lPath_leaf X2 X.rl Br HBr HlocR els pids Hp
      have hpI := WOpen.lPath_posI X2 X.rl Br HBr HlocR els pids Hp j p hpj
      have hfa := WOpen.route_found_at X2 X.rl els pids key HlocR Hp Hr
      obtain ⟨we, hwe, hwk, hwf⟩ := rinv_entry Hpre Hreach Hfv HB0 HI2 Hc
      have hw := hfa we hwe hwk
      rw [hle] at hw
      rw [hle, hw]
      icases Hkv with ⟨%Hkw, #Hks, #Hvs⟩
      have hwm : we ∈ ws := List.mem_of_getElem? hw
      obtain ⟨hlk, hlv⟩ := WOpen.leaf_live X2 X.rl Br HBr HlocR p hpI ws hL we hwm
      try wp_auto
      wp_apply wp_string_to_bytes key as %ksl2 ⟨Hksl2, -⟩
      icases wtxW_cells_acc K tx r m X2 $$ Hw with ⟨%Hbase, Hcells, Hwbc⟩
      icases viewCells_src_acc wq X2.v Hbase k _ we.key
        (WOpen.leafSrc_live X2 X.rl Br HBr HlocR _ hlk) $$ [Hcells] with ⟨%dk, Hkk, Hcb⟩
      · iframe; iframe #
      wp_apply hEq ksl2 k (DFrac.own 1) dk key we.key $$ [Hksl2 Hkk] as ⟨-, Hkk⟩
      · iframe
      ihave Hcells := Hcb $$ Hkk
      ihave Hw := Hwbc $$ Hcells
      rw [decide_eq_true hwk.symm]
      try wp_auto
      have hbf : ¬ (fl &&& W32 1 = W32 0) := by rw [Hkw.2]; exact hwf
      rw [decide_eq_false hbf]
      try wp_auto
      wp_apply wp_string_to_bytes key as %ok ⟨Hok, -⟩
      imod ownSlice_persist ok _ _ $$ Hok with #Hok
      wp_apply wp_string_to_bytes key as %nk ⟨Hnk, -⟩
      imod ownSlice_persist nk _ _ $$ Hnk with #Hnk
      imod ownSlice_persist val _ _ $$ Hval with #Hval
      try wp_auto
      icases wtxW_nodes_nonnull K tx r m X2 X.rl Br HBr $$ Hw with ⟨Hw, %Hnn⟩
      obtain ⟨Hroot0, Hvwf, Hpready⟩ := rinv_ready Hpre HB0 HI2 HBr Hp
      icases wtxW_matReady_all K tx r m X2 Br pids Hroot0 Hvwf Hpready $$ Hw with ⟨Hw, %Hmr⟩
      wp_apply hNode K tx r m X2 X.rl Br cur stk' els pids (DFrac.own 1) HBr HlocR Hp Hnn Hmr
        $$ [Hw Hcu Hs] as %l ⟨%X3, Hw, Hcu, Hs, %Hcn⟩
      · iframe
      obtain ⟨Hmg, -, HlocR', B3, pid, HB3, Hlast, Hres⟩ := Hcn
      obtain ⟨rl, Hrl, Hll, Hrlb, Hcap, Hsrt, Hwl, Hmk, Hv3, Hpar, Hkl, -⟩ :=
        rinv_putPre HI2 Hmg Hp Hr HB3 Hlast Hres ⟨we, hwe, hwk⟩
      icases wtxW_open K tx r m X3 $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hclose⟩
      ihave %Hok3 := wtxHeap_heapOK tx (DFrac.own 1) X3 $$ Hh
      have Htx3 : B3.bv.tx' = tx := (Hok3.2.2.1 X.rl B3 HB3).1
      have HlB3 : X.rl ∈ X3.liveB := HlocR'.1
      icases wtxHeap_setNode_acc tx (DFrac.own 1) X3 X.rl B3 l rl HB3 Hrl $$ Hh
        with ⟨Hno, Hbo, Hf, Hrf, Hback⟩
      rw [decide_eq_true Hll, decide_eq_true HlB3]
      isimp only [objOwn] at Hbo
      icases Hbo with ⟨Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10⟩
      have Hroot1 : X.rl = B3.bv.tx'.[Tx, go!"root"] := by
        rw [Htx3]; exact Hok.1
      rw [if_pos Hroot1, Htx3]
      unfold txFields
      icases Hf with ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩
      have Hbase3 : 0 < X3.v.base.addr := by rw [Hv3]; exact Hbase
      wp_apply hPut X3.v l X.rl rl tx X3.t.t.meta' X3.t.mv (DFrac.own 1) (DFrac.own 1) wq ok nk val key key
          (inlineVal C1.ib rn1.ws) (Src.own DFrac.discard) (Src.own DFrac.discard) (Src.own DFrac.discard)
          (W64 0) (W32 1) Hrlb Hcap Hsrt Hwl (by simpa using Hmk) Hkl Hkl (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h) Hbase3
        $$ [Hno Hv Q2 Hmeta Hmv] as ⟨%sl, %ins', Hno, Hv, Q2, Hmeta, Hmv⟩
      · iframe; iframe #; unfold srcOwn; iframe #
      try wp_auto
      icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn5, Hins5, Hcap5, Hws5, Hch5, Hchcap5, Hkey5⟩
      ihave %Hinsl := BigSepL2.bigSepL2_length $$ Hws5
      ihave Hno := (objOwn_live_node _ l (DFrac.own 1) X.rl _).2
        $$ [Hn5 Hins5 Hcap5 Hws5 Hch5 Hchcap5 Hkey5]
      · iframe
      ihave Hh := Hback $$ %(rl.withEnts sl ins' (wsPutAt rl.ws key
          ⟨W32 1, W64 0, key, inlineVal C1.ib rn1.ws, Src.own DFrac.discard, Src.own DFrac.discard⟩))
        %(by simpa [NRec.withEnts] using Hpar) [Hno] [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10]
        [Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs] Hrf
      · iexact Hno
      · isimp only [objOwn]
        rw [if_pos Hroot1, Htx3]
        iframe
      · iframe
      ihave Hw := Hclose $$ %(X3.setNode X.rl l (rl.withEnts sl ins'
          (wsPutAt rl.ws key ⟨W32 1, W64 0, key, inlineVal C1.ib rn1.ws, Src.own DFrac.discard, Src.own DFrac.discard⟩))) [] Hh Hv Hst
      · ipureintro; rw [setNode_eq X3 X.rl l B3 _ HB3]; exact ⟨rfl, rfl, rfl⟩
      have HI4 := rinv_put HI2 (upd_same ks key _) Hc Hmg Hp Hr HB3 Hlast Hres Hrl sl ins' Hinsl
            ⟨we, hwe, hwk, hwf⟩
      rw [upd_upd, show rootEnt key (inlineVal C1.ib rn1.ws) = ⟨W32 1, W64 0, key, inlineVal C1.ib rn1.ws, Src.own DFrac.discard, Src.own DFrac.discard⟩ from rfl] at HI4
      obtain ⟨Br4, HBr4, Hbk4, Hbm4⟩ := HI4.root
      icases wtxW_bm_acc K tx r m _ X.rl Br4 HBr4 B0.bv.buckets' B0.bm Hbk4 Hbm4 $$ Hw
        with ⟨Hbm, Hwb⟩
      have Hv4 : (X3.setNode X.rl l (rl.withEnts sl ins'
          (wsPutAt rl.ws key ⟨W32 1, W64 0, key, inlineVal C1.ib rn1.ws, Src.own DFrac.discard, Src.own DFrac.discard⟩))).v = X2.v := by
        rw [setNode_eq X3 X.rl l B3 _ HB3]; exact Hv3
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists B0.bm
      iframe Hbm
      isplitr
      · ipureintro; rfl
      iframe
      iexists w2, (st ++ st'), Lroot, upd Dc key [], upd ks key (.val (inlineVal C1.ib rn1.ws) true)
      rw [Hv4]
      iframe
      ipureintro
      exact ⟨HI4, ksAt_step Hknd Hks Hkey _ ⟨(fun h => nomatch h), (fun v h => nomatch h)⟩⟩
    · rw [decide_eq_false Hinl]
      try wp_auto
      obtain ⟨h, F, N, Hbk⟩ := rinv_bkPre HI Hknd Hkm Htodo Hc HC
      wp_apply (Bucket.spill.wp_child hNS hRoot hPgid hSRP) K tx r m X1 w1 c C _ h F (Dc key) N Hbk
        $$ [Hw Hdb] as %err Hpost
      · iframe
      unfold bkPost
      icases Hpost with (⟨%he, %X2, %w2, %st2, Hw, Hdb, %Hdone⟩ |
        ⟨%hne, #HeOk, %X2, %w2, %st2, %Hst2, Hcase⟩)
      · subst he
        icases keep_pure (Q := wdbW K tx X2.v w2)
            (P := wdbOK w2 ∧ w2.ms = some (X2.v.base, mapLen w2.ms) ∧ X2.v = View.ofC X2.v.base w2.C)
            (by unfold wdbW; iintro ⟨-, %H⟩; ipureintro; exact H) $$ Hdb with ⟨Hdb, %Hwf2⟩
        obtain ⟨C2, Dc2, s2, st3, HC2, HcL2, HI2, Hs2⟩ : ∃ C2 Dc2 s2 st3,
            X2.t.bs !! c = some C2 ∧ c ∈ X2.liveB ∧
            RInv X w B0 keys Lroot X2 w2 st3 Dc2 (upd ks key s2) ∧
            ((C2.bv.rootNode' = null ∧ s2 = .nilc) ∨
             (C2.bv.rootNode' ≠ null ∧ s2 = .val (encode C2.ib) false)) := by
          rcases Hdone.2 with ⟨hn, rfl, rfl⟩ | ⟨hn, -⟩
          · exact ⟨C, Dc, .nilc, st, HC, HcL, rinv_nil HI Htodo Hc HC hn, Or.inl ⟨hn, rfl⟩⟩
          · obtain ⟨C', D', HC', Hnn, HcL', HI'⟩ := rinv_spilled HI Hknd Hkm Htodo Hc HC hn Hdone Hwf2.2.2
            exact ⟨C', upd Dc key D', _, _, HC', HcL', HI', Or.inr ⟨Hnn, rfl⟩⟩
        try wp_auto
        wp_apply wp_slice_make2 (V := w8) $$ [] as %val ⟨Hv, Hcap⟩
        · ipureintro; decide
        ihave %Hvl := ownSlice_len _ _ _ $$ Hv
        ihave %Hvp := ownSlice_ptr_pos _ _ _ (by simp) $$ Hv
        icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hvp $$ Hv
          with ⟨Hbytes, Hback⟩
        rw [flatMap_encode_w8, show (zero_val w8 : w8) = 0 from rfl]
        have hvlen : sint.Z val.len = 16 :=
          internal.common.sint_Z_eq_of_sint_nat _ _ (by simpa using Hvl.1) Hvl.2
        icases (bytesPointsto_typed (V := InBucket) _ _ _ (by simp) Hvp).1 $$ Hbytes with Hh0
        simp only [hvlen, show sint.Z (W64 0) = 0 from rfl,
          show (0 : Int) ≤ 0 ∧ (0 : Int) < 16 from ⟨Int.le_refl _, by decide⟩]
        rw [show sliceIndexRef w8 0 val = val.ptr by rw [sliceIndexRef_byte _ _ Hvp (Int.le_refl _)]; simp]
        icases wtxW_bkt_acc K tx r m X2 c C2 HC2 $$ Hw with ⟨Ho, Hwb2⟩
        rw [decide_eq_true HcL2]
        unfold objOwn
        icases Ho with ⟨G1, G2, G3, G4, G5, G6, G7, G8, G9, G10⟩
        try wp_auto
        icases (typedPointsto_bytes (V := InBucket) _ _ _ Hvp).1 $$ Hh0 with Hh0
        ihave Hval := Hback $$ %(encode C2.ib) [] [Hh0]
        · ipureintro; simp [ByteEncoding.encode_length]
        · rw [flatMap_encode_w8]; iexact Hh0
        ihave Hw := Hwb2 $$ [G1 G2 G3 G4 G5 G6 G7 G8 G9 G10]
        · dsimp only; iframe
        rcases Hs2 with ⟨Hn2, rfl⟩ | ⟨Hn2, rfl⟩
        · rw [decide_eq_true Hn2]
          try wp_auto
          obtain ⟨Br, HBr, Hbk', Hbm'⟩ := HI2.root
          icases wtxW_bm_acc K tx r m X2 X.rl Br HBr B0.bv.buckets' B0.bm Hbk' Hbm' $$ Hw
            with ⟨Hbm, Hwb⟩
          unfold forMapPostcondition
          ileft
          isplitr
          · ipureintro; rfl
          iexists B0.bm
          iframe Hbm
          isplitr
          · ipureintro; rfl
          iframe
          iexists st3, Lroot, Dc2, upd ks key .nilc
          iframe
          ipureintro
          exact ⟨HI2, ksAt_step Hknd Hks Hkey .nilc ⟨(fun h => nomatch h), (fun v h => nomatch h)⟩⟩
        · rw [decide_eq_false Hn2]
          try wp_auto
          obtain ⟨Br, HBr, -, -⟩ := HI2.root
          icases wtxW_cursor_acc K tx r m X2 X.rl Br HBr $$ Hw with ⟨-, -, Hst, %dt, Htx, Hwbc⟩
          wp_apply hCur K tx r m 1 X.rl dt $$ [Hst Htx] as %cur ⟨%stk, Hcu, Hs, Hscap, Hst, Htx⟩
          · iframe; iframe #
          ihave Hw := Hwbc $$ Hst Htx
          try wp_auto
          wp_apply wp_string_to_bytes key as %ksl ⟨Hksl, Hkcap⟩
          imod ownSlice_persist ksl _ _ $$ Hksl with #Hksl
          have HlocR : bktLocalOK X2 X.rl := HI2.rootOK.1
          wp_apply hSeek K tx r m X2 X.rl cur stk [] ksl key (KeyR.heap DFrac.discard) HlocR
            (pmFresh_of_spG HI2.G) $$ [Hw Hcu Hs Hscap]
            as %k %vl %fl ⟨%stk', %els, %pids, Hw, Hcu, Hs, Hscap, Hkey, %Hrt, Hkv⟩
          · iframe; unfold keyR; iexact Hksl
          obtain ⟨Hp, Hr⟩ := Hrt
          obtain ⟨p, ws, ⟨j, hpj⟩, hL, hle⟩ := WOpen.lPath_leaf X2 X.rl Br HBr HlocR els pids Hp
          have hpI := WOpen.lPath_posI X2 X.rl Br HBr HlocR els pids Hp j p hpj
          have hfa := WOpen.route_found_at X2 X.rl els pids key HlocR Hp Hr
          obtain ⟨we, hwe, hwk, hwf⟩ := rinv_entry Hpre Hreach Hfv HB0 HI2 Hc
          have hw := hfa we hwe hwk
          rw [hle] at hw
          rw [hle, hw]
          icases Hkv with ⟨%Hkw, #Hks, #Hvs⟩
          have hwm : we ∈ ws := List.mem_of_getElem? hw
          obtain ⟨hlk, hlv⟩ := WOpen.leaf_live X2 X.rl Br HBr HlocR p hpI ws hL we hwm
          try wp_auto
          wp_apply wp_string_to_bytes key as %ksl2 ⟨Hksl2, -⟩
          icases wtxW_cells_acc K tx r m X2 $$ Hw with ⟨%Hbase, Hcells, Hwbc⟩
          icases viewCells_src_acc wq X2.v Hbase k _ we.key
            (WOpen.leafSrc_live X2 X.rl Br HBr HlocR _ hlk) $$ [Hcells] with ⟨%dk, Hkk, Hcb⟩
          · iframe; iframe #
          wp_apply hEq ksl2 k (DFrac.own 1) dk key we.key $$ [Hksl2 Hkk] as ⟨-, Hkk⟩
          · iframe
          ihave Hcells := Hcb $$ Hkk
          ihave Hw := Hwbc $$ Hcells
          rw [decide_eq_true hwk.symm]
          try wp_auto
          have hbf : ¬ (fl &&& W32 1 = W32 0) := by rw [Hkw.2]; exact hwf
          rw [decide_eq_false hbf]
          try wp_auto
          wp_apply wp_string_to_bytes key as %ok ⟨Hok, -⟩
          imod ownSlice_persist ok _ _ $$ Hok with #Hok
          wp_apply wp_string_to_bytes key as %nk ⟨Hnk, -⟩
          imod ownSlice_persist nk _ _ $$ Hnk with #Hnk
          imod ownSlice_persist val _ _ $$ Hval with #Hval
          try wp_auto
          icases wtxW_nodes_nonnull K tx r m X2 X.rl Br HBr $$ Hw with ⟨Hw, %Hnn⟩
          obtain ⟨Hroot0, Hvwf, Hpready⟩ := rinv_ready Hpre HB0 HI2 HBr Hp
          icases wtxW_matReady_all K tx r m X2 Br pids Hroot0 Hvwf Hpready $$ Hw with ⟨Hw, %Hmr⟩
          wp_apply hNode K tx r m X2 X.rl Br cur stk' els pids (DFrac.own 1) HBr HlocR Hp Hnn Hmr
            $$ [Hw Hcu Hs] as %l ⟨%X3, Hw, Hcu, Hs, %Hcn⟩
          · iframe
          obtain ⟨Hmg, -, HlocR', B3, pid, HB3, Hlast, Hres⟩ := Hcn
          obtain ⟨rl, Hrl, Hll, Hrlb, Hcap, Hsrt, Hwl, Hmk, Hv3, Hpar, Hkl, -⟩ :=
            rinv_putPre HI2 Hmg Hp Hr HB3 Hlast Hres ⟨we, hwe, hwk⟩
          icases wtxW_open K tx r m X3 $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hclose⟩
          ihave %Hok3 := wtxHeap_heapOK tx (DFrac.own 1) X3 $$ Hh
          have Htx3 : B3.bv.tx' = tx := (Hok3.2.2.1 X.rl B3 HB3).1
          have HlB3 : X.rl ∈ X3.liveB := HlocR'.1
          icases wtxHeap_setNode_acc tx (DFrac.own 1) X3 X.rl B3 l rl HB3 Hrl $$ Hh
            with ⟨Hno, Hbo, Hf, Hrf, Hback⟩
          rw [decide_eq_true Hll, decide_eq_true HlB3]
          isimp only [objOwn] at Hbo
          icases Hbo with ⟨Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10⟩
          have Hroot1 : X.rl = B3.bv.tx'.[Tx, go!"root"] := by
            rw [Htx3]; exact Hok.1
          rw [if_pos Hroot1, Htx3]
          unfold txFields
          icases Hf with ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩
          have Hbase3 : 0 < X3.v.base.addr := by rw [Hv3]; exact Hbase
          wp_apply hPut X3.v l X.rl rl tx X3.t.t.meta' X3.t.mv (DFrac.own 1) (DFrac.own 1) wq ok nk val key key
              (encode C2.ib) (Src.own DFrac.discard) (Src.own DFrac.discard) (Src.own DFrac.discard)
              (W64 0) (W32 1) Hrlb Hcap Hsrt Hwl (by simpa using Hmk) Hkl Hkl (by intro h; cases h)
              (by intro h; cases h) (by intro h; cases h) Hbase3
            $$ [Hno Hv Q2 Hmeta Hmv] as ⟨%sl, %ins', Hno, Hv, Q2, Hmeta, Hmv⟩
          · iframe; iframe #; unfold srcOwn; iframe #
          try wp_auto
          icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn5, Hins5, Hcap5, Hws5, Hch5, Hchcap5, Hkey5⟩
          ihave %Hinsl := BigSepL2.bigSepL2_length $$ Hws5
          ihave Hno := (objOwn_live_node _ l (DFrac.own 1) X.rl _).2
            $$ [Hn5 Hins5 Hcap5 Hws5 Hch5 Hchcap5 Hkey5]
          · iframe
          ihave Hh := Hback $$ %(rl.withEnts sl ins' (wsPutAt rl.ws key
              ⟨W32 1, W64 0, key, encode C2.ib, Src.own DFrac.discard, Src.own DFrac.discard⟩))
            %(by simpa [NRec.withEnts] using Hpar) [Hno] [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10]
            [Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs] Hrf
          · iexact Hno
          · isimp only [objOwn]
            rw [if_pos Hroot1, Htx3]
            iframe
          · iframe
          ihave Hw := Hclose $$ %(X3.setNode X.rl l (rl.withEnts sl ins'
              (wsPutAt rl.ws key ⟨W32 1, W64 0, key, encode C2.ib, Src.own DFrac.discard, Src.own DFrac.discard⟩))) [] Hh Hv Hst
          · ipureintro; rw [setNode_eq X3 X.rl l B3 _ HB3]; exact ⟨rfl, rfl, rfl⟩
          have HI4 := rinv_put HI2 (upd_same ks key _) Hc Hmg Hp Hr HB3 Hlast Hres Hrl sl ins' Hinsl
            ⟨we, hwe, hwk, hwf⟩
          rw [upd_upd, show rootEnt key (encode C2.ib) = ⟨W32 1, W64 0, key, encode C2.ib, Src.own DFrac.discard, Src.own DFrac.discard⟩ from rfl] at HI4
          obtain ⟨Br4, HBr4, Hbk4, Hbm4⟩ := HI4.root
          icases wtxW_bm_acc K tx r m _ X.rl Br4 HBr4 B0.bv.buckets' B0.bm Hbk4 Hbm4 $$ Hw
            with ⟨Hbm, Hwb⟩
          have Hv4 : (X3.setNode X.rl l (rl.withEnts sl ins'
              (wsPutAt rl.ws key ⟨W32 1, W64 0, key, encode C2.ib, Src.own DFrac.discard, Src.own DFrac.discard⟩))).v = X2.v := by
            rw [setNode_eq X3 X.rl l B3 _ HB3]; exact Hv3
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists B0.bm
          iframe Hbm
          isplitr
          · ipureintro; rfl
          iframe
          iexists w2, st3, Lroot, Dc2, upd ks key (.val (encode C2.ib) true)
          rw [Hv4]
          iframe
          ipureintro
          exact ⟨HI4, ksAt_step Hknd Hks Hkey _ ⟨(fun h => nomatch h), (fun v h => nomatch h)⟩⟩
      · cases err with
        | nil => exact absurd rfl hne
        | ok ii =>
        try wp_auto
        unfold forMapPostcondition
        iright; iright; iright
        iexists #()
        isplitr
        · ipureintro; rfl
        dsimp only
        wp_auto
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
          exact errFacts_of_spErr (spErr_trans (rinv_spErr HI) Hst2) (by rw [HB0]; rfl)
        iexact Hcase
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
    icases wdbW_ofC K tx X1.v w1 $$ Hdb with ⟨Hdb, %HvC⟩
    obtain ⟨Hok1, Hsb1⟩ := rinv_end_nil Hpre Hreach Hfv HB0 Hkset HI Hks HB Hnull HvC Htx
    have HG := HI.G
    iapply HΦ
    unfold spillPost
    ileft
    isplitr
    · ipureintro; rfl
    iexists X1, w1
    iframe
    ipureintro
    exact ⟨Hok1, HI.C, HG.2.2.1, HG.2.2.2.1, HG.2.2.2.2.1, HG.2.1, Hsb1, HI.tt, Hrl,
      by rw [Hrl, HB]; rfl, HI.mvEq,
      end_nil_notPend Hpre Hreach Hfv HB0 Hkset HI Hks HB Hnull HvC, markCov_grow Hmc HI.grow,
      bufSlots_src HI.src HsOK.2.1⟩
  rw [decide_eq_false Hnull]
  try wp_auto
  ihave Hh := Hhb $$ [Hib Htx Hbk Hpg Hrn Hnd Hibv Hnm Hbm Hpo]
  · dsimp only; iframe
  ihave Hw := Hclose $$ %X1 [] Hh Hv Hst
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  icases wdbW_ofC K tx X1.v w1 $$ Hdb with ⟨Hdb, %HvC⟩
  obtain ⟨rn, h, F, D, N, E, Hun, Hsp, Hfin⟩ :=
    rinv_end Hpre Hreach Hfv HB0 Hkset HI Hks HB Hnull HvC Htx
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
    rcases Hc with ⟨Hsp1, -, -⟩ | ⟨-, T, D', Hfr, -, Hsi', HD1, HD2, -, -, rt, rr, S, h', Hrt, Hrtl,
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
    have hbtx : B1.bv.tx' = tx := (Hok2.2.2.1 X.rl B1 HB1).1
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
      refine ⟨?_, fun _ _ => rfl, ⟨rfl, rfl⟩, ?_⟩
      · intro l hl; rw [List.mem_singleton.1 hl]; exact Hrr
      · intro l hl; rw [List.mem_singleton.1 hl, Hrpar]; exact Ne.symm Hrt0
    · iapply BigSepL.bigSepL_singleton.2; rw [decide_eq_true Hrtl]; iexact Hn
    · dsimp only [bkRooted]
      iframe
    · iframe
    ihave Hw := Hclose $$ %(X2.setBkt X.rl (bkRooted B1 rt rr.nv.pgid')) [] Hh Hv Hst
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    try wp_auto
    obtain ⟨Hok', Hsb'⟩ := Hfin X2 w2 st2 B1 rt rr Hdone' HB1 Hrr Hrtl Hrsp Hrpar Hroot
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
    have Hrl2 : X2.rl = X.rl := Hfr.1.trans Hrl
    have Hcp2 : w.C.pages = X2.v.pages := by
      rw [s3, ← HI.C]
      have := congrArg View.pages HvC; simpa [View.ofC] using this.symm
    refine ⟨Hok', s1.trans HI.C, HG'.2.2.1, HG'.2.2.2.1, HG'.2.2.2.2.1, s5, Hsb',
      Hfr.2.2.2.2.2.2.1.trans HI.tt, Hrl2, ?_,
      mv_trans HI.mvEq (Hfr.2.2.2.2.2.2.2.1 : X2.t.mv = { X1.t.mv with pgid' := X2.t.mv.pgid' }),
      root_notPend Hrl2 Hcp2 HsT HD' Hsi', markCov_grow Hmc (markGrow_trans HI.grow s8.2.2.1),
      bufSlots_src (X := X2.setBkt X.rl (bkRooted B1 rt rr.nv.pgid'))
        (bufSrc_grow HI.src s8.2.2.2 (fun y hy => by
          rw [HI.fl] at hy; exact applySteps_free_sub st w.fl w.wtxid y hy) HI.mark) HsOK.2.1⟩
    show ((X2.t.bs.insert X.rl (bkRooted B1 rt rr.nv.pgid')) !! X2.rl).isSome
    rw [Hrl2, GMap.lookup_insert]; rfl
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
      exact errFacts_of_spErr (spErr_trans (rinv_spErr HI) Hst2) (by rw [HB0]; rfl)
    iexact Hcase

end proof
end Spill
end bbolt
end EtcdGrove
end Perennial
