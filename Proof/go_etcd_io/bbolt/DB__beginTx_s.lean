/-
The proof of `Spec/go_etcd_io/bbolt/DB__beginTx_s.lean` (U5, `notes/bbolt-proof-plan.md`): a read
transaction on the writer side's spare pair, under `metalock` and `mmaplock`'s read lock: the
meta copied (`Tx.init`, the meta cells borrowed), the reader registered in the freelist, the
store (`store_register`) and the transactions (`txs_register'`).
-/
module

public import Spec.go_etcd_io.bbolt.DB__beginTx_s
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__AddReadonlyTXID
public import Proof.go_etcd_io.bbolt.Txn.Init
public import Proof.go_etcd_io.bbolt.Txn.Txs
public import Proof.go_etcd_io.bbolt.Txn.RdReg
public import Proof.go_etcd_io.bbolt.Txn.RdInit
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

private instance BC_core_persistent_b (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

theorem DB.beginTx_s.wp_proof (wp_meta : DB.meta.spec (GF := GF) (hG := hG))
    (wp_Copy : internal.common.Meta.Copy.spec (GF := GF) (hG := hG))
    (wp_RootBucket : internal.common.Meta.RootBucket.spec (GF := GF) (hG := hG))
    (wp_IncTxid : internal.common.Meta.IncTxid.spec (GF := GF) (hG := hG))
    (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (wp_AddRO : internal.freelist.Interface.AddReadonlyTXID.spec (GF := GF) (hG := hG)) :
    DB.beginTx_s.spec (GF := GF) (hG := hG) := by
  intro K C b l hok htree
  wp_start as ⟨#Hcore, Hpair, Hcur, Hmap, Hop⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, #Hpkg, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  iunfold rdPair at Hpair
  icases Hpair with ⟨Hmtok, Hstok⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hsync $Hml] as ⟨Hlk, HR⟩
  wp_apply sync.RWMutex.wp_RLock $$ [$Hsync $Hmtok] as ⟨Hrl, HP⟩
  iunfold metaR at HR
  icases HR with ⟨%C', %F, %cl, %fli, %wa, Hcur', Hst', Hcls, Hop', Hfl', Hwa, Hob, Hmlk, Hfa, Hro, %Hok, %HF⟩
  iunfold Pm at HP
  icases HP with ⟨%ms, Hmap', Hmf, Hmt⟩
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  subst hC
  icombine Hop Hop' gives %hcl
  have hcl' : cl = false := by simpa using hcl.symm
  subst hcl'
  obtain ⟨-, -, htx1⟩ := Hok rfl
  icombine Hmap Hmap' gives % ⟨_, hms⟩
  subst hms
  iunfold mapFields at Hmf
  icases Hmf with ⟨Hdr, Hd, Hm0, Hm1, %Hb⟩
  have hbn : b ≠ Loc.null := fun e => by subst e; exact absurd Hb.2.1 (Int.lt_irrefl 0)
  wp_auto
  rw [decide_eq_false hbn]
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Htx, %Htxn⟩
  iStructNamed Htx
  -- the meta cells, borrowed for `Tx.init`
  ihave ⟨Hmt, Hmt2⟩ := (ghostVar_split_half K.B.mtok sync.rfrac ()).1 $$ Hmt
  imod meta_borrow K.B K.N K.p ⊤ CoPset.subseteq_top C (some (b, l)) $$ [Hpi Hmlk Hmt2 Hcur' Hmap']
    with ⟨Hmc, Hmln, Hcur', Hmap'⟩
  · iframe; iframe #
  ihave Hmf : mapFields K.db (DFrac.own sync.rfrac.half) (some (b, l) : MapSt) $$ [Hdr Hd Hm0 Hm1]
  · simp only [mapFields]; iframe; ipureintro; exact Hb
  wp_apply wp_Tx_init wp_meta wp_Copy wp_RootBucket wp_IncTxid «$r0_ptr» K.db b l C _ _ false _ _ _ _ hok
    $$ [writable db meta' root pages Hmf Hmc] as %m %ibp %bm %nm %pm ⟨Hw, Hdb, Hme, Hrt, Hpg, Hmv, Hib, Hmaps, Hmf, Hmc⟩
  · iframe
  imod meta_return K.B K.N K.p ⊤ CoPset.subseteq_top C (some (b, l)) $$ [Hpi Hmc Hmln Hcur' Hmap']
    with ⟨Hmlk, Hmt2, Hcur', Hmap'⟩
  · iframe; iframe #
  ihave Hmt := (ghostVar_split_half K.B.mtok sync.rfrac ()).2 $$ [Hmt Hmt2]
  · iframe
  -- the reader's key, its txid in `metaR`, its view in the store
  have hC63 : C.txid < 2 ^ 63 := htree.2.2.2.2.2
  have hmvtx : (metaOf (C.slot C.txid)).txid'.toNat = C.txid := hok.2.2.2.2.2.2.1.1
  have htid : (metaOf (C.slot C.txid)).txid' = W64 (C.txid : Int) := by
    apply BitVec.eq_of_toNat_eq; rw [hmvtx]; simp; omega
  obtain ⟨k, hk⟩ := gmap_nat_fresh F
  imod (ghost_map_insert k (W64 (C.txid : Int)) hk) $$ Hfa with ⟨Hfa, Hfk⟩
  imod store_pages_bound K.B K.N K.p ⊤ CoPset.subseteq_top C b l _ $$ [Hpi Hcur' Hmap']
    with ⟨Hcur', Hmap', %Hpgb⟩
  · iframe; iframe #
  imod store_register K.B K.N K.p ⊤ CoPset.subseteq_top C b l k $$ [Hpi Hcur' Hmap' Hmt Hfk]
    with ⟨Hcur', Hmap', Hrds, Hvc⟩
  · iframe; iframe #
  -- the transaction's names and its registration
  imod rd_names_alloc (GF := GF)
    ((false, (View.ofC b C).data, (View.ofC b C).data, ∅) : TxViewC)
    (TxX.rd (View.ofC b C) (metaOf (C.slot C.txid)) k) (View.ofC b C)
    with ⟨%n, Hv, Hex, Hrbk, Hdone, #Hvw⟩
  ihave ⟨Hv1, Hv2⟩ := (ghostVar_split_half n.v 1 _).1 $$ Hv
  ihave ⟨Hd1, Hd2⟩ := (ghostVar_split_half n.done 1 false).1 $$ Hdone
  imod txs_register K.B K.N K.p K.sp K.t0 ⊤ CoPset.subseteq_top «$r0_ptr»
    ⟨K.db, n, false, .spare⟩ _ $$ [Hti Hdb stats Hv1 Hd1 Hd2 Hrl Hstok Hrds Hrbk]
    with ⟨#Hreg, Hdb⟩
  · iframe Hti Hdb stats Hd2
    isplitl [Hv1 Hd1 Hrl Hstok Hrds]
    · iunfold txExcl
      iexists _, (TxX.rd (View.ofC b C) (metaOf (C.slot C.txid)) k)
      iframe Hv1 Hd1
      simp only [reduceCtorEq, ↓reduceIte]
      iframe
    · iunfold readerHandles
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists ∅; iexact Hrbk
  simp only [initMeta, Bool.false_eq_true, ↓reduceIte]
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave #Hpkf : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist $$ []
  · iPkgInit
  -- `AddReadonlyTXID`, if there is a freelist
  iunfold flRoOpt at Hro
  cases fli
  -- a freelist: `AddReadonlyTXID`
  rename_i i
  simp only [reduceCtorEq, ↓reduceIte]
  icases Hro with ⟨%ro, Hro, %Hperm⟩
  generalize hmvv : metaOf (C.slot C.txid) = mv at htid ⊢
  wp_auto
  wp_apply wp_Txid $$ [Hmv] as Hmv
  · iframe
  wp_apply wp_AddRO (GoInterface.ok i) ro _ $$ [Hro] as Hro
  · iframe
  ihave Hro : flRoOpt (GoInterface.ok i) (<[k := W64 (C.txid : Int)]> F) $$ [Hro]
  · iunfold flRoOpt; simp only [reduceCtorEq, ↓reduceIte]
    iexists _; iframe Hro; ipureintro; rw [htid]; exact ro_insert_perm F k _ ro hk Hperm
  subst hmvv
  rotate_left
  -- no freelist
  simp only [↓reduceIte]
  wp_auto
  ihave Hro : flRoOpt GoInterface.nil (<[k := W64 (C.txid : Int)]> F) $$ []
  · iunfold flRoOpt; simp only [↓reduceIte]; itrivial
  all_goals
    icases Hmaps with %Hnull
    obtain ⟨rfl, rfl, rfl⟩ := Hnull
    imod rdTxK_intro K «$r0_ptr» .spare n C b l k m ibp hok htree Htxn Hpgb
      $$ [Hreg Hpkg Hcore Hv2 Hex Hw managed Hme Hrt Hpg commitHandlers WriteFlag Hdb Hmv Hib
        Hvc Hmap' Hmf Hvw] with Hrd
    · iframe; iframe #
      simp only [reduceCtorEq, ↓reduceIte]; itrivial
    wp_apply sync.Mutex.wp_Unlock _ (metaR K.B K.db K.p) $$ [$Hsync $Hml $Hlk Hcur' Hst' Hcls Hop' Hfl' Hwa Hob Hmlk Hfa Hro]
    · iunfold metaR
      iexists C, _, false, _, wa
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      ipureintro
      refine ⟨fun _ => ⟨hok, htree, htx1⟩, ?_⟩
      intro k' t h'
      by_cases hkk : k = k'
      · subst hkk
        rw [GMap.lookup_insert] at h'
        cases h'
        rw [toNat_W64_of_lt C.txid (by omega)]
        omega
      · rw [GMap.lookup_insert_ne _ _ hkk] at h'
        exact HF k' t h'
    -- the statistics
    iunfold dbFixed at Hfix
    icases Hfix with ⟨-, #Hsp, -⟩
    wp_auto
    by_cases hsp : K.sp = null
    rw [decide_eq_true hsp]
    wp_auto
    rotate_left
    rw [decide_eq_false hsp]
    wp_auto
    wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hsync $Hsl] as ⟨Hsw, HPs⟩
    iunfold Ps at HPs
    simp only [hsp, ↓reduceIte]
    icases HPs with ⟨%st, Hs⟩
    wp_auto
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hsw Hs]
    · iunfold Ps; simp only [hsp, ↓reduceIte]; iexists _; iexact Hs
    all_goals
      iapply HΦ
      iframe
      ipureintro; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
