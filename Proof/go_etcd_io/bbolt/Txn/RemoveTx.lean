/-
`DB.removeTx` (U5 of `notes/bbolt-proof-plan.md`; design §3.11, "Reader end"): a reader's
registry entry in the store and its txid in `metaR` removed, its `mmaplock` share back as a reader
token, the transaction done (`txs_close`) and its statistics merged into the database's.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Txn.RdReg
public import Proof.go_etcd_io.bbolt.Txn.StatsAdd
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__RemoveReadonlyTXID
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

private instance BC_core_persistent_rm (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

/-- **`db.removeTx(tx)`** of a reader `tx` whose exclusive part was taken out (`txExcl_take`):
its read lock and registry key (`k`, the view `v`), its view's cells and mapping share, its
`statlock` token and the exclusive part's `done` half, its meta copy. Its `mmaplock` reader token
comes back, the transaction is done (`txDone`, its `done` half `true`) and the invariant's quarter
of `tx.db` comes out. -/
theorem wp_removeTx (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (wp_RemoveRO : internal.freelist.Interface.RemoveReadonlyTXID.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (v : View) (mv : Meta) (k : Nat) (m : Loc) (l : Nat)
    (hdb : r.db = K.db) (htxid : mv.txid'.toNat = v.txid) :
    {{ K.core (GF := GF) ∗ reg tx K.B r ∗
        sync.ownRWMutexRLocked K.db.[DB, go!"mmaplock"] (Pm K.B K.db) ∗
        ghostVar K.B.map sync.rfrac.half.half (some (v.base, l) : MapSt) ∗
        mapFields K.db (DFrac.own sync.rfrac.half) (some (v.base, l) : MapSt) ∗
        k ↪[K.B.rds] (⟨v⟩ : RdInfo) ∗ viewCells rq v ∗
        sync.ownRWMutex K.db.[DB, go!"statlock"] (Ps K.sp) ∗
        ghostVar r.n.done (1 : Qp).half false ∗ tx.[Tx, go!"meta"] ↦ m ∗ m ↦ mv ∗
        (if r.src = .loan then emp else ghostVar K.B.spr (1 : Qp).half (some k)) }}
      (App (Val (K.db @!! go.GoType.PointerType DB.ty @!! go!"removeTx")) (Val #tx))
    {{ RET #(); sync.ownRWMutex K.db.[DB, go!"mmaplock"] (Pm K.B K.db) ∗
        sync.ownRWMutex K.db.[DB, go!"statlock"] (Ps K.sp) ∗ tx.[Tx, go!"meta"] ↦ m ∗ m ↦ mv ∗
        tx.[Tx, go!"db"] ↦{DFrac.own (1 : Qp).half.half} r.db ∗
        ghostVar r.n.done (1 : Qp).half true ∗ txDoneDef tx ∗
        (if r.src = .loan then emp else spareTok K.B) }} := by
  wp_start as ⟨#Hcore, #Hreg, Hrl, Hmap, Hmf, Hrds, Hvc, Hstok, Hd, Hme, Hmv, Hsp⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, #Hpkg, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave #Hpkf : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist $$ []
  · iPkgInit
  -- the transaction done: the statistics persisted, the quarter of `tx.db` out
  imod txs_close K.B K.N K.p K.sp K.t0 ⊤ CoPset.subseteq_top tx r $$ [Hti Hreg Hd]
    with ⟨Hdb4, ⟨%s, #Hst⟩, Hd⟩
  · iframe; iframe #
  -- the store's registry entry, then the read lock
  imod store_deregister K.B K.N K.p ⊤ CoPset.subseteq_top k ⟨v⟩ $$ [Hpi Hrds Hvc]
    with ⟨Hmt, Hfk⟩
  · iframe; iframe #
  wp_auto
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hsync $Hrl Hmap Hmf Hmt] as Hmtok
  · iunfold Pm; iexists _; iframe
  wp_apply sync.Mutex.wp_Lock $$ [$Hsync $Hml] as ⟨Hlk, HR⟩
  iunfold metaR at HR
  icases HR with ⟨%C, %F, %cl, %fli, %wa, Hcur, Hst', Hcls, Hop, Hfl, Hwa, Hob, Hmlk, Hfa, Hro,
    %Hok, %HF⟩
  iunfold fltxAuth at Hfa
  icases Hfa with ⟨Hfa, %o, Ho, Hcl⟩
  ihave %hk := ghost_map_lookup $$ Hfa Hfk
  -- batch 41: the spare state (the spare reader's: reset, `store_spr_reset`), its clause kept
  ihave Hspr : |={⊤}=> (∃ o' : Option Nat, ghostVar K.B.spr (1 : Qp).half.half o' ∗
      (opnShot K.B ∨ ⌜sprCl o' (GMap.delete k F)⌝)) ∗
      (if r.src = .loan then emp else spareTok K.B) ∗ k ↪[K.B.fltx] (W64 (v.txid : Int))
      $$ [Ho Hcl Hsp Hfk]
  · cases hs : r.src
    · simp only [↓reduceIte]
      imodintro
      iframe Hfk
      iexists o
      iframe Ho
      icases Hcl with (#Hshot | %hcl)
      · ileft; iexact Hshot
      · iright; ipureintro
        intro k' x hx
        rw [GMap.lookup_delete_iff] at hx
        split at hx
        · cases hx
        · exact hcl k' x hx
    · simp only [reduceCtorEq, ↓reduceIte]
      imod store_spr_reset K.B K.N K.p ⊤ CoPset.subseteq_top k _ o $$ [Hpi Hsp Ho Hfk]
        with ⟨Htok, Ho, Hfk, %ho⟩
      · iframe; iframe #
      imodintro
      iframe Htok Hfk
      iexists none
      iframe Ho
      icases Hcl with (#Hshot | %hcl)
      · ileft; iexact Hshot
      · iright; ipureintro
        intro k' x hx
        rw [GMap.lookup_delete_iff] at hx
        split at hx
        · cases hx
        · rename_i hne
          have := hcl k' x hx
          rw [ho] at this
          cases this
          exact absurd rfl hne
  imod Hspr with ⟨Hspr, Htok, Hfk⟩
  imod ghost_map_delete $$ Hfa Hfk with Hfa
  have hmv : mv.txid' = W64 (v.txid : Int) := by
    apply BitVec.eq_of_toNat_eq; rw [htxid]; simp; have := htxid ▸ BitVec.isLt mv.txid'; omega
  iunfold flRoOpt at Hro
  cases fli
  -- a freelist: `RemoveReadonlyTXID`
  rename_i i
  simp only [reduceCtorEq, ↓reduceIte]
  icases Hro with ⟨%ro, Hro, %Hperm⟩
  wp_auto
  wp_apply wp_Txid $$ [Hmv] as Hmv
  · iframe
  wp_apply wp_RemoveRO (GoInterface.ok i) ro _ $$ [Hro] as ⟨%ro', Hro, %Hperm'⟩
  · iframe
  ihave Hro : flRoOpt (GoInterface.ok i) (GMap.delete k F) $$ [Hro]
  · iunfold flRoOpt; simp only [reduceCtorEq, ↓reduceIte]
    iexists _; iframe Hro; ipureintro
    rw [hmv] at Hperm'
    exact ro_delete_perm F k _ ro ro' hk Hperm Hperm'
  rotate_left
  -- no freelist
  simp only [↓reduceIte]
  wp_auto
  ihave Hro : flRoOpt GoInterface.nil (GMap.delete k F) $$ []
  · iunfold flRoOpt; simp only [↓reduceIte]; itrivial
  all_goals
    wp_apply sync.Mutex.wp_Unlock _ (metaR K.B K.db K.p) $$ [$Hsync $Hml $Hlk Hcur Hst' Hcls Hop Hfl Hwa Hob Hmlk Hfa Hspr Hro]
    · iunfold metaR
      iexists C, _, cl, _, wa
      iunfold fltxAuth
      iframe
      ipureintro
      refine ⟨Hok, ?_⟩
      intro k' t h'
      by_cases hkk : k = k'
      · subst hkk; rw [GMap.lookup_delete] at h'; cases h'
      · rw [GMap.lookup_delete_iff] at h'; simp only [hkk, ↓reduceIte] at h'; exact HF k' t h'
    iunfold dbFixed at Hfix
    icases Hfix with ⟨-, #Hsp, -⟩
    wp_auto
    by_cases hsp : K.sp = null
    · rw [decide_eq_true hsp]
      wp_auto
      iapply HΦ
      iframe
      iunfold txDoneDef; iexists s; iexact Hst
    · rw [decide_eq_false hsp]
      wp_auto
      wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hsync $Hsl] as ⟨Hsw, HPs⟩
      iunfold Ps at HPs
      simp only [hsp, ↓reduceIte]
      icases HPs with ⟨%st, Hs⟩
      wp_auto
      icases typedPointsto_not_null_dup _ _ _ $$ Hs with ⟨Hs, %Hspn⟩
      iStructNamed Hs
      wp_apply wp_TxStats_add _ _ _ _ DFrac.discard $$ [TxStats Hst] as ⟨⟨%ts, Hts⟩, -⟩
      · iframe; iframe #
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hsw Hts FreePageN PendingPageN FreeAlloc
        FreelistInuse TxN OpenTxN]
      · iunfold Ps; simp only [hsp, ↓reduceIte]
        iexists ({ st with TxStats' := ts, OpenTxN' := st.OpenTxN' - W64 1 } : Stats)
        iapply typedPointsto_combine _ _ _ Hspn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      iapply HΦ
      iframe
      iunfold txDoneDef; iexists s; iexact Hst

end proof

end bbolt
end EtcdGrove
end Perennial
