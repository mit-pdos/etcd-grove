/-
`DB.beginRWTx` (bbolt, internal to U5 of `notes/bbolt-proof-plan.md`; design §3.11 "Writer begin"):
`rwlock` (the writer side idle, `rwR`), `metalock` (deferred unlock), the errors (closed:
`ErrDatabaseNotOpen`; unmapped after a failed remap: `ErrInvalidMapping`), `Tx.init` on the
committed state's metas, `db.rwtx = t`, `ReleasePendingPages` (`store_release`), then the store's
writer state begins (`store_wbegin`) and the transaction is registered with its exclusive part.
-/
module

public import Spec.go_etcd_io.bbolt.DB__beginTx_s
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__ReleasePendingPages
public import Proof.go_etcd_io.bbolt.Txn.Init
public import Proof.go_etcd_io.bbolt.Txn.Txs
public import Proof.go_etcd_io.bbolt.Txn.WInitH
public import Proof.go_etcd_io.bbolt.Txn.WRelease
public import Proof.go_etcd_io.bbolt.Txn.Begin
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.beginRWTx()`**: a write transaction at the committed data `D` (`TxView.wr D`), of `db`
(`txDBDef`); or an error (`beginErr`). -/
abbrev DB.beginRWTx.spec : Prop :=
  ∀ (K : BC),
  {{ K.full (GF := GF) }}
    (App (Val (K.db @!! go.GoType.PointerType DB.ty @!! go!"beginRWTx")) (Val #()))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err);
      (⌜err = interface.nil⌝ ∗ txDBDef K.B K.N tx K.db ∗ ∃ D : Data,
        boltTxDef K.B K.N tx 1 (TxView.wr D)) ∨ beginErr err }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit [GooseExts] in
private theorem mem_pendSlots_rw (fl : FLPg) (s : Nat) :
    s ∈ pendSlots fl ↔ ∃ t pd x, fl.pending !! t = some pd ∧ x ∈ pd.ids ∧ x.toNat = s := by
  simp only [pendSlots, FLPg.pendingIds, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨x, ⟨⟨t, pd⟩, hkv, hx⟩, rfl⟩
    exact ⟨t, pd, x, (GMap.mem_toList _ _ _).1 hkv, hx, rfl⟩
  · rintro ⟨t, pd, x, hp, hx, rfl⟩
    exact ⟨x, ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩, rfl⟩

/-- The idle store's tree slots are not pending. -/
theorem storeOK_tree_not_pend (σ : StoreSt) (h : storeOK σ) (hw : σ.wtx = none) :
    ∀ s ∈ treeSlots σ.C, s ∉ pendSlots σ.fl := by
  obtain ⟨-, htree, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, -, -, -, hhwm⟩ := h
  intro s hs hp
  have hlt : s < 2 ^ 64 := by
    unfold treeSlots at hs
    rw [mem_pagesSlots_iff] at hs
    obtain ⟨id, pg, hpg, -, hs2⟩ := hs
    have := htree.2.2.2.1 id pg hpg
    omega
  rcases h17 s hs with h | h
  · exact h hp
  · obtain ⟨t, pd, x, hpd, hx, rfl⟩ := (mem_pendSlots_rw _ _).1 hp
    have hxe : W64 ((x.toNat : Nat) : Int) = x := by
      apply BitVec.eq_of_toNat_eq; rw [toNat_W64_of_lt _ hlt]
    have := h t pd hpd (by rw [hxe]; exact hx)
    rw [hw] at this; cases this

/-- The store's committed pages lie inside its mapping. -/
theorem storeOK_pages_bound (σ : StoreSt) (h : storeOK σ) (b : Loc) (l : Nat)
    (hms : σ.ms = some (b, l)) :
    ∀ id pg, σ.C.pages !! id = some pg → (id + 1) * 4096 ≤ l := by
  have hb := h.2.2.2.2.2.2.2.2.2.2.2.2.1 b l hms
  intro id pg hpg
  have hs : id ∈ storeSlots σ := by
    unfold storeSlots
    rw [Perennial.mem_list_dedup, List.mem_append]
    left
    unfold treeSlots
    rw [mem_pagesSlots_iff]
    exact ⟨id, pg, hpg, Nat.le_refl _, by omega⟩
  have := hb id hs
  have h4 : (id + 1) * 4096 ≤ l / 4096 * 4096 := Nat.mul_le_mul_right _ this
  exact Nat.le_trans h4 (Nat.div_mul_le_self l 4096)

omit [GooseExts] in
theorem ofC_wr (D : Data) : TxView.ofC ((true, D, D, ∅) : TxViewC) = TxView.wr D := by
  unfold TxView.ofC TxView.wr; simp

private instance BC_full_persistent_rw (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

private instance BC_core_persistent_rw (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

theorem DB.beginRWTx.wp_proof (wp_meta : DB.meta.spec (GF := GF) (hG := hG))
    (wp_Copy : internal.common.Meta.Copy.spec (GF := GF) (hG := hG))
    (wp_RootBucket : internal.common.Meta.RootBucket.spec (GF := GF) (hG := hG))
    (wp_IncTxid : internal.common.Meta.IncTxid.spec (GF := GF) (hG := hG))
    (wp_Release : internal.freelist.Interface.ReleasePendingPages.spec (GF := GF) (hG := hG)) :
    DB.beginRWTx.spec (GF := GF) (hG := hG) := by
  intro K
  wp_start as #Hfull
  ihave #Hcore : K.core $$ []
  · unfold BC.full BC.core isBoltP; icases Hfull with ⟨$, -⟩
  ihave #Hrw : sync.isMutex K.db.[DB, go!"rwlock"] (rwR K.B K.db K.p K.sp K.t0) $$ []
  · unfold BC.full isBoltP; icases Hfull with ⟨-, $, -⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, #Hpkg, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hep : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors $$ []
  · iPkgInit
  ihave #Hei : (go_etcd_io.bbolt.errors.bboltErrorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hep
  unfold go_etcd_io.bbolt.errors.bboltErrorsInit go_etcd_io.bbolt.errors.bboltErrorsVars
  icases Hei with ⟨%_, #-, %_, #H0, -, #H2, -⟩
  unfold go_etcd_io.bbolt.errors.bboltErrVar
  icases H0 with ⟨%eNO0, #HNO, -⟩
  icases H2 with ⟨%eIM0, #HIM, -⟩
  have HNOn : GoInterface.ok eNO0 ≠ GoInterface.nil := by simp
  have HIMn : GoInterface.ok eIM0 ≠ GoInterface.nil := by simp
  ihave #Hfix' := Hfix
  iunfold dbFixed at Hfix'
  icases Hfix' with ⟨#Hps, #Hsp, -, #Hro, -⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hsync $Hrw] as ⟨Hrwl, HW⟩
  wp_apply sync.Mutex.wp_Lock $$ [$Hsync $Hml] as ⟨Hlk, HR⟩
  try wp_auto
  iunfold metaR at HR
  icases HR with ⟨%C, %F, %cl, %fli, %wa, Hcur', Hst', Hcls', Hop', Hfl', Hwa', Hob, Hmlk, Hfa, Hro,
    %Hok, %HF⟩
  iunfold rwR at HW
  icases HW with (⟨%w, Hwo, %Hwok, Hcls⟩ | Hclo)
  rotate_left
  · -- closed: `ErrDatabaseNotOpen`
    iunfold closedR at Hclo
    icases Hclo with ⟨Hcls, %C2, %fl2, %ms2, Hcur2, Hst2, Hfl2, Hmap2, Hmf2, Hout2, Hwv2, Hop2,
      Hfli2, Hwa2⟩
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ (rwR K.B K.db K.p K.sp K.t0) $$ [$Hsync $Hrw $Hrwl Hcls Hcur2 Hst2
      Hfl2 Hmap2 Hmf2 Hout2 Hwv2 Hop2 Hfli2 Hwa2]
    · iunfold rwR; iright; iunfold closedR; iframe
    wp_apply sync.Mutex.wp_Unlock _ (metaR K.B K.db K.p) $$ [$Hsync $Hml $Hlk Hcur' Hst' Hcls' Hop'
      Hfl' Hwa' Hob Hmlk Hfa Hro]
    · iunfold metaR; iexists C, F, cl, fli, wa; iframe; ipureintro; exact ⟨Hok, HF⟩
    iapply HΦ
    iright
    unfold beginErr
    isplitr
    · ipureintro; exact HNOn
    ileft; iexact HNO
  -- the writer side idle
  iunfold wdbOwn at Hwo
  icases Hwo with ⟨Hcg, Hst, Hflo, Hpair, Hrcpt⟩
  iunfold wdbCore at Hcg
  iunfold wdbCoreG at Hcg
  icases Hcg with ⟨%wa2, Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hop, Hwa, Hrwtx, Hfile, Hpath,
    Hdsz, Hmf, Hosm, Hfo, Hfd, Hmc, Hmob, Hwc, Hwb, Hjunk⟩
  icombine Hcls Hcls' gives % ⟨_, hcl⟩
  subst hcl
  obtain ⟨hok, htree, htx1⟩ := Hok rfl
  icombine Hcur Hcur' gives % ⟨_, hC⟩
  subst hC
  icombine Hfli Hfl' gives %hfli
  subst hfli
  wp_auto
  rcases hms : w.ms with _ | ⟨b, l⟩
  · -- unmapped (a failed remap): `ErrInvalidMapping`
    iunfold mapFields at Hmf
    icases Hmf with ⟨Hdr, Hd, Hm0, Hm1⟩
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ (rwR K.B K.db K.p K.sp K.t0) $$ [$Hsync $Hrw $Hrwl Hcls Hcur Hgfl
      Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile Hpath Hdsz Hdr Hd Hm0 Hm1 Hosm Hfo Hfd Hmc Hmob Hwc
      Hwb Hjunk Hst Hflo Hpair Hrcpt]
    · iunfold rwR; ileft; iexists w
      unfold wdbOwn wdbCore wdbCoreG
      rw [hms]
      simp only [mapFields]
      iframe
      try (ipureintro; exact Hwok)
    wp_apply sync.Mutex.wp_Unlock _ (metaR K.B K.db K.p) $$ [$Hsync $Hml $Hlk Hcur' Hst' Hcls' Hop'
      Hfl' Hwa' Hob Hmlk Hfa Hro]
    · iunfold metaR; iexists w.C, F, false, w.fli, wa; iframe; ipureintro
      exact ⟨fun _ => ⟨hok, htree, htx1⟩, HF⟩
    iapply HΦ
    iright
    unfold beginErr
    isplitr
    · ipureintro; exact HIMn
    iright; ileft; iexact HIM
  iunfold mapFields at Hmf
  icases Hmf with ⟨Hdr, Hd, Hm0, Hm1, %Hb⟩
  have hbn : b ≠ Loc.null := fun e => by subst e; exact absurd Hb.2.1 (Int.lt_irrefl 0)
  wp_auto
  rw [decide_eq_false hbn]
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Htx, %Htxn⟩
  iStructNamed Htx
  ihave Hmf : mapFields K.db (DFrac.own (1 : Qp).half) (some (b, l) : MapSt) $$ [Hdr Hd Hm0 Hm1]
  · simp only [mapFields]; iframe; ipureintro; exact Hb
  wp_apply wp_Tx_init wp_meta wp_Copy wp_RootBucket wp_IncTxid «$r0_ptr» K.db b l w.C _ _ true _ _ _ _ hok
    $$ [writable db meta' root pages Hmf Hmc] as %m %ibp %bm %nm %pm ⟨Hw, Hdb, Hme, Hrt, Hpg, Hmv, Hib, Hmaps, Hmf, Hmc⟩
  · iframe
  icases Hmaps with ⟨Hpm, Hbm, Hnm⟩
  -- `ReleasePendingPages`
  icases (and_intro .rfl (flPgOwn_ok w.fli w.fl) : flPgOwn (GF := GF) w.fli w.fl ⊢ _ ∧ _) $$ Hflo
    with ⟨Hflo, %Hfln⟩
  iunfold flRoOpt at Hro
  simp only [Hfln, ↓reduceIte]
  icases Hro with ⟨%ro, Hrol, %Hperm⟩
  ihave #Hpkf : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Release w.fli w.fl ro $$ [Hflo Hrol] as ⟨Hflo, Hrol⟩
  · iframe
  -- the store: read idle, the pending pages released, read again, the writer's view lent
  imod store_ok_read K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl (some (b, l)) wIdle
    $$ [Hpi Hcur Hgfl Hgmap Hgwv] with ⟨Hcur, Hgfl, Hgmap, Hgwv, %Hσ⟩
  · iframe; iframe #
  obtain ⟨σ, hσC, hσfl, hσms, hσws, hσok⟩ := Hσ
  imod store_release_len K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl (some (b, l)) F ro Hperm HF
    $$ [Hpi Hcur Hgfl Hgmap Hgwv Hfa] with ⟨%S, %bs, Hcur, Hgfl, Hgmap, Hgwv, Hfa, Hso, %HS, %Hbs⟩
  · iframe; iframe #
  have hrel := wdb_release (GF := GF) K.p w σ ro S bs
    ⟨hσC, hσfl, hσms.trans hms.symm, hσws, hσok⟩ Hwok (by rw [hms]; simp) HS Hbs
  rw [hms] at hrel
  icases hrel $$ [Hwc Hwb Hso] with ⟨%Hwok', Hwc, Hwb⟩
  · iframe
  imod store_ok_read K.B K.N K.p ⊤ CoPset.subseteq_top w.C (w.fl.releasePending ro) (some (b, l))
    wIdle $$ [Hpi Hcur Hgfl Hgmap Hgwv] with ⟨Hcur, Hgfl, Hgmap, Hgwv, %Hσ2⟩
  · iframe; iframe #
  obtain ⟨σ2, h2C, h2fl, h2ms, h2ws, h2ok⟩ := Hσ2
  have h2w : σ2.wtx = none := by
    have := congrArg (fun x : WSt => x.2.1) h2ws; simpa [StoreSt.wst, wIdle] using this
  have hnp := storeOK_tree_not_pend σ2 h2ok h2w
  rw [h2C, h2fl] at hnp
  have hpgb := storeOK_pages_bound σ2 h2ok b l h2ms
  rw [h2C] at hpgb
  have hmv : mvccView (w.fl.releasePending ro) (View.ofC b w.C) := by
    have := h2ok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b; rw [h2C, h2fl] at this; exact this
  have hwf : (w.fl.releasePending ro).WF := by have := h2ok.2.2.2.1; rw [h2fl] at this; exact this
  have hbl : flBelow (w.fl.releasePending ro) w.C none := by
    have := h2ok.2.2.1; rw [h2C, h2fl, h2w] at this; exact this
  have hhwm : w.C.hwm ≤ 2 ^ 62 := by
    have := h2ok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; rw [h2C] at this; exact this
  imod store_wbegin K.B K.N K.p ⊤ CoPset.subseteq_top w.C b l $$ [Hpi Hcur Hgmap Hgwv]
    with ⟨Hcur, Hgmap, Hgwv, Hvc⟩
  · iframe; iframe #
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
