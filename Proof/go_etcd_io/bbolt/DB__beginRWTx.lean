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
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
