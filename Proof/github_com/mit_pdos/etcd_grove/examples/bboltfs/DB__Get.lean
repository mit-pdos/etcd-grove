/- Lean-first (no Rocq counterpart). The proof of `db.Get()`.

A Go load is not atomic (every byte is a `StartRead` and a `FinishRead`), so the reader borrows
the cells it loads from the mapping's invariant (`MapLoan.lean`): under `metalock`, the meta cells
whole (`meta_borrow`), which it views as the two typed metas for `DB.meta`'s spec and the copy
`*db.meta()`, and gives back before unlocking (`meta_return`); and a share of the root page's cells
(`page_borrow`, still under `metalock`, where the meta pages name the root page), from which it
loads the page's `count` (a typed `Page` view) and value (a `uint64` view), and which it gives back
before `RUnlock` (`page_return`). The root page's bytes are those `metaR` records (`pageIs_agree`),
so the result is `dbTx` of the current transaction.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__meta
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.pageAt
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.MapLoan
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

set_option maxHeartbeats 1600000 in
theorem DB.Get.wp_proof (wp_meta : DB.«meta».spec (GF := GF) (hG := hG))
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG)) :
    DB.Get.spec (GF := GF) (hG := hG) := by
  intro γ db t
  wp_start as ⟨Hdb, Hrd, Hlast⟩
  iunfold isDB at Hdb
  icases Hdb with ⟨%f, %fd, %p, #Hpkg, #Hos, #Hfile, #Hpath, #Hrw, #Hmeta, #Hguard⟩
  iunfold dbReader at Hrd
  icases Hrd with ⟨%f', %fd', %p', #Hfile', #Hpath', Hrd⟩
  iunfold pkgFacts at Hpkg
  icases Hpkg with ⟨#Hsync, %e1, %e2, #He1, #He2, %He, %eof, #Heof, %Heof⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p) $$ [$Hmeta $Hsync]
    as ⟨Hlocked, HR⟩
  iunfold metaR at HR
  icases HR with ⟨%b, %mp, %mx, %hwm, %mxc, %T, Hfl, Hcur, Hmb, %Hmx, Hauth, Hout, Hrest⟩
  wp_auto
  cases b with
  | true =>
    wp_auto
    wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p)
      $$ [$Hmeta $Hsync $Hlocked Hfl Hcur Hmb Hauth Hout Hrest]
    · iunfold metaR
      iexists true, mp, mx, hwm, mxc, T
      iframe
      ipureintro; exact Hmx
    (try wp_auto)
    iapply HΦ
    isplitl [Hrd]
    · iunfold dbReader; iexists f', fd', p'; iframe; iframe #
    iright; ipureintro; exact He.1
  | false =>
    wp_auto
    wp_apply sync.RWMutex.wp_RLock db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f' fd' p')
      $$ [$Hrd $Hsync] as ⟨Hrl, HM⟩
    iunfold mapR at HM
    icases HM with ⟨%st, HM⟩
    iunfold mapBody at HM
    icases HM with ⟨Hmap, Hflds, Hmr⟩
    rcases st with _ | ⟨base, len, γm⟩
    · dsimp only [mapFields, mapRest]
      icases Hflds with ⟨Hd, H0, H1⟩
      wp_auto
      wp_apply sync.RWMutex.wp_RUnlock db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f' fd' p')
        $$ [$Hrl $Hsync Hmap Hd H0 H1] as Hrd
      · iunfold mapR; iexists none; iunfold mapBody
        dsimp only [mapFields, mapRest]
        iframe
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p)
        $$ [$Hmeta $Hsync $Hlocked Hfl Hcur Hmb Hauth Hout Hrest]
      · iunfold metaR
        iexists false, mp, mx, hwm, mxc, T
        iframe
        ipureintro; exact Hmx
      (try wp_auto)
      iapply HΦ
      isplitl [Hrd]
      · iunfold dbReader; iexists f', fd', p'; iframe; iframe #
      iright; ipureintro; exact He.1
    · dsimp only [mapFields, mapRest]
      icases Hflds with ⟨Hd, H0, H1⟩
      icases Hmr with ⟨%Hbase, Htok, #Hinv, Hf, Hfd⟩
      icombine Hpath Hpath' gives %Hpp
      subst Hpp
      iunfold mapInv at Hinv
      icases Hinv with ⟨%Hlen, %γl, #HinvL⟩
      icases Hrest with ⟨Hfail, %Hok, Hlauth, Hown, %B, #HB, #Htx, %HT⟩
      obtain ⟨Hmx', Hmpok, Hhwm⟩ := Hok
      subst mx hwm
      obtain ⟨Hmpl, Hval, Hr2, Hrh, Hbound⟩ := Hmpok
      rw [show sync.rfrac.half = sync.rfrac.half.half + (metaDep + metaDep) by unfold metaDep; qp_eq] at *
      icases ((ghostVar_fractional γm ()).fractional _ _).1 $$ Htok with ⟨Hq, Htok⟩
      icases ((ghostVar_fractional γm ()).fractional _ _).1 $$ Htok with ⟨Hmd, Hpd⟩
      imod meta_borrow γ p base len γm γl mp (curPgid mp) T sync.rfrac.half.half $$ [HinvL Hq Hcur Hout Hauth Hmd]
        with ⟨Hq, Hcur, Hout, Hauth, Hk0, Hmc⟩
      · iframe; iframe #
      imod page_borrow γ p base len γm γl mp (curPgid mp) (curRoot mp) sync.rfrac.half.half metaDep Hr2 Hrh
        $$ [HinvL Hq Hcur Hpd] with ⟨Hq, Hcur, %Hlen2, %B', #HB', Hkr, Hbr⟩
      · iframe; iframe #
      icases pageIs_agree p (curRoot mp) B B' $$ [HB HB'] with %HBB
      · iframe #
      subst HBB
      obtain ⟨Hm0, Hm1⟩ := metasOf_take mp Hmpl
      have Hmcl := metasOf_length mp Hmpl
      iunfold metaBytes at Hmc
      icases Hmc with ⟨Hc0, Hc1⟩
      have h16 : 0 < (base +ₗ (16 : Int)).addr := by simp only [Loc.add]; omega
      have h4112 : 0 < (base +ₗ (4112 : Int)).addr := by simp only [Loc.add]; omega
      icases (bytesPointsto_typed (V := Meta) (base +ₗ (16 : Int)) _ ((metasOf mp).take 64)
        (by simp; omega) h16).1 $$ Hc0 with Hc0
      icases (bytesPointsto_typed (V := Meta) (base +ₗ (4112 : Int)) _ ((metasOf mp).drop 64)
        (by simp; omega) h4112).1 $$ Hc1 with Hc1
      rw [Hm0, Hm1]
      have Hb0 : (base +ₗ (16 : Int) ↦{DFrac.own (1 : Qp).half} fileMeta mp 0 : IProp GF) ⊢
          bytesPointsto (base +ₗ (16 : Int)) (DFrac.own (1 : Qp).half) ((metasOf mp).take 64) := by
        rw [← Hm0]; exact (bytesPointsto_typed (V := Meta) _ _ _ (by simp; omega) h16).2
      have Hb1 : (base +ₗ (4112 : Int) ↦{DFrac.own (1 : Qp).half} fileMeta mp 1 : IProp GF) ⊢
          bytesPointsto (base +ₗ (4112 : Int)) (DFrac.own (1 : Qp).half) ((metasOf mp).drop 64) := by
        rw [← Hm1]; exact (bytesPointsto_typed (V := Meta) _ _ _ (by simp; omega) h4112).2
      have Hsel : (base +ₗ (16 : Int) ↦{DFrac.own (1 : Qp).half} fileMeta mp 0 ∗
          base +ₗ (4112 : Int) ↦{DFrac.own (1 : Qp).half} fileMeta mp 1 : IProp GF) ⊢
          pickMetaRes (base +ₗ 16) (fileMeta mp 0) (base +ₗ 4112) (fileMeta mp 1) ↦{DFrac.own (1 : Qp).half} curMeta mp ∗
          (pickMetaRes (base +ₗ 16) (fileMeta mp 0) (base +ₗ 4112) (fileMeta mp 1) ↦{DFrac.own (1 : Qp).half} curMeta mp -∗
            base +ₗ (16 : Int) ↦{DFrac.own (1 : Qp).half} fileMeta mp 0 ∗
            base +ₗ (4112 : Int) ↦{DFrac.own (1 : Qp).half} fileMeta mp 1) := by
        rcases pick_cur mp (base +ₗ 16) (base +ₗ 4112) Hval with ⟨Hpk, Hcm⟩ | ⟨Hpk, Hcm⟩ <;> rw [Hpk, Hcm]
        · iintro ⟨H0, H1⟩; iframe H0; iintro H0; iframe
        · iintro ⟨H0, H1⟩; iframe H1; iintro H1; iframe
      have Hlv : (monoNatAuthOwn γ.last 1 (curMeta mp).txid'.toNat ∗ dbLast γ t : IProp GF) ⊢
          (monoNatAuthOwn γ.last 1 (curMeta mp).txid'.toNat ∗ dbLast γ t) ∗ ⌜t ≤ (curMeta mp).txid'.toNat⌝ :=
        keep_pure (by
          iintro ⟨H1, H2⟩; iunfold dbLast at H2
          icases monoNatLbOwn_valid γ.last 1 _ _ $$ H1 H2 with %h
          ipureintro; exact h.2)
      icases Hlv $$ [Hlauth Hlast] with ⟨⟨Hlauth, -⟩, %Hle⟩
      · iframe
      ihave #Hlb := monoNatLbOwn_get γ.last 1 _ $$ Hlauth
      wp_auto
      have hnn : (base +ₗ (16 : Int)) ≠ null := by
        intro h; have := congrArg Loc.addr h; simp only [Loc.add, null] at this; omega
      rw [decide_eq_false hnn]
      wp_auto
      wp_apply wp_meta db (base +ₗ 16) (base +ₗ 4112) (fileMeta mp 0) (fileMeta mp 1) _ _ _ Hval
        $$ [H0 H1 Hc0 Hc1] as ⟨H0, H1, Hc0, Hc1⟩
      · iframe; ipureintro; exact ⟨h16, h4112⟩
      icases Hsel $$ [Hc0 Hc1] with ⟨Hc, Hcb⟩
      · iframe
      wp_auto
      icases Hcb $$ Hc with ⟨Hc0, Hc1⟩
      icases Hb0 $$ Hc0 with Hc0
      icases Hb1 $$ Hc1 with Hc1
      imod meta_return γ p base len γm γl T sync.rfrac.half.half (metasOf mp)
        $$ [HinvL Hq Hout Hauth Hk0 Hc0 Hc1] with ⟨Hq, Hout, Hauth, Hmd⟩
      · iframe #; iunfold metaBytes; iframe
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p)
        $$ [$Hmeta $Hsync $Hlocked Hfl Hcur Hmb Hauth Hout Hfail Hlauth Hown]
      · iunfold metaR
        iexists false, mp, mp, curPgid mp, mxc, T
        iframe
        dsimp only
        isplitr; · ipureintro; exact Hmx
        iframe
        isplitr; · ipureintro; exact ⟨rfl, ⟨Hmpl, Hval, Hr2, Hrh, Hbound⟩, rfl⟩
        iframe
        iexists B; iframe #; ipureintro; exact HT
      iunfold pageIs at HB
      icases HB with ⟨%HBl, -⟩
      have hrr : 4096 * curRoot mp + 4096 ≤ 4096 * curPgid mp := by
        have := Nat.mul_le_mul_left 4096 (Nat.succ_le_of_lt Hrh); omega
      have hoff : sint.Z ((curMeta mp).root'.root' * W64 4096) = ((4096 * curRoot mp : Nat) : Int) := by
        have h1 : (curMeta mp).root'.root'.toNat * 4096 < 2 ^ 30 := by
          have : curRoot mp = (curMeta mp).root'.root'.toNat := rfl
          omega
        show _ = (((4096 * (curMeta mp).root'.root'.toNat : Nat)) : Int)
        word
      have hlenZ : sint.Z (W64 (len : Int)) = (len : Int) := sint_Z_W64_nat _ (by omega)
      wp_apply wp_pageAt ⟨base, W64 len, W64 len⟩ ((curMeta mp).root'.root' * W64 4096)
      · ipureintro
        refine ⟨Hbase, ?_, ?_⟩
        · rw [hoff]; omega
        · rw [hoff]; simp only at hlenZ ⊢; rw [hlenZ]; omega
      simp only
      rw [hoff]
      have hl : 0 < (base +ₗ ((4096 * curRoot mp : Nat) : Int)).addr := by simp only [Loc.add]; omega
      icases bytesPointsto_view_read (V := Page) (base +ₗ ((4096 * curRoot mp : Nat) : Int)) _ B 0
        (base +ₗ ((4096 * curRoot mp : Nat) : Int)) (by simp) (by omega) hl $$ Hbr with ⟨Hpg, Hpgb⟩
      simp only [List.drop_zero]
      rw [show (decode (List.take 16 B) : Page) = pageHdrOf B from rfl]
      have hlnn : (base +ₗ ((4096 * curRoot mp : Nat) : Int)) ≠ null := by
        intro h; have := congrArg Loc.addr h; simp only [Loc.add, null] at this hl; omega
      icases typedPointsto_split _ _ _ $$ Hpg with Hpg
      simp only [TypedPointsto.typedPointstoDef]
      icases Hpg with ⟨Hid, Hflags, Hcount, Hover, -⟩
      wp_auto
      ihave Hpg : (base +ₗ ((4096 * curRoot mp : Nat) : Int)) ↦{DFrac.own metaDep.half.half} pageHdrOf B
        $$ [Hid Hflags Hcount Hover]
      · iapply typedPointsto_combine _ _ _ hlnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Hbr := Hpgb $$ Hpg
      have hcnt : (pageHdrOf B).count' = (decode (List.take 2 (List.drop 2 (List.drop 8 (List.take 16 B)))) : w16) := rfl
      generalize (decode (List.take 2 (List.drop 2 (List.drop 8 (List.take 16 B)))) : w16) = cnt at hcnt ⊢
      by_cases hc : cnt = W16 1
      · rw [decide_eq_true hc]
        wp_auto
        have hix : sint.Z ((curMeta mp).root'.root' * W64 4096 + W64 16) =
            ((4096 * curRoot mp + 16 : Nat) : Int) := by
          have h1 : (curMeta mp).root'.root'.toNat * 4096 < 2 ^ 30 := by
            have : curRoot mp = (curMeta mp).root'.root'.toNat := rfl
            omega
          show _ = (((4096 * (curMeta mp).root'.root'.toNat + 16 : Nat)) : Int)
          word
        rw [hix, ite_cond_eq_true _ _ (eq_true ⟨by omega, by rw [hlenZ]; omega⟩), sliceIndexRef_byte _ _ Hbase (by omega)]
        simp only
        icases bytesPointsto_view_read (V := w64) (base +ₗ ((4096 * curRoot mp : Nat) : Int)) _ B 16
          (base +ₗ ((4096 * curRoot mp + 16 : Nat) : Int)) (by rw [loc_add_assoc]; congr 1)
          (by omega) hl $$ Hbr with ⟨Hv, Hvb⟩
        wp_auto
        ihave Hbr := Hvb $$ Hv
        imod page_return γ p base len γm γl (curRoot mp) sync.rfrac.half.half metaDep B Hr2
          $$ [HinvL Hq Hkr Hbr] with ⟨Hq, Hpd⟩
        · iframe #; iframe
        ihave Htok := ((ghostVar_fractional γm ()).fractional metaDep metaDep).2 $$ [Hmd Hpd]
        · iframe
        ihave Htok := ((ghostVar_fractional γm ()).fractional sync.rfrac.half.half (metaDep + metaDep)).2 $$ [Hq Htok]
        · iframe
        rw [← show sync.rfrac.half = sync.rfrac.half.half + (metaDep + metaDep) by unfold metaDep; qp_eq]
        wp_apply sync.RWMutex.wp_RUnlock db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f' fd' p)
          $$ [$Hrl $Hsync Hmap Hd H0 H1 Htok Hf Hfd] as Hrd
        · iunfold mapR; iexists (some (base, len, γm)); iunfold mapBody
          dsimp only [mapFields, mapRest]
          isplitl [Hmap]; · iexact Hmap
          isplitl [Hd H0 H1]; · iframe
          isplitr; · ipureintro; exact Hbase
          isplitl [Htok]; · iexact Htok
          isplitr
          · iunfold mapInv
            isplitr; · ipureintro; exact Hlen
            iexists γl; iexact HinvL
          iframe
        (try wp_auto)
        iapply HΦ
        isplitl [Hrd]
        · iunfold dbReader; iexists f', fd', p; iframe; iframe #
        ileft
        isplitr; · ipureintro; exact ⟨rfl, Hle⟩
        have hpv : pageVal B = some (decode (List.take 8 (List.drop 16 B))) := by
          unfold pageVal; rw [hcnt, if_pos hc]
        rw [if_pos rfl, ← hpv]
        iunfold dbLast
        iframe #
      · rw [decide_eq_false hc]
        wp_auto
        imod page_return γ p base len γm γl (curRoot mp) sync.rfrac.half.half metaDep B Hr2
          $$ [HinvL Hq Hkr Hbr] with ⟨Hq, Hpd⟩
        · iframe #; iframe
        ihave Htok := ((ghostVar_fractional γm ()).fractional metaDep metaDep).2 $$ [Hmd Hpd]
        · iframe
        ihave Htok := ((ghostVar_fractional γm ()).fractional sync.rfrac.half.half (metaDep + metaDep)).2 $$ [Hq Htok]
        · iframe
        rw [← show sync.rfrac.half = sync.rfrac.half.half + (metaDep + metaDep) by unfold metaDep; qp_eq]
        wp_apply sync.RWMutex.wp_RUnlock db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f' fd' p)
          $$ [$Hrl $Hsync Hmap Hd H0 H1 Htok Hf Hfd] as Hrd
        · iunfold mapR; iexists (some (base, len, γm)); iunfold mapBody
          dsimp only [mapFields, mapRest]
          isplitl [Hmap]; · iexact Hmap
          isplitl [Hd H0 H1]; · iframe
          isplitr; · ipureintro; exact Hbase
          isplitl [Htok]; · iexact Htok
          isplitr
          · iunfold mapInv
            isplitr; · ipureintro; exact Hlen
            iexists γl; iexact HinvL
          iframe
        (try wp_auto)
        iapply HΦ
        isplitl [Hrd]
        · iunfold dbReader; iexists f', fd', p; iframe; iframe #
        ileft
        isplitr; · ipureintro; exact ⟨rfl, Hle⟩
        have hpv : pageVal B = none := by
          unfold pageVal; rw [hcnt, if_neg hc]
        rw [if_neg Bool.false_ne_true, ← hpv]
        iunfold dbLast
        iframe #

end proof

end bboltfs
end EtcdGrove
end Perennial
