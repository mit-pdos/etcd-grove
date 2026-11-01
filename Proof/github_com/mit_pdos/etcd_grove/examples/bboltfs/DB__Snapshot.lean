/- Lean-first (no Rocq counterpart). The proof of `db.Snapshot()`.

Proved: every error path (a failed handle; no mapping, `meta0 == nil`). Not proved (`sorry`):
the success path, which needs changes in `DB.lean`:
- the mapped cells the reader loads (the two metas in `db.meta()` and `*db.meta()`, the root
  page's `count` and value) are in the mapping's invariant (`mapInv`, an `inv`), but a Go load
  is not atomic: every byte is a `Read`, a `StartRead` and a `FinishRead` (two atomic steps,
  `_internal_wp_untyped_read`), and a scalar or struct load reads byte after byte
  (`wp_readBytes`), `db.meta()` many loads; so the invariant cannot be opened around a load. The
  reader needs fractions of those cells for the duration of its loads (lent by the invariant
  while it holds the read lock, and the meta cells while it also holds `metalock`);
- `metaR` gives only `T !! txid = some (pageVal B)` with `ghostMapAuth γ.txs`, from which no
  `dbTx γ txid _` (a fragment) can be made: `metaR` needs `dbTx` of the current transaction;
- `dbReader` does not pin the path: its `mapR γ db f' fd' p'` may name another path than
  `isDB`'s, and the root page's bytes in the invariant (`pageIs p' r B'`) cannot be related to
  `metaR`'s (`pageIs p r B`) without `p = p'`.
The racing `ReadAt` (`os.File.ReadAt.specRacy`) needs two more:
- `io.EOF`'s value (`globalAddr io.EOF ↦□ eof`), which `err != io.EOF` compares with, and that it
  is not a `*PathError` (so that a failure is not taken for the end of the file): `pkgFacts`
  has neither;
- `len(out) = (pgid+1)*4096 ≤ 2^30` (the spec's `maxRW`), but `metaPagesOk` bounds the file by
  `2^40` only (`off + len < 2^63` follows from it).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__meta
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.pageAt
public import Spec.os.File__ReadAt
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
theorem DB.Snapshot.wp_proof (wp_meta : DB.«meta».spec (GF := GF) (hG := hG))
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG))
    (wp_ReadAt : os.File.ReadAt.specRacy (GF := GF) (hG := hG)) :
    DB.Snapshot.spec (GF := GF) (hG := hG) := by
  intro γ db t
  wp_start as ⟨Hdb, Hrd, Hlast⟩
  iunfold isDB at Hdb
  icases Hdb with ⟨%f, %fd, %p, #Hpkg, #Hos, #Hfile, #Hpath, #Hrw, #Hmeta, #Hguard⟩
  iunfold dbReader at Hrd
  icases Hrd with ⟨%f', %fd', %p', #Hfile', #Hpath', Hrd⟩
  iunfold pkgFacts at Hpkg
  icases Hpkg with ⟨#Hsync, %e1, %e2, #He1, #He2, %He, %eof, #Heof, %Heof⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
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
      obtain ⟨Hmx', Hmpok, Hhwm, HTn⟩ := Hok
      subst mx hwm
      obtain ⟨Hmpl, Hval, Hr2, Hrh, Hbound⟩ := Hmpok
      rw [show sync.rfrac.half = sync.rfrac.half.half + (metaDep + metaDep) by unfold metaDep; qp_eq] at *
      icases ((ghostVar_fractional γm ()).fractional _ _).1 $$ Htok with ⟨Hq, Htok⟩
      icases ((ghostVar_fractional γm ()).fractional _ _).1 $$ Htok with ⟨Hmd, Hpd⟩
      imod meta_borrow γ p base len γm γl mp (curPgid mp) T sync.rfrac.half.half $$ [HinvL Hq Hcur Hout Hauth Hmd]
        with ⟨Hq, Hcur, Hauth, Hk0, Hmc⟩
      · iframe; iframe #
      imod page_pageIs γ p base len γm γl mp (curPgid mp) (curPgid mp - 1) sync.rfrac.half.half
        (by omega) (by omega) $$ [HinvL Hq Hcur] with ⟨Hq, Hcur, %B2, #HB2⟩
      · iframe; iframe #
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
        rcases pickMeta_cur mp (base +ₗ 16) (base +ₗ 4112) Hval with ⟨Hpk, Hcm⟩ | ⟨Hpk, Hcm⟩ <;> rw [Hpk, Hcm]
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
        $$ [HinvL Hq Hauth Hk0 Hc0 Hc1] with ⟨Hq, Hout, Hauth, Hmd⟩
      · iframe #; iunfold metaBytes; iframe
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p)
        $$ [$Hmeta $Hsync $Hlocked Hfl Hcur Hmb Hauth Hout Hfail Hlauth Hown]
      · iunfold metaR
        iexists false, mp, mp, curPgid mp, mxc, T
        iframe
        dsimp only
        isplitr; · ipureintro; exact Hmx
        iframe
        isplitr; · ipureintro; exact ⟨rfl, ⟨Hmpl, Hval, Hr2, Hrh, Hbound⟩, rfl, HTn⟩
        iframe
        iexists B; iframe #; ipureintro; exact HT
      ihave Htok := ((ghostVar_fractional γm ()).fractional metaDep metaDep).2 $$ [Hmd Hpd]
      · iframe
      ihave Htok := ((ghostVar_fractional γm ()).fractional sync.rfrac.half.half (metaDep + metaDep)).2 $$ [Hq Htok]
      · iframe
      rw [← show sync.rfrac.half = sync.rfrac.half.half + (metaDep + metaDep) by unfold metaDep; qp_eq]
      sorry

end proof

end bboltfs
end EtcdGrove
end Perennial
