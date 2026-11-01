/- Lean-first (no Rocq counterpart). The proof of `db.Snapshot()`.

Proved: every error path (a failed handle; no mapping, `meta0 == nil`), and the success path up to
the copy: the meta copied through the meta cells borrowed from the mapping's invariant
(`meta_borrow`/`meta_return`, as in `DB__Get.lean`), `metalock` released, the deferred `RUnlock`
pushed, with `pageIs` of the root page (`metaR`) and of the last committed page `pgid - 1`
(`page_pageIs`) in hand. Not proved (`sorry`): from `make` on. What remains:
- `make([]byte, (pgid+1)*4096)` (`wp_slice_make2`, `(pgid+1)*4096 ≤ 2^30` by `metaPagesOk`);
- the racing `ReadAt` (`os.File.ReadAt.specRacy`) over the held ranges of those two pages' discarded
  bytes, with the file and fd fractions of `mapRest`;
- `err != nil && err != io.EOF`: comparing an `error` with `io.EOF` needs `eof`'s dynamic type to be
  comparable, which `pkgFacts` does not say (an addition to `pkgFacts` may be needed);
- `n ≥ pgid*4096`: the `io.EOF` clause at the last byte of page `pgid - 1`;
- the root page's bytes in `out` are `B` (the held range), viewed from `out`'s slice points-to
  (`bytesPointsto_ownSlice`) as a `Page` and a `uint64`, as in `Get`;
- the deferred `RUnlock` with `mapR` rebuilt from the fields, `γm`'s share and the file fractions.
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

theorem snap_mul4096 (x : w64) (hx : x.toNat * 4096 < 2 ^ 30) :
    sint.Z (x * W64 4096) = ((4096 * x.toNat : Nat) : Int) := by
  word

theorem snap_sintZ (n : w64) (h : n.toNat ≤ 2 ^ 30) : sint.Z n = (n.toNat : Int) := by
  word

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
      have hpg : curPgid mp = (curMeta mp).pgid'.toNat := rfl
      have hsz : sint.Z (((curMeta mp).pgid' + W64 1) * W64 4096) =
          (((curPgid mp + 1) * 4096 : Nat) : Int) := by
        rw [hpg] at Hbound ⊢; word
      wp_apply (wp_slice_make2 (V := w8) (((curMeta mp).pgid' + W64 1) * W64 4096)) as %buf ⟨Hbuf, -⟩
      · ipureintro; rw [hsz]; omega
      have hnat : sint.nat (((curMeta mp).pgid' + W64 1) * W64 4096) = (curPgid mp + 1) * 4096 := by
        show (sint.Z _).toNat = _; omega
      rw [hnat]
      ihave #HBc := HB
      ihave #HB2c := HB2
      iunfold pageIs at HBc HB2c
      icases HBc with ⟨%HBl, #HBb⟩
      icases HB2c with ⟨%HB2l, #HB2b⟩
      ihave Hrs : ([∗list] r ∈ [(4096 * curRoot mp, DFrac.discard, B.map (·, true)),
          (4096 * (curPgid mp - 1), DFrac.discard, B2.map (·, true))],
          osBytes (GF := GF) p r.1 r.2.1 r.2.2) $$ []
      · iapply BigSepL.bigSepL_cons.2; isplitl; · iexact HBb
        iapply BigSepL.bigSepL_singleton.2; iexact HB2b
      wp_apply wp_ReadAt f' fd' p (DFrac.own sync.rfrac.half) buf
          (List.replicate ((curPgid mp + 1) * 4096) (zero_val w8)) (W64 0) (DFrac.own sync.rfrac.half)
          ⟨p, true, true⟩ _ eof rfl (by decide) (by simp; omega) (by simp; omega)
        $$ [Hf Hbuf Hfd Hrs] as %n %err ⟨Hf, Hfd, Hrs, %vs', Hbuf, %Hres⟩
      · iframe; iframe #
      obtain ⟨-, Heofpe, T, l, rfl⟩ := Heof
      obtain ⟨Hl', Hn, Hheld, Hcase⟩ := Hres
      simp only [List.length_replicate] at Hl' Hn Hheld Hcase
      have hlast : os.heldByte [(4096 * curRoot mp, DFrac.discard, B.map (·, true)),
          (4096 * (curPgid mp - 1), DFrac.discard, B2.map (·, true))] (4096 * curPgid mp - 1) (B2[4095]!) := by
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_, ?_⟩
        · dsimp only; omega
        · dsimp only
          rw [show 4096 * curPgid mp - 1 - 4096 * (curPgid mp - 1) = 4095 by omega]
          rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)]
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show 4095 < B2.length by omega)]
      have hcase : (err = interface.nil ∨ err = interface.mkOk (go.GoType.PointerType T) #l) ∧
            4096 * curPgid mp ≤ n.toNat ∨
          ∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType _root_.Perennial.io.fs.PathError.ty) #pe := by
        rcases Hcase with ⟨rfl, Hnlen⟩ | ⟨rfl, Hreach⟩ | ⟨pe, rfl⟩
        · left; refine ⟨Or.inl rfl, ?_⟩; rw [Hnlen]; rw [Nat.add_mul]; omega
        · left; refine ⟨Or.inr rfl, ?_⟩
          have := Hreach _ _ hlast (by simp) (by simp; rw [Nat.add_mul]; omega)
          simp at this; omega
        · right; exact ⟨pe, rfl⟩
      clear Hcase
      rcases hcase with ⟨herr, hnge⟩ | ⟨pe, rfl⟩
      · have hpgw : sint.Z ((curMeta mp).pgid' * W64 4096) = ((4096 * curPgid mp : Nat) : Int) := by
          rw [hpg]; exact snap_mul4096 _ (by rw [← hpg]; rw [Nat.add_mul] at Hbound; omega)
        have hnZ : sint.Z n = (n.toNat : Int) :=
          snap_sintZ n (by rw [Nat.add_mul] at Hbound Hn; omega)
        rcases herr with rfl | rfl <;> wp_auto
        all_goals
          rw [decide_eq_false (by rw [hpgw, hnZ]; omega)]
          wp_auto
          sorry
      · wp_auto
        by_cases hT : go.GoType.PointerType _root_.Perennial.io.fs.PathError.ty = go.GoType.PointerType T
        · rw [ite_cond_eq_true _ _ (eq_true hT)]
          have hpl : pe ≠ l := by
            rintro rfl; exact Heofpe pe (by rw [hT])
          wp_auto
          rw [decide_eq_false hpl]
          wp_auto
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
          iright; ipureintro; intro h; cases h
        · rw [ite_cond_eq_false _ _ (eq_false hT)]
          wp_auto
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
          iright; ipureintro; intro h; cases h

end proof

end bboltfs
end EtcdGrove
end Perennial
