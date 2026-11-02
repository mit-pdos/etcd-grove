/- Lean-first (no Rocq counterpart). The proof of `db.Snapshot()`.

Under `metalock`, as in `DB__Get.lean`: the meta copied through the meta cells borrowed from the
mapping's invariant (`meta_borrow`/`meta_return`), with `pageIs` of the root page (`metaR`) and of
the last committed page `pgid - 1` (`page_pageIs`) in hand; then `metalock` released, and the
deferred `RUnlock` pushed. The copy is a racing `ReadAt` (`os.File.ReadAt.specRacy`) of
`[0, (pgid+1)*4096)` into a fresh buffer, over the held ranges of those two pages' discarded bytes
and `mmaplock`'s fractions of the file and its fd. Its error is `nil`, `io.EOF` or a `*PathError`.
`err != io.EOF` compares two interface values: `io.EOF` is a pointer error (`pkgFacts`), so the
comparison does not panic, and a `*PathError` is never `io.EOF`. With `nil` the read is whole; with
`io.EOF` it reaches every held byte, the last byte of page `pgid - 1` included, so `n ≥ pgid*4096`
and the panic never fires. The root page's bytes in the buffer are then exactly `B` (the held-byte
clause), viewed as a `Page` (its `count`) and a `uint64` (its value), so the result is `dbTx` of the
current transaction. The deferred `RUnlock` gives back `mmaplock`'s resource.
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

theorem snap_add16 (x : w64) (hx : x.toNat * 4096 < 2 ^ 30) :
    sint.Z (x * W64 4096 + W64 16) = ((4096 * x.toNat + 16 : Nat) : Int) := by
  word

/-- `DB.Snapshot.spec` with the reader slot the caller borrowed (`dbReader_borrow`), behind a later. -/
abbrev DB.Snapshot.readerSpec : Prop :=
  ∀ (γ : DBNames) (db : Loc) (t : Nat) (o : Option (Nat × Nat)),
  {{ isDB (GF := GF) γ db ∗ ▷ dbReader (GF := GF) γ db ∗ dbLast (GF := GF) γ t ∗
      dbOwnerOpt (GF := GF) γ o }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Snapshot")) (Val #()))
  {{ (txid v : w64) (has : Bool) (err : GoInterface), RET (PairV (PairV (PairV #txid #v) #has) #err);
      dbReader (GF := GF) γ db ∗ dbOwnerOpt (GF := GF) γ o ∗
      ((⌜err = interface.nil ∧ t ≤ txid.toNat ∧ ∀ x, o = some x → txid.toNat = x.1⌝ ∗ dbLast (GF := GF) γ txid.toNat ∗
          dbTx (GF := GF) γ txid.toNat (if has then some v else none)) ∨
       ⌜err ≠ interface.nil⌝) }}

set_option maxHeartbeats 4000000 in
theorem DB.Snapshot.wp_reader (wp_meta : DB.«meta».spec (GF := GF) (hG := hG))
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG))
    (wp_ReadAt : os.File.ReadAt.specRacy (GF := GF) (hG := hG)) :
    DB.Snapshot.readerSpec (GF := GF) (hG := hG) := by
  intro γ db t o
  wp_start as ⟨Hdb, Hrd, Hlast, Hoo⟩
  iunfold isDB at Hdb
  icases Hdb with ⟨⟨%f, %fd, %p, #Hpkg, #Hos, #Hfile, #Hpath, #Hrw, #Hmeta, #Hguard⟩, -⟩
  iunfold pkgFacts at Hpkg
  icases Hpkg with ⟨#Hsync, %e1, %e2, #He1, #He2, %He, %eof, #Heof, %Heof, -⟩
  wp_auto
  iunfold dbReader at Hrd
  icases Hrd with ⟨%f', %fd', %p', #Hfile', #Hpath', Hrd⟩
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
    iframe Hoo; iright; ipureintro; exact He.1
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
      iframe Hoo; iright; ipureintro; exact He.1
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
      icases dbOwnerOpt_agree γ o _ _ $$ [Hoo Hown] with ⟨⟨Hoo, Hown⟩, %Hoeq⟩
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
        have hR : curRoot mp = (curMeta mp).root'.root'.toNat := rfl
        have hrr : 4096 * curRoot mp + 4096 ≤ 4096 * curPgid mp := by
          have := Nat.mul_le_mul_left 4096 (Nat.succ_le_of_lt Hrh); omega
        have hoff : sint.Z ((curMeta mp).root'.root' * W64 4096) = ((4096 * curRoot mp : Nat) : Int) := by
          rw [hR]; exact snap_mul4096 _ (by rw [← hR]; rw [Nat.add_mul] at Hbound; omega)
        have hix : sint.Z ((curMeta mp).root'.root' * W64 4096 + W64 16) =
            ((4096 * curRoot mp + 16 : Nat) : Int) := by
          rw [hR]; exact snap_add16 _ (by rw [← hR]; rw [Nat.add_mul] at Hbound; omega)
        have hget : ∀ j < 4096, vs'[4096 * curRoot mp + j]? = B[j]? := by
          intro j hj
          have hb := Hheld (4096 * curRoot mp + j) (B[j]'(by omega))
            ⟨_, List.mem_cons_self .., by dsimp only; omega, by
              dsimp only; rw [show 4096 * curRoot mp + j - 4096 * curRoot mp = j by omega]
              simp [List.getElem?_eq_getElem (show j < B.length by omega)]⟩
            (by simp) (by simp; omega)
          simp only [show (W64 0).toNat = 0 from rfl, Nat.sub_zero] at hb
          rw [hb, List.getElem?_eq_getElem (show j < B.length by omega)]
        have h16 : (vs'.drop (4096 * curRoot mp)).take 16 = B.take 16 := by
          apply List.ext_getElem?; intro j
          simp only [List.getElem?_take, List.getElem?_drop]
          split
          · exact hget j (by omega)
          · rfl
        have h8 : (vs'.drop (4096 * curRoot mp + 16)).take 8 = (B.drop 16).take 8 := by
          apply List.ext_getElem?; intro j
          simp only [List.getElem?_take, List.getElem?_drop]
          split
          · rw [show 4096 * curRoot mp + 16 + j = 4096 * curRoot mp + (16 + j) by omega]
            exact hget _ (by omega)
          · rfl
        rcases herr with rfl | rfl <;> wp_auto
        all_goals
          rw [decide_eq_false (by rw [hpgw, hnZ]; omega)]
          wp_auto
          ihave %Hbl := ownSlice_len $$ Hbuf
          ihave %Hpos := ownSlice_ptr_pos buf vs' _ (by intro h; rw [h] at Hl'; simp at Hl') $$ Hbuf
          have hlenZ : sint.Z buf.len = (vs'.length : Int) := by
            have h1 : (sint.Z buf.len).toNat = vs'.length := Hbl.1.symm
            have h2 := Hbl.2; omega
          wp_apply wp_pageAt buf ((curMeta mp).root'.root' * W64 4096)
          · ipureintro; refine ⟨Hpos, ?_, ?_⟩
            · rw [hoff]; omega
            · rw [hoff, hlenZ, Hl']; rw [Nat.add_mul]; omega
          simp only
          rw [hoff]
          icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) buf _ _ Hpos $$ Hbuf
            with ⟨Hbytes, -⟩
          simp only [flatMap_encode_w8]
          have hl : 0 < (buf.ptr +ₗ ((4096 * curRoot mp : Nat) : Int)).addr := by
            simp only [Loc.add]; omega
          icases bytesPointsto_view_read (V := Page) buf.ptr _ vs' (4096 * curRoot mp)
            (buf.ptr +ₗ ((4096 * curRoot mp : Nat) : Int)) rfl (by rw [Hl', Nat.add_mul]; omega) Hpos
            $$ Hbytes with ⟨Hpg, Hpgb⟩
          rw [h16, show (decode (List.take 16 B) : Page) = pageHdrOf B from rfl]
          have hlnn : (buf.ptr +ₗ ((4096 * curRoot mp : Nat) : Int)) ≠ null := by
            intro h; have := congrArg Loc.addr h; simp only [Loc.add, null] at this hl; omega
          icases typedPointsto_split _ _ _ $$ Hpg with Hpg
          simp only [TypedPointsto.typedPointstoDef]
          icases Hpg with ⟨Hid, Hflags, Hcount, Hover, -⟩
          wp_auto
          ihave Hpg : (buf.ptr +ₗ ((4096 * curRoot mp : Nat) : Int)) ↦{DFrac.own 1} pageHdrOf B
            $$ [Hid Hflags Hcount Hover]
          · iapply typedPointsto_combine _ _ _ hlnn
            simp only [TypedPointsto.typedPointstoDef]
            iframe
          ihave Hbytes := Hpgb $$ Hpg
          have hcnt : (pageHdrOf B).count' = (decode (List.take 2 (List.drop 2 (List.drop 8 (List.take 16 B)))) : w16) := rfl
          generalize (decode (List.take 2 (List.drop 2 (List.drop 8 (List.take 16 B)))) : w16) = cnt at hcnt ⊢
          by_cases hc : cnt = W16 1
          · rw [decide_eq_true hc]
            wp_auto
            rw [hix, ite_cond_eq_true _ _ (eq_true ⟨by omega, by rw [hlenZ, Hl', Nat.add_mul]; omega⟩),
              sliceIndexRef_byte _ _ Hpos (by omega)]
            (try simp only)
            icases bytesPointsto_view_read (V := w64) buf.ptr _ vs' (4096 * curRoot mp + 16)
              (buf.ptr +ₗ ((4096 * curRoot mp + 16 : Nat) : Int)) rfl (by rw [Hl', Nat.add_mul]; omega) Hpos
              $$ Hbytes with ⟨Hv, -⟩
            rw [h8]
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
            iframe Hoo
            ileft
            isplitr; · ipureintro; exact ⟨rfl, Hle, Hoeq⟩
            have hpv : pageVal B = some (decode (List.take 8 (List.drop 16 B))) := by
              unfold pageVal; rw [hcnt, if_pos hc]
            rw [if_pos rfl, ← hpv]
            iunfold dbLast
            iframe #
          · rw [decide_eq_false hc]
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
            iframe Hoo
            ileft
            isplitr; · ipureintro; exact ⟨rfl, Hle, Hoeq⟩
            have hpv : pageVal B = none := by
              unfold pageVal; rw [hcnt, if_neg hc]
            rw [if_neg Bool.false_ne_true, ← hpv]
            iunfold dbLast
            iframe #
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
          iframe Hoo; iright; ipureintro; intro h; cases h
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
          iframe Hoo; iright; ipureintro; intro h; cases h

/-- `DB.Snapshot.wp_reader`, the reader slot borrowed from `isDB`'s pool with the thread token and
given back after. -/
theorem DB.Snapshot.wp_proof (wp_meta : DB.«meta».spec (GF := GF) (hG := hG))
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG))
    (wp_ReadAt : os.File.ReadAt.specRacy (GF := GF) (hG := hG)) :
    DB.Snapshot.spec (GF := GF) (hG := hG) := by
  intro γ db t o
  wp_start_folded as ⟨#Hdb, Htok, Hlast, Hoo⟩
  iapply wp_fupd
  iapply fupd_wp
  imod dbReader_borrow γ db $$ [Htok] with ⟨Hrd, Hloan⟩
  · iframe; iframe #
  imodintro
  wp_apply DB.Snapshot.wp_reader wp_meta wp_pageAt wp_ReadAt γ db t o $$ [$Hdb $Hrd $Hlast $Hoo]
    as %txid %v %has %err ⟨Hrd, Hoo, Hres⟩
  imod dbReader_giveBack γ db $$ [Hloan Hrd] with Htok
  · iframe
  imodintro
  iapply HΦ
  iframe

end proof

end bboltfs
end EtcdGrove
end Perennial
