/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__Seek.lean` (U6h, U6i, `notes/bbolt-proof-plan.md`):
split on `T.rw`. A reader (`wp_reader`): `seek` (`Cursor.seek_r`), whose stack is at entry
`seekIdx es kb` (`rRoute_seekPos`); past its leaf's end, `next` (`Cursor.next_r`, the stack
unchanged past the last entry); the result as the public `curAt`. A writer (`wp_writer`):
`Read/PubWSeek`'s.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__Seek
public import Spec.go_etcd_io.bbolt.Cursor__seek_r
public import Spec.go_etcd_io.bbolt.Cursor__next_r
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Proof.go_etcd_io.bbolt.Read.PubR
public import Proof.go_etcd_io.bbolt.Read.SeekPos
public import Proof.go_etcd_io.bbolt.Txn.RdInit
public import Proof.go_etcd_io.bbolt.Read.PubWSeek
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A reader's `Seek`.** -/
theorem Cursor.Seek.wp_reader [HasExt osFsExt]
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hseek : Cursor.seek_r.spec (GF := GF) (hG := hG))
    (hnx : Cursor.next_r.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (key : GoSlice) (kb : GoString) (dk : DFrac)
    (hro : T.rw = false) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos ∗ key ↦*{dk} kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Seek")) (Val #key))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗ key ↦*{dk} kb ∗
      boltCur tx γ c T es (some (seekIdx es kb)) ∗ curAt tx γ es (seekIdx es kb) k v }} := by
  wp_start as ⟨Ht, Hc, Hkey⟩
  unfold boltTx boltCur
  icases rdCur_open _ _ tx c q T es pos hro $$ [Ht Hc] with
    ⟨%K, %v, %r, %b, %stk, %els, %bv, %ibp, %pp, Hk, #Hb, Hc, Hs, Hcap, #Hreg, #Hvo, %Hf, Hcl⟩
  · iframe
  obtain ⟨-, hfacts, -⟩ := Hf
  have hok := hfacts.2.1
  have hlen : es.length = (rEnts v bv).length := by rw [hfacts.2.2.1, rEnts_length]
  have hsk : seekIdx es kb = ((rEnts v bv).takeWhile (entLt kb)).length := by
    rw [hfacts.2.2.1]; exact seekIdx_rEnts v bv kb
  icases (persistent_entails_left (rdTxK_view K tx .loan q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  obtain ⟨-, C, hokC, hvC⟩ := Hvw
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  obtain ⟨-, -, -, pht, hpht⟩ := hokC.1
  rw [← hpv] at hpht
  ihave #Hpkg := (rdTxK_pkgInit _ tx .loan q T v) $$ Hk
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases rdTxK_flags_acc K tx .loan q T v $$ Hk with ⟨Hmg, Hdb, Hw, -, %Hdbn, Hkcl⟩
  unfold rBktP
  icases Hb with ⟨#HIB, #Htx, #Hbks, #Hpage, #Hroot, #Hnodes, #Hhdr, #Hil⟩
  wp_auto
  rw [decide_eq_false Hdbn]
  simp only [Bool.not_false]
  wp_apply hA
  try wp_auto
  ihave Hk := Hkcl $$ Hmg Hdb Hw
  wp_apply hseek K tx .loan q T v b DFrac.discard bv ibp pp c stk els key (KeyR.heap dk) kb hok.1
    hok.2.1 $$ [Hk Hc Hs Hcap Hkey]
    as %k %vl %fl ⟨%stk', %els', %e, %pid, %pg, Hk, -, Hc, Hs, Hcap, Hkey, %Hr, Hkv⟩
  · iframe; unfold rBktP keyR; iframe; iframe #
  obtain ⟨hrt, hpa, hfl, hidx⟩ := Hr
  obtain ⟨s0, hp0⟩ := rRoute_seekPos kb hok pht hpht _ hrt
  rw [← hsk] at hp0
  obtain ⟨els2, e2, pid2, pg2, hp2, hpa2, hn2, -, hwf2, h162, -⟩ :=
    rRoute_last v bv pp kb _ _ hok.2.1 hrt
  have he2 := (List.append_inj' hp2 rfl).2
  simp only [List.cons.injEq, and_true] at he2
  subst he2
  have hpg : pg2 = pg := rPageAt_det v bv pp pid2 pid _ pg2 pg hpa2 hpa
  rw [hpg] at hwf2 h162
  have hlf : rLfAt v bv pp pid e pg (pageSeekIdx pg kb) :=
    ⟨hpa, hn2, hfl, (pageSeekIdx_le pg kb).1, hidx⟩
  have hsl := rPosAt_last _ _ _ hp0 e pid pg _ (by simp) hlf
  ihave %Hsl2 := ownSlice_len _ _ _ $$ Hs
  have hidx2 : sint.Z (stk'.len - W64 1) = (els'.length : Int) := by
    have h1 := Hsl2.1; have h2 := Hsl2.2
    rw [show sint.nat stk'.len = (sint.Z stk'.len).toNat from rfl] at h1
    simp only [List.length_append, List.length_singleton] at h1; word
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (stk'.len - W64 1) ∧ sint.Z (stk'.len - W64 1) < sint.Z stk'.len by
    rw [hidx2]; constructor <;> word)]
  icases ownSlice_elem_acc (sint.Z (stk'.len - W64 1)) e _ _ (els' ++ [e]) (by omega)
    (by rw [hidx2]; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx2]
  wp_auto
  wp_method_call; wp_call
  wp_auto
  rw [hlf.2.1]
  wp_auto
  icases rd_hdr_acc K tx .loan q T v b DFrac.discard bv ibp pp pid e.page' pg hlf.1 h162 $$ [Hk]
    with ⟨%dqh, Hh, Hhb⟩
  · iframe; unfold rBktP; iframe #
  obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
  have hcz : uint.Z hd.count' = (pageCount pg : Int) := by unfold pageCount; rw [hH]
  have hcL := pageCount_lt pg
  rw [hH]
  wp_apply hCnt e.page' hd dqh $$ [Hh] as Hh
  · iexact Hh
  ihave Hkb := Hhb $$ Hh
  icases Hkb with ⟨Hk, -⟩
  ihave Hs := Hsback $$ He
  rw [show (els' ++ [e]).set (↑els'.length : Int).toNat e = els' ++ [e] by simp]
  unfold keyR
  have hix : sint.Z e.index' = (pageSeekIdx pg kb : Int) := by
    rw [hidx]; have := (pageSeekIdx_le pg kb).1; word
  have hcz' : sint.Z (W64 (uint.Z hd.count')) = (pageCount pg : Int) := by rw [hcz]; word
  try wp_auto
  by_cases hlt : pageSeekIdx pg kb < pageCount pg
  · -- on an entry
    have hc : ¬ (sint.Z (W64 (uint.Z hd.count')) ≤ sint.Z e.index') := by rw [hcz', hix]; omega
    rw [decide_eq_false hc]
    rw [if_pos hlt] at hsl
    subst hsl
    have hent := rPosAt_ent' _ _ _ hp0 (by omega) e pid pg _ (by simp) hlf
    icases rKV_curAt γ tx r v bv es (seekIdx es kb) pg (pageSeekIdx pg kb) k vl fl hfacts.2.2.1
      hent $$ [Hkv] with ⟨#Hca, %Hfl⟩
    · iframe #; iexact Hkv
    have hes' : es[seekIdx es kb]? = some (leafKey pg (pageSeekIdx pg kb),
        leafValue pg (pageSeekIdx pg kb)) := by
      have h := rEnts_get v bv _ pg _ hent; rw [← hfacts.2.2.1] at h; exact h
    ihave %Hkn := curAt_some_key γ tx es (seekIdx es kb) k vl _ hes' $$ Hca
    have hflb : fl &&& W32 1 = W32 0 := by
      obtain ⟨hpgm, -⟩ := rEnts_mem v bv _ pg _ hent
      have := hfacts.2.2.2 pg hpgm _ hlt
      unfold leafFlags at this; rw [← Hfl] at this; exact (w32_and_one fl).2 this
    wp_auto
    rw [decide_eq_false Hkn]
    wp_auto
    rw [decide_eq_true hflb]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    ihave Hfin := Hcl $$ %stk' %(els' ++ [e]) %(some (seekIdx es kb)) Hk Hc Hs Hcap
    ihave Hfin := Hfin $$ []
    · ipureintro; exact Or.inl ⟨_, hp0, fun h => by omega⟩
    icases Hfin with ⟨Ht, Hc⟩
    iframe; iframe #
  · -- past the leaf's end: `next`
    have hc : sint.Z (W64 (uint.Z hd.count')) ≤ sint.Z e.index' := by
      rw [hcz', hix]; have := (pageSeekIdx_le pg kb).1; omega
    rw [decide_eq_true hc]
    rw [if_neg hlt] at hsl
    subst hsl
    wp_auto
    wp_apply hnx K tx .loan q T v b DFrac.discard bv ibp pp c stk' (els' ++ [e]) (seekIdx es kb)
      (seekIdx es kb) hok hp0 $$ [Hk Hc Hs Hcap]
      as %k2 %vl2 %fl2 ⟨%stk3, %els3, Hk, -, Hc, Hs, Hcap, Hcur, -, %Hsame⟩
    · iframe; unfold rBktP; iframe #
    icases rCurKV_pub γ tx r v bv pp els3 (seekIdx es kb) k2 vl2 fl2 es hfacts $$ [Hcur] with
      ⟨#Hca, %Hfp⟩
    · iframe #; iexact Hcur
    obtain ⟨hfl2, hp3⟩ := Hfp
    have hcp : rCurPos v bv pp els3 (some (seekIdx es kb)) := by
      rcases hp3 with h | ⟨hj, -⟩
      · exact Or.inl ⟨_, h, fun h => by omega⟩
      · have he := Hsame (by omega)
        subst he
        exact Or.inl ⟨_, hp0, fun _ => by omega⟩
    try wp_auto
    by_cases hk : k2 = slice.nil
    · subst hk
      ihave %Hv := curAt_nil_key γ tx es _ vl2 $$ Hca
      subst Hv
      try rw [decide_eq_true (rfl : (slice.nil : GoSlice) = slice.nil)]
      wp_auto
      iapply HΦ
      ihave Hfin := Hcl $$ %stk3 %els3 %(some (seekIdx es kb)) Hk Hc Hs Hcap
      ihave Hfin := Hfin $$ []
      · ipureintro; exact hcp
      icases Hfin with ⟨Ht, Hc⟩
      iframe; iframe #
    · rw [decide_eq_false hk]
      wp_auto
      rw [decide_eq_true hfl2]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      ihave Hfin := Hcl $$ %stk3 %els3 %(some (seekIdx es kb)) Hk Hc Hs Hcap
      ihave Hfin := Hfin $$ []
      · ipureintro; exact hcp
      icases Hfin with ⟨Ht, Hc⟩
      iframe; iframe #

/-- **A writer's `Seek`** (U6aa): `Read/PubWSeek`'s, over `seek_w`/`next_w`; `gensOK`'s third
clause by `gensOK_handle_bktLoc` and the cursor's writer facts by `wrCurFacts_of` (both OPEN). -/
theorem Cursor.Seek.wp_writer [HasExt osFsExt]
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hseekw : Cursor.seek_w.specQ (GF := GF) (hG := hG))
    (hnxw : Cursor.next_w.specQ (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (key : GoSlice) (kb : GoString) (dk : DFrac)
    (hrw : T.rw = true) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos ∗ key ↦*{dk} kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Seek")) (Val #key))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗ key ↦*{dk} kb ∗
      boltCur tx γ c T es (some (seekIdx es kb)) ∗ curAt tx γ es (seekIdx es kb) k v }} :=
  Cursor.Seek.wp_writerW hA hseekw hnxw hCnt tx c γ q T es pos key kb dk hrw
    (gensOK_handle_bktLoc T)
    (fun X hok hg hwr hcur hbase => wrCurFacts_of T X hok hg hwr hcur hbase)

theorem Cursor.Seek.wp_proof
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hseek : ∀ [HasExt osFsExt], Cursor.seek_r.spec (GF := GF) (hG := hG))
    (hnx : ∀ [HasExt osFsExt], Cursor.next_r.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hseekw : ∀ [HasExt osFsExt], Cursor.seek_w.specQ (GF := GF) (hG := hG))
    (hnxw : ∀ [HasExt osFsExt], Cursor.next_w.specQ (GF := GF) (hG := hG)) :
    Cursor.Seek.spec (GF := GF) (hG := hG) := by
  intro _ tx c γ q T es pos key kb dk
  by_cases hrw : T.rw = true
  · exact Cursor.Seek.wp_writer hA hseekw hnxw hCnt tx c γ q T es pos key kb dk hrw
  · exact Cursor.Seek.wp_reader hA hseek hnx hCnt tx c γ q T es pos key kb dk
      (Bool.eq_false_iff.2 hrw)

end proof

end bbolt
end EtcdGrove
end Perennial
