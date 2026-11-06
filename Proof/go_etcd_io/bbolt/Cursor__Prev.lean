/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__Prev.lean` (U6h, `notes/bbolt-proof-plan.md`): the
triple is for readers only (`⌜T.rw = false⌝`): `prev` (`Cursor.prev_r`), its result as `curAt`
(`rKV_curAt`; a top-level bucket's entries are plain).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__Prev
public import Spec.go_etcd_io.bbolt.Cursor__prev_r
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Proof.go_etcd_io.bbolt.Read.PubR
public import Proof.go_etcd_io.bbolt.Txn.RdInit
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

theorem Cursor.Prev.wp_proof
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hprev : ∀ [HasExt osFsExt], Cursor.prev_r.spec (GF := GF) (hG := hG)) :
    Cursor.Prev.spec (GF := GF) (hG := hG) := by
  intro _ tx c γ q T es pos
  wp_start as ⟨Ht, Hc, %hro⟩
  unfold boltTx boltCur
  icases rdCur_open _ _ tx c q T es pos hro $$ [Ht Hc] with
    ⟨%K, %v, %r, %b, %stk, %els, %bv, %ibp, %pp, Hk, #Hb, Hc, Hs, Hcap, #Hreg, #Hvo, %Hf, Hcl⟩
  · iframe
  obtain ⟨-, hfacts, hpos⟩ := Hf
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
  wp_apply hprev K tx .loan q T v b DFrac.discard bv ibp pp c stk els pos hfacts.2.1 hpos
    $$ [Hk Hc Hs Hcap] as %k %vl %fl ⟨%stk', %els', Hk, -, Hc, Hs, Hcap, Hpost⟩
  · iframe; unfold rBktP; iframe #
  obtain ⟨-, -, hes, hplain⟩ := hfacts
  match pos with
  | none =>
    unfold rPrevPost
    icases Hpost with %Hp
    obtain ⟨rfl, rfl, rfl, hel⟩ := Hp
    try wp_auto
    try rw [decide_eq_true (show (W32 0 : w32) &&& W32 1 = W32 0 by decide)]
    try simp only [Bool.not_true]
    try wp_auto
    iapply HΦ
    ihave Hfin := Hcl $$ %stk' %els' %none Hk Hc Hs Hcap
    ihave Hfin := Hfin $$ []
    · ipureintro; exact hel
    icases Hfin with ⟨Ht, Hc⟩
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  | some 0 =>
    unfold rPrevPost
    icases Hpost with %Hp
    obtain ⟨rfl, rfl, rfl, hcp⟩ := Hp
    try wp_auto
    try rw [decide_eq_true (show (W32 0 : w32) &&& W32 1 = W32 0 by decide)]
    try simp only [Bool.not_true]
    try wp_auto
    iapply HΦ
    ihave Hfin := Hcl $$ %stk' %els' %(some 0) Hk Hc Hs Hcap
    ihave Hfin := Hfin $$ []
    · ipureintro; exact hcp
    icases Hfin with ⟨Ht, Hc⟩
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  | some (i + 1) =>
    unfold rPrevPost
    icases Hpost with ⟨%pg, %idx, ⟨%hp, -, %hent⟩, Hkv⟩
    icases rKV_curAt γ tx r v bv es i pg idx k vl fl hes hent $$ [Hkv] with ⟨#Hca, %Hfl⟩
    · iframe #; iexact Hkv
    have hflb : fl &&& W32 1 = W32 0 := by
      obtain ⟨hpgm, hidx⟩ := rEnts_mem v bv i pg idx hent
      have := hplain pg hpgm idx hidx
      unfold leafFlags at this; rw [← Hfl] at this; exact (w32_and_one fl).2 this
    try wp_auto
    rw [decide_eq_true hflb]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    ihave Hfin := Hcl $$ %stk' %els' %(some i) Hk Hc Hs Hcap
    ihave Hfin := Hfin $$ []
    · ipureintro; exact Or.inl ⟨_, hp, fun h => by omega⟩
    icases Hfin with ⟨Ht, Hc⟩
    iframe; iframe #

end proof

end bbolt
end EtcdGrove
end Perennial
