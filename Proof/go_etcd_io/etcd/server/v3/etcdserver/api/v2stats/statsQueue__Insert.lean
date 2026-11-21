/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/statsQueue__Insert.lean`
(`queue.go`): under the queue's write lock (its guard), the ring's invariant `v2stats.sqOk` kept:
the new back an index, the front's `RequestStats` non-nil when the ring is full (the window of
`size` slots from `front` on), `p` stored at the new back.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.statsQueue__Insert

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section lemmas

theorem v2stats.sq_nb (bk : w64) (h1 : -1 ≤ sint.Z bk) (h2 : sint.Z bk < 200) :
    sint.Z (BitVec.srem (bk + W64 1) (W64 200)) = (sint.Z bk + 1) % 200 := by
  have ha : (bk + W64 1).toInt = sint.Z bk + 1 := by word
  have hb : (W64 200).toInt = 200 := by decide
  show (BitVec.srem (bk + W64 1) (W64 200)).toInt = _
  rw [BitVec.toInt_srem, ha, hb]
  exact Int.tmod_eq_emod_of_nonneg (by omega)

theorem v2stats.sq_incr (sz : w64) (h1 : 0 ≤ sint.Z sz) (h2 : sint.Z sz < 200) :
    sint.Z (sz + W64 1) = sint.Z sz + 1 := by
  word

theorem v2stats.sq_eq200 (sz : w64) : sz = W64 200 ↔ sint.Z sz = 200 := by
  constructor
  · intro h; subst h; rfl
  · intro h; word

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Assumptions]

/-- A load of the `i`-th slot of the ring. -/
theorem v2stats.wp_load_slot (l : Loc) (a : GoArray Loc 200) (i : Int) (hi : 0 ≤ i ∧ i < 200) :
    {{ (l ↦ a : IProp GF) }}
      (App (Val (GoInstruction (GoLoad (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.RequestStats.ty))))
        (Val #(arrayIndexRef Loc i l)))
    {{ RET #(a.arr.getD i.toNat null); l ↦ a }} := by
  iintro %Φ Ha HΦ
  obtain ⟨arr⟩ := a
  icases array_len _ _ _ _ $$ Ha with %Hlen
  have hlk : arr[i.toNat]? = some (arr.getD i.toNat null) := by
    rw [List.getElem?_eq_getElem (by omega)]
    simp [List.getD, List.getElem?_eq_getElem (show i.toNat < arr.length by omega)]
  icases array_acc _ i (DFrac.own 1) 200 ⟨arr⟩ (arr.getD i.toNat null) hi.1 hlk $$ Ha with ⟨Hv, Ha⟩
  wp_apply IntoValTyped.wp_load (t := go.GoType.PointerType
    go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.RequestStats.ty) _ _ _ $$ Hv as Hv
  iapply HΦ
  ihave Ha := Ha $$ Hv
  rw [list_set_lookup_self arr i.toNat _ hlk]
  iexact Ha

/-- A store of the `i`-th slot of the ring. -/
theorem v2stats.wp_store_slot (l : Loc) (a : GoArray Loc 200) (i : Int) (v : Loc)
    (hi : 0 ≤ i ∧ i < 200) :
    {{ (l ↦ a : IProp GF) }}
      (App (Val (GoInstruction (GoStore (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.RequestStats.ty))))
        (Val (PairV #(arrayIndexRef Loc i l) #v)))
    {{ RET #(); l ↦ (array.mk 200 (a.arr.set i.toNat v) : GoArray Loc 200) }} := by
  iintro %Φ Ha HΦ
  obtain ⟨arr⟩ := a
  icases array_len _ _ _ _ $$ Ha with %Hlen
  have hlk : arr[i.toNat]? = some (arr.getD i.toNat null) := by
    rw [List.getElem?_eq_getElem (by omega)]
    simp [List.getD, List.getElem?_eq_getElem (show i.toNat < arr.length by omega)]
  icases array_acc _ i (DFrac.own 1) 200 ⟨arr⟩ (arr.getD i.toNat null) hi.1 hlk $$ Ha with ⟨Hv, Ha⟩
  wp_apply IntoValTyped.wp_store (t := go.GoType.PointerType
    go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.RequestStats.ty) _ _ _ $$ Hv as Hv
  iapply HΦ
  iapply Ha $$ Hv

/-- A slot of the ring, from its persistent slots. -/
theorem v2stats.sqSlot_lookup (it : List Loc) (i : Nat) (hi : i < it.length) :
    ([∗list] y ∈ it, v2stats.sqSlot (GF := GF) y) ⊢ v2stats.sqSlot (it.getD i null) := by
  iintro #Hel
  ihave #Hf := BigSepL.bigSepL_forall_intro $$ Hel
  iapply Hf $$ %i %(it.getD i null)
  ipureintro
  rw [List.getElem?_eq_getElem hi]; simp [List.getD, List.getElem?_eq_getElem hi]

/-- The slots after a store of `p`. -/
theorem v2stats.sqSlot_set (it : List Loc) (i : Nat) (p : Loc)
    (rs : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.RequestStats) :
    ([∗list] y ∈ it, v2stats.sqSlot (GF := GF) y) ∗ p ↦□ rs ⊢
      [∗list] y ∈ it.set i p, v2stats.sqSlot (GF := GF) y := by
  iintro ⟨#Hel, #Hp⟩
  ihave #Hf := BigSepL.bigSepL_forall_intro $$ Hel
  iapply BigSepL.bigSepL_forall_elim
  iintro %k %y %Hk
  by_cases hk : k = i
  · subst hk
    rw [List.getElem?_set_self'] at Hk
    have hy : y = p := by
      cases h : it[k]? with
      | none => simp [h] at Hk
      | some _ => simp [h] at Hk; exact Hk.symm
    subst hy
    iunfold v2stats.sqSlot
    iright; iexists rs; iexact Hp
  · rw [List.getElem?_set_ne (Ne.symm hk)] at Hk
    iapply Hf $$ %k %y %Hk

/-- The ring's invariant after an insertion into a full ring. -/
theorem v2stats.sqOk_full (it : List Loc) (fr bk nb : w64) (p : Loc) (hlen : it.length = 200)
    (hp : p ≠ null) (hok : v2stats.sqOk it (W64 200) fr bk)
    (hnb : sint.Z nb = (sint.Z bk + 1) % 200) :
    v2stats.sqOk (it.set (sint.Z nb).toNat p) (W64 200)
      (BitVec.srem (nb + W64 1) (W64 200)) nb := by
  obtain ⟨-, -, hf0, hf1, hb0, hb1, hmod, hwin⟩ := hok
  have h200 : sint.Z (W64 200) = 200 := by decide
  rw [h200] at hmod hwin
  have hnf := v2stats.sq_nb nb (by omega) (by omega)
  refine ⟨by rw [h200]; omega, by rw [h200]; omega, by omega, by omega, by omega, by omega,
    by rw [h200, hnf]; omega, ?_⟩
  intro k hk0 hk1
  rw [h200] at hk1
  rw [hnf]
  generalize hj : ((((sint.Z nb + 1) % 200) + k) % 200).toNat = j
  have hjlt : j < 200 := by omega
  by_cases hjn : j = (sint.Z nb).toNat
  · rw [hjn, List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]; simpa using hp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hjn), ← List.getD_eq_getElem?_getD]
    have := hwin (((j : Int) - sint.Z fr) % 200) (by omega) (by omega)
    have he : ((sint.Z fr + ((j : Int) - sint.Z fr) % 200) % 200).toNat = j := by omega
    rwa [he] at this

/-- The ring's invariant after an insertion into a ring that is not full. -/
theorem v2stats.sqOk_grow (it : List Loc) (sz fr bk nb : w64) (p : Loc) (hlen : it.length = 200)
    (hp : p ≠ null) (hok : v2stats.sqOk it sz fr bk) (hsz : sint.Z sz ≠ 200)
    (hnb : sint.Z nb = (sint.Z bk + 1) % 200) :
    v2stats.sqOk (it.set (sint.Z nb).toNat p) (sz + W64 1) fr nb := by
  obtain ⟨hs0, hs1, hf0, hf1, hb0, hb1, hmod, hwin⟩ := hok
  have hinc := v2stats.sq_incr sz hs0 (by omega)
  refine ⟨by omega, by omega, hf0, hf1, by omega, by omega, by rw [hinc]; omega, ?_⟩
  intro k hk0 hk1
  rw [hinc] at hk1
  generalize hj : ((sint.Z fr + k) % 200).toNat = j
  by_cases hjn : j = (sint.Z nb).toNat
  · rw [hjn, List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]; simpa using hp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hjn), ← List.getD_eq_getElem?_getD]
    have hks : k < sint.Z sz := by omega
    have := hwin k hk0 hks
    rwa [hj] at this

set_option hygiene false in
/-- `Insert`'s common tail: `p` stored at the new back, its `Size` added. -/
local macro "sq_tail" : tactic => `(tactic| (
    have Hnb0 : 0 ≤ sint.Z nb ∧ sint.Z nb < 200 := by omega
    rw [if_pos Hnb0]
    (try wp_auto)
    wp_apply v2stats.wp_store_slot _ _ (sint.Z nb) p Hnb0 $$ Hit as Hit
    (try wp_auto)
    rw [if_pos Hnb0]
    (try wp_auto)
    wp_apply v2stats.wp_load_slot _ _ (sint.Z nb) Hnb0 $$ Hit as Hit
    have Hget : (it.set (sint.Z nb).toNat p).getD (sint.Z nb).toNat null = p := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]; rfl
    dsimp only
    rw [Hget]
    iStructNamed Hp
    (try wp_auto)
    ihave #Hel' := v2stats.sqSlot_set it (sint.Z nb).toNat p rs $$ [Hel Hp]
    · iframe #))

theorem v2stats.statsQueue.Insert.wp_proof :
    v2stats.statsQueue.Insert.spec (GF := GF) (hG := hG) := by
  intro q p rs
  wp_start as ⟨#Hq, #Hp⟩
  iunfold v2stats.isStatsQueue at Hq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hq] as ⟨Hlk, HP⟩
  iunfold v2stats.sqP at HP
  icases HP with ⟨%x, HB⟩
  obtain ⟨⟨it⟩, sz, fr, bk, tot⟩ := x
  iunfold v2stats.sqBody at HB
  icases HB with ⟨Hit, Hsz, Hfr, Hbk, Htot, %Hok, #Hel⟩
  simp only at Hok
  obtain ⟨Hs0, Hs1, Hf0, Hf1, Hb0, Hb1, Hmod, Hwin⟩ := Hok
  icases array_len _ _ _ _ $$ Hit with %Hlen
  ihave %Hpnn := typedPointsto_not_null $$ Hp
  (try wp_auto)
  have Hnb := v2stats.sq_nb bk Hb0 Hb1
  generalize hnb : BitVec.srem (bk + W64 1) (W64 200) = nb at *
  have Hlen' : it.length = 200 := by omega
  wp_if_destruct
  · rw [if_pos ⟨Hf0, Hf1⟩]
    (try wp_auto)
    wp_apply v2stats.wp_load_slot _ _ (sint.Z fr) ⟨Hf0, Hf1⟩ $$ [$Hit] as Hit
    have hy : it.getD (sint.Z fr).toNat null ≠ null := by
      have h := Hwin 0 (by omega) (by decide)
      have he : ((sint.Z fr + 0) % 200).toNat = (sint.Z fr).toNat := by omega
      rwa [he] at h
    ihave #Hs := v2stats.sqSlot_lookup it (sint.Z fr).toNat (by omega) $$ Hel
    iunfold v2stats.sqSlot at Hs
    icases Hs with (%Hnull | ⟨%rs', #Hrs⟩)
    · exact absurd Hnull hy
    dsimp only
    iStructNamed Hrs
    (try wp_auto)
    sq_tail
    have Hok' := v2stats.sqOk_full it fr bk nb p Hlen' Hpnn
      ⟨Hs0, Hs1, Hf0, Hf1, Hb0, Hb1, Hmod, Hwin⟩ Hnb
    wp_apply +noauto sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hsz Hbk Hfr Hit Htot]
    · inext
      iunfold v2stats.sqP
      iexists (⟨it.set (sint.Z nb).toNat p⟩, W64 200, BitVec.srem (nb + W64 1) (W64 200), nb,
        tot - rs'.Size' + rs.Size')
      iunfold v2stats.sqBody
      iframe Hsz Hbk Hfr Hit Htot Hel'
      ipureintro; exact Hok'
    (try wp_auto)
    iapply HΦ
    itrivial
  · (try wp_auto)
    sq_tail
    have Hsz' : sint.Z sz ≠ 200 := fun h => Hif ((v2stats.sq_eq200 sz).2 h)
    have Hok' := v2stats.sqOk_grow it sz fr bk nb p Hlen' Hpnn
      ⟨Hs0, Hs1, Hf0, Hf1, Hb0, Hb1, Hmod, Hwin⟩ Hsz' Hnb
    wp_apply +noauto sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hsz Hbk Hfr Hit Htot]
    · inext
      iunfold v2stats.sqP
      iexists (⟨it.set (sint.Z nb).toNat p⟩, sz + W64 1, fr, nb, tot + rs.Size')
      iunfold v2stats.sqBody
      iframe Hsz Hbk Hfr Hit Htot Hel'
      ipureintro; exact Hok'
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
