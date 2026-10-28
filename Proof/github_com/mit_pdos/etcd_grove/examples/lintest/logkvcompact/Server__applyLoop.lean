/-
Lean-first (no Rocq counterpart).

The proof of `(*Server).applyLoop`: the loop holds the mutex and its lock invariant
(`logkvcompactR`) between `Wait`s. Applying the entry at `applied` is the linearization point of its
writer's `Put`: the entry's pending slot (`pendSlot`) holds the writer's atomic update, which
takes the register (the caller's half of the ghost variable, agreeing with the lock
invariant's half, the value of `s.state`) to the entry's value; its result `P` goes to the
entry's done slot (`doneSlot`), where the writer collects it. The log holds the requests from
`start` on, so the entry at `applied` is at `applied - start`; caught up (`applied = |rs|`), the
loop drops the applied prefix (`ownSlice_slice_with_cap`: the rest of the backing array becomes
the new slice's capacity) and sets `start` to `applied`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Server__applyLoop
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Cond__Wait
public import Perennial.Spec.sync.Cond__Broadcast
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.Results

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvcompact

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Assumptions]

theorem Server.applyLoop.wp_proof : Server.applyLoop.spec (GF := GF) (hG := hG) := by
  intro γ s
  wp_start as #Hs
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isServer at Hs
  icases Hs with ⟨%γr, %c, %Hbnd, #Hc, #Hcond, #Hmu⟩
  ihave #Hlocker := sync.Mutex_is_Locker (muAddr s) (logkvcompactR γ γr s) $$ Hsync Hmu
  wp_auto
  wp_apply sync.Mutex.wp_Lock (muAddr s) (logkvcompactR γ γr s) $$ [$Hmu] as ⟨Hlocked, HR⟩
  iclear HΦ
  wp_for
  wp_for
  iunfold logkvcompactR at HR
  icases HR with ⟨%sl, %rs, %b, %a, %st, Hlog, Hsl, Hcap, Hstart, Happ, Hst, Hg, Hrs, Hrc, %Ha,
    Hdone, Hpend⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  have Hsum : uint.nat (b + sl.len) = rs.length := by
    simp only [List.length_map, List.length_drop] at Hlen
    word
  wp_auto
  wp_if_destruct
  · -- `s.applied < s.start + len(s.log)`: apply the entry at `applied`
    have Hlt : uint.nat a < rs.length := by
      have := of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
      word
    have Hidx : 0 ≤ sint.Z (a - b) ∧ sint.Z (a - b) < sint.Z sl.len := by
      simp only [List.length_map, List.length_drop] at Hlen
      word
    simp only [Hidx, and_self, ite_true]
    have Hlook : (List.map Prod.fst (rs.drop (uint.nat b)))[(sint.Z (a - b)).toNat]? =
        some rs[uint.nat a].1 := by
      have : (sint.Z (a - b)).toNat = uint.nat a - uint.nat b := by
        simp only [List.length_map, List.length_drop] at Hlen
        word
      rw [this, List.getElem?_map, List.getElem?_drop,
        show uint.nat b + (uint.nat a - uint.nat b) = uint.nat a by omega,
        List.getElem?_eq_getElem Hlt]
      rfl
    -- the linearization point of the entry's `Put`
    rw [List.drop_eq_getElem_cons Hlt]
    ihave ⟨Hslot, Hpend⟩ := (BigSepL.bigSepL_cons).1 $$ Hpend
    iunfold pendSlot at Hslot
    icases Hslot with ⟨%P, #HP, Hau⟩
    iunfold regAu at Hau
    iapply fupd_wp
    imod Hau with ⟨%x, Hx, Hclose⟩
    iunfold regState at Hx
    icombine Hg Hx gives %Hagree
    obtain ⟨_, Heq⟩ := Hagree
    subst Heq
    imod ghostVar_update_halves rs[uint.nat a].1 γ _ _ $$ Hg Hx with ⟨Hg, Hx⟩
    imod Hclose $$ [Hx] with HPr
    · iunfold regState; iexact Hx
    imodintro
    wp_apply wp_load_slice_index sl (sint.Z (a - b)) (List.map Prod.fst (rs.drop (uint.nat b))) _
      rs[uint.nat a].1
      Hidx.1 $$ [$Hsl] as Hsl
    · ipureintro; exact Hlook
    wp_for_post
    iframe
    iunfold logkvcompactR
    have Hn : uint.nat (a + W64 1) = uint.nat a + 1 := by word
    iexists sl, rs, b, a + W64 1, rs[uint.nat a].1
    rw [Hn, List.take_add_one, List.getElem?_eq_getElem Hlt]
    simp only [Option.toList_some]
    iframe
    isplitr
    · ipureintro; omega
    iapply BigSepL.bigSepL_singleton.2
    iunfold doneSlot
    iexists P
    iframe HP
    ileft
    iexact HPr
  · -- caught up: compact the log, wake the writers, then wait for more entries
    have Hd : decide (uint.Z a < uint.Z (b + sl.len)) = false := by
      cases h : decide (uint.Z a < uint.Z (b + sl.len))
      · rfl
      · rw [h] at Hif; exact absurd rfl Hif
    have Hab : uint.nat a = rs.length := by
      have := of_decide_eq_false Hd
      word
    simp only [Hd, Bool.false_eq_true, ite_false]
    have Hk : sint.Z (a - b) = sint.Z sl.len := by
      simp only [List.length_map, List.length_drop] at Hlen
      word
    ihave %Hwf := ownSliceCap_wf $$ Hcap
    wp_auto
    simp only [Hk, Int.le_refl, _root_.and_true, Hlen.2, Hwf.2, ite_true]
    ihave ⟨-, Hsl, Hcap⟩ := ownSlice_slice_with_cap (a - b) sl.len sl _ ⟨by omega, by omega, Int.le_refl _⟩
      $$ [Hsl Hcap]
    · iframe
    wp_auto
    ihave HR : logkvcompactR γ γr s $$ [Hlog Hsl Hcap Hstart Happ Hst Hg Hrs Hrc Hdone Hpend]
    · iunfold logkvcompactR
      iexists _, rs, a, a, st
      have Hnil : subslice (sint.nat (a - b)) (sint.nat sl.len)
          (List.map Prod.fst (rs.drop (uint.nat b))) = List.map Prod.fst (rs.drop (uint.nat a)) := by
        have Hn : sint.nat (a - b) = sint.nat sl.len := by word
        rw [Hab, List.drop_length, List.map_nil, subslice_def, Hn]
        apply List.drop_eq_nil_of_le
        rw [List.length_take]
        omega
      rw [← Hnil]
      iframe
      ipureintro; omega
    wp_apply sync.Cond.wp_Broadcast $$ [$Hcond]
    wp_apply sync.Cond.wp_Wait c (muLocker s) (iprop(sync.ownMutex (muAddr s) ∗ logkvcompactR γ γr s))
      $$ [Hlocked HR] as ⟨Hlocked, HR⟩
    · isplitr
      · iexact Hcond
      isplitr
      · iexact Hlocker
      iframe
    wp_for_post
    iframe

end proof

end logkvcompact
end lintest
end EtcdGrove
end Perennial
