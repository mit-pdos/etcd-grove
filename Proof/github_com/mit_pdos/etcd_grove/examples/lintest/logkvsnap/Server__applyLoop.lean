/-
Lean-first (no Rocq counterpart).

The proof of `(*Server).applyLoop`: the loop holds the mutex and its lock invariant
(`logkvsnapR`) between `Wait`s. Applying the entry at `applied` is the linearization point of its
writer's `Put`: the entry's pending slot (`pendSlot`) holds the writer's atomic update, which
takes the register (the caller's half of the ghost variable, agreeing with the lock
invariant's half, the value of `s.state`) to the entry's value; its result `P` goes to the
entry's done slot (`doneSlot`), where the writer collects it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Server__applyLoop
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
namespace logkvsnap

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Assumptions]

theorem Server.applyLoop.wp_proof : Server.applyLoop.spec (GF := GF) (hG := hG) := by
  intro γ s
  wp_start as #Hs
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isServer at Hs
  icases Hs with ⟨%γr, %c, #Hc, #Hcond, #Hmu⟩
  ihave #Hlocker := sync.Mutex_is_Locker (muAddr s) (logkvsnapR γ γr s) $$ Hsync Hmu
  wp_auto
  wp_apply sync.Mutex.wp_Lock (muAddr s) (logkvsnapR γ γr s) $$ [$Hmu] as ⟨Hlocked, HR⟩
  iclear HΦ
  wp_for
  wp_for
  iunfold logkvsnapR at HR
  icases HR with ⟨%sl, %rs, %a, %st, Hlog, Hsl, Hcap, Happ, Hst, Hg, Hrs, %Ha, Hdone, Hpend⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  wp_if_destruct
  · -- `s.applied < len(s.log)`: apply the entry at `applied`
    have Hlt : uint.nat a < rs.length := by
      have := of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
      simp only [List.length_map] at Hlen
      word
    have Hidx : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z sl.len := by
      have := of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
      simp only [List.length_map] at Hlen
      word
    simp only [Hidx, and_self, ite_true]
    have Hlook : (List.map Prod.fst rs)[(sint.Z a).toNat]? = some rs[uint.nat a].1 := by
      have : (sint.Z a).toNat = uint.nat a := by word
      rw [this, List.getElem?_map, List.getElem?_eq_getElem Hlt]
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
    wp_apply wp_load_slice_index sl (sint.Z a) (List.map Prod.fst rs) _ rs[uint.nat a].1
      Hidx.1 $$ [$Hsl] as Hsl
    · ipureintro; exact Hlook
    wp_for_post
    iframe
    iunfold logkvsnapR
    have Hn : uint.nat (a + W64 1) = uint.nat a + 1 := by
      simp only [List.length_map] at Hlen
      word
    iexists sl, rs, a + W64 1, rs[uint.nat a].1
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
  · -- caught up: wake the writers, then wait for more entries
    ihave HR : logkvsnapR γ γr s $$ [Hlog Hsl Hcap Happ Hst Hg Hrs Hdone Hpend]
    · iunfold logkvsnapR
      iexists sl, rs, a, st
      iframe
      ipureintro; exact Ha
    have Hd : decide (uint.Z a < uint.Z sl.len) = false := by
      cases h : decide (uint.Z a < uint.Z sl.len)
      · rfl
      · rw [h] at Hif; exact absurd rfl Hif
    simp only [Hd, Bool.false_eq_true, ite_false]
    wp_auto
    wp_apply sync.Cond.wp_Broadcast $$ [$Hcond]
    wp_apply sync.Cond.wp_Wait c (muLocker s) (iprop(sync.ownMutex (muAddr s) ∗ logkvsnapR γ γr s))
      $$ [Hlocked HR] as ⟨Hlocked, HR⟩
    · isplitr
      · iexact Hcond
      isplitr
      · iexact Hlocker
      iframe
    wp_for_post
    iframe

end proof

end logkvsnap
end lintest
end EtcdGrove
end Perennial
