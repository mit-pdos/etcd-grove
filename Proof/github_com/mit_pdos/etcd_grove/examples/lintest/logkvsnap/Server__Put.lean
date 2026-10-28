/-
Lean-first (no Rocq counterpart).

The proof of `(*Server).Put`: under the mutex, the write's entry is appended to the log, and
its pending slot (`pendSlot`) gets the caller's atomic update, with the update's result `P`
(`True -∗ Φ #()`) saved under a fresh name and a fresh ticket kept by `Put`; the request is
recorded in the requests' monotone list, `Put` keeping a witness of its index. The apply
goroutine fires the update when it applies the entry (`applyLoop`, the linearization point).
`Put` waits on the condition variable until `applied` passes the entry; the entry's slot is then
done (`doneSlot`): its result is there (the ticket is `Put`'s, so it was not taken), it is `P`
(the saved proposition, `▷ (P' ≡ P)`), and `Put` takes it, leaving its ticket. The later from the
saved proposition's agreement goes with `Unlock`'s step.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Server__Put
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
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

theorem Server.Put.wp_proof : Server.Put.spec (GF := GF) (hG := hG) := by
  intro γ s v
  iintro %Φ ⟨#Hpkg, #Hs⟩ HAU
  simp only [LawfulSet.diff_empty]
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isServer at Hs
  icases Hs with ⟨%γr, %c, #Hc, #Hcond, #Hmu⟩
  ihave #Hlocker := sync.Mutex_is_Locker (muAddr s) (logkvsnapR γ γr s) $$ Hsync Hmu
  wp_method_call
  wp_call
  wp_auto
  wp_apply sync.Mutex.wp_Lock (muAddr s) (logkvsnapR γ γr s) $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold logkvsnapR at HR
  icases HR with ⟨%sl, %rs, %a, %st, Hlog, Hsl, Hcap, Happ, Hst, Hg, Hrs, %Ha, Hdone, Hpend⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_apply wp_slice_literal (V := GoString) [v]
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
  ihave %Hlen' := ownSlice_len $$ Hsl
  -- the request: the saved postcondition, the ticket, and its index in the requests' list
  imod saved_prop_alloc (GF := GF) iprop(True -∗ Φ #()) DFrac.discard DFrac.valid_discard
    with ⟨%γP, #HP⟩
  imod token_alloc (GF := GF) with ⟨%γt, Htok⟩
  let r : Req := (v, γP, γt)
  imod monoListAuthOwn_update_app (A := Req) [r] $$ Hrs with ⟨Hrs, #Hlb⟩
  ihave #Hidx := monoListIdxOwn_get (GF := GF) rs.length r (by simp) $$ Hlb
  ihave HR : logkvsnapR γ γr s $$ [Hlog Hsl Hcap Happ Hst Hg Hrs Hdone Hpend HAU]
  · iunfold logkvsnapR
    iexists sl', rs ++ [r], a, st
    rw [List.map_append, List.take_append_of_le_length Ha, List.drop_append_of_le_length Ha]
    iframe
    isplitr
    · ipureintro; simp only [List.length_append]; omega
    iapply BigSepL.bigSepL_singleton.2
    iunfold pendSlot
    iexists iprop(True -∗ Φ #())
    iframe HP
    iunfold regAu
    iexact HAU
  wp_apply sync.Cond.wp_Broadcast $$ [$Hcond]
  wp_for
  iunfold logkvsnapR at HR
  icases HR with ⟨%sl1, %rs1, %a1, %st1, Hlog, Hsl, Hcap, Happ, Hst, Hg, Hrs, %Ha1, Hdone, Hpend⟩
  wp_auto
  wp_if_destruct
  · -- not applied yet: wait
    ihave HR : logkvsnapR γ γr s $$ [Hlog Hsl Hcap Happ Hst Hg Hrs Hdone Hpend]
    · iunfold logkvsnapR
      iexists sl1, rs1, a1, st1
      iframe
      ipureintro; exact Ha1
    wp_apply sync.Cond.wp_Wait c (muLocker s) (iprop(sync.ownMutex (muAddr s) ∗ logkvsnapR γ γr s))
      $$ [Hlocked HR] as ⟨Hlocked, HR⟩
    · isplitr
      · iexact Hcond
      isplitr
      · iexact Hlocker
      iframe
    wp_for_post
    iframe
  · -- applied: collect the result
    have Hd : decide (uint.Z a1 < uint.Z sl'.len) = false := by
      cases h : decide (uint.Z a1 < uint.Z sl'.len)
      · rfl
      · rw [h] at Hif; exact absurd rfl Hif
    have Hge : rs.length < uint.nat a1 := by
      have := of_decide_eq_false Hd
      simp only [List.length_append, List.length_map, List.length_singleton] at Hlen'
      word
    simp only [Hd, Bool.false_eq_true, ite_false]
    icases mono_list_auth_idx_lookup γr 1 rs1 rs.length r $$ Hrs Hidx with %Hlook
    have Htk : (rs1.take (uint.nat a1))[rs.length]? = some r := by
      rw [List.getElem?_take]
      simp only [Hge, ite_true, Hlook]
    have Hset : (rs1.take (uint.nat a1)).set rs.length r = rs1.take (uint.nat a1) := by
      obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp Htk
      rw [← he]
      exact List.set_getElem_self hi
    ihave ⟨Hslot, Hback⟩ := (BigSepL.bigSepL_lookup_acc Htk).1 $$ Hdone
    iunfold doneSlot at Hslot
    icases Hslot with ⟨%P', #HP', HPor⟩
    icases HPor with (HPr | Htok')
    · ihave #Heq := saved_prop_agree γP DFrac.discard DFrac.discard P' iprop(True -∗ Φ #())
        $$ HP' HP
      ihave Hdone := Hback $$ %r [Htok]
      · iunfold doneSlot
        iexists P'
        iframe HP'
        iright
        iexact Htok
      rw [Hset]
      ihave HA : ▷ (True -∗ Φ #()) $$ [HPr]
      · inext
        ihave Hiff := internalEq_iff _ _ $$ Heq
        icases Hiff with ⟨Hiff, -⟩
        iapply Hiff $$ HPr
      ihave HR : logkvsnapR γ γr s $$ [Hlog Hsl Hcap Happ Hst Hg Hrs Hdone Hpend]
      · iunfold logkvsnapR
        iexists sl1, rs1, a1, st1
        iframe
        ipureintro; exact Ha1
      wp_auto
      wp_apply sync.Mutex.wp_Unlock (muAddr s) (logkvsnapR γ γr s) $$ [$Hmu $Hlocked HR]
      · inext; iexact HR
      iapply HA
      itrivial
    · iexfalso
      iapply token_exclusive $$ Htok Htok'

end proof

end logkvsnap
end lintest
end EtcdGrove
end Perennial
