/- Lean-first (no Rocq counterpart). The proof of `runner.writeSub`: proved.

The outline: by `s.kind`: a put is `pending.put` and `tw.Put` (`Txn.Put.contract`, the
lease attached through the owner's part), checked at the pending revision; a delete is
`pending.del` and `tw.DeleteRange` (`Txn.DeleteRange.contract`), its count and revision checked
(`delKeys_eq_match`); a read is `writeRange`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeSub
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pending__put
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pending__del
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriteSubLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.writeSub.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (wp_put : pending.put.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_del : pending.del.spec (GF := GF) (hG := hG))
    (wp_writeRange : runner.writeRange.spec (GF := GF) (hG := hG)) :
    runner.writeSub.spec (GF := GF) (hG := hG) := by
  intro x ks h γh mp γk tw trace te σ pend Hs p P sv sm L hok hlen hrev hreach hLok h63 hpl hfresh hput
  wp_start as ⟨Hks, HH, Hrd, Hlb, Hcmp, Htx, Htrc, Hp, Hs, Hlo⟩
  icases (persistent_entails_right (hsh.2.2.1 tw γk trace (.write σ pend))) $$ Htx with ⟨%Hsht, Htx⟩
  obtain ⟨tty, tv, rfl, -, -, -, hPutC, hDelC, -, -⟩ := Hsht
  obtain ⟨hl2, hc1, hcr⟩ := reach_bounds σ hreach
  have hne : σ.log ≠ [] := by intro h0; rw [h0] at hl2; simp at hl2
  have hPrev := pendOk_rev' hok
  iunfold runnerKeys at Hks
  icases Hks with ⟨%keys, #Hkeys, #Hksl, %Hsorted, %Hksne⟩
  iunfold subIs at Hs
  icases Hs with ⟨#Hk, #He, #Hq, %Hsv⟩
  obtain ⟨hkind, hendNil, hval, hlease⟩ := Hsv
  wp_auto
  by_cases hk0 : sm.kind = W64 0
  · -- a put
    rw [hkind]
    simp only [hk0, _root_.decide_true]
    obtain ⟨hkks, hlL⟩ := hput hk0
    (try wp_auto)
    wp_apply wp_bytes_to_string sv.key' sm.key DFrac.discard $$ [$Hk] as -
    (try wp_auto)
    rw [hval, hlease]
    wp_apply wp_put p P sm.key sm.val sm.lease $$ [$Hp] as Hp
    (try wp_auto)
    wp_apply wp_string_to_bytes as %vs ⟨Hvs, -⟩
    imod ownSlice_persist $$ Hvs with #Hvs
    ihave #Hvs' : vs ↦*□ sm.val $$ []
    · rw [← hval]; iexact Hvs
    (try wp_auto)
    try rw [hlease]
    -- SPEC GAP (frozen spec): `Txn.Put` needs `|key| < 2 ^ 63 - 1`; writeSub's pre bounds the key
    -- only through its slice (`|key| ≤ 2 ^ 63 - 1`) and `sm.key ∈ ks`, with no length bound on `ks`
    -- (`writerCtx` has one, writeSub does not take it). `notes/mvccfull-prove-writer.md`.
    have hklen : (sm.key.length : Int) < 2 ^ 63 - 1 := by
      sorry
    wp_apply (hPutC γk trace te σ pend sv.key' vs sm.key sm.val sm.lease L)
      $$ [$Htx $Htrc $Hk $Hvs' $Hlo] as ⟨Htx, Htrc, Hlo⟩
    · ipureintro; exact ⟨hklen, hlL⟩
    (try wp_auto)
    iunfold ownPending at Hp
    icases Hp with ⟨%pv, Hpv, %Hprev, Hpst, Hpch, Hpcap⟩
    (try wp_auto)
    wp_apply wp_check
    · ipureintro
      simp only [PendM.put] at Hprev
      rw [Hprev, hPrev, hlen]; simp
    (try wp_auto)
    iapply HΦ
    have hsub : subStep ks P sm = P.put sm.key sm.val sm.lease := by
      unfold subStep; simp [hk0]
    rw [hsub]
    iframe
    isplitr
    · ipureintro
      exact ⟨pendOk_put' ks σ Hs pend P hok hlen _ _ _ hkks,
        logOk_put' σ.log pend hLok hne (by omega) _ _ _,
        by have := List.length_pos_iff.2 Hksne; simp; omega⟩
    · iunfold ownPending; iexists pv; iframe; ipureintro; exact Hprev
  · rw [hkind]
    simp only [hk0, _root_.decide_false]
    (try wp_auto)
    by_cases hk1 : sm.kind = W64 1
    · -- a range delete
      simp only [hk1, _root_.decide_true]
      (try wp_auto)
      wp_apply wp_del p P keys ks DFrac.discard sv.key' sv.end' sm.key sm.e DFrac.discard
        DFrac.discard $$ [$Hp $Hksl $Hk $He] as ⟨Hp, -, -, -⟩
      (try wp_auto)
      wp_apply (hDelC γk trace σ pend sv.key' sv.end' sm.key sm.e L) $$ [$Htx $Hk $He $Hlo]
        as %n2 %rev ⟨Htx, Hlo, %Hnr, %Hlwf⟩
      have hks := delKeys_eq_match ks Hsorted σ.log pend hne hLok (decide (sv.end' = slice.nil))
        sm.key sm.e P.st hok.2
      have hok' := pendOk_del' ks σ Hs pend P hok (decide (sv.end' = slice.nil)) sm.key sm.e hks
      have hLog' : txn.LogOk (σ.log ++ [pend ++
          (delKeys σ.log pend (decide (sv.end' = slice.nil)) sm.key sm.e).map Change.del]) :=
        txn.LogOk.of_cert ⟨Hlwf.1, by simp; omega, Hlwf.2⟩ (by simp)
      have hdl : ((delKeys σ.log pend (decide (sv.end' = slice.nil)) sm.key sm.e).map
          Change.del).length ≤ ks.length := by
        rw [List.length_map, hks]; exact matchKeys_length_le' _ _ _ _ _
      rw [hks] at Hnr
      obtain ⟨rfl, rfl⟩ := Hnr
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; simp
      (try wp_auto)
      iunfold ownPending at Hp
      icases Hp with ⟨%pv, Hpv, %Hprev, Hpst, Hpch, Hpcap⟩
      ihave %Hcl := ownSlice_len $$ Hpch
      have hcl' := pendOk_chs_length hok'
      have hrevP : (P.del ks (decide (sv.end' = slice.nil)) sm.key sm.e).rev =
          W64 (σ.log.length : Int) := by
        rw [pendOk_rev' hok', hlen]
      rw [hrevP] at Hprev
      have hsub : subStep ks P sm = P.del ks (decide (sv.end' = slice.nil)) sm.key sm.e := by
        unfold subStep; rw [if_neg hk0, if_pos hk1, hendNil]
      (try wp_auto)
      wp_if_destruct
      · wp_apply wp_check
        · ipureintro
          have hD : pend ++ List.map Change.del
              (delKeys σ.log pend (decide (sv.end' = slice.nil)) sm.key sm.e) ≠ [] := by
            intro h0
            rw [h0] at hcl'
            have h0' : sint.Z (W64 0) = 0 := by decide
            have : sint.nat pv.changes'.len = (sint.Z pv.changes'.len).toNat := rfl
            simp only [List.length_nil] at hcl'
            omega
          rw [← hks]
          simp [Hprev, writeRev, hD]
        (try wp_auto)
        iapply HΦ
        rw [hsub]
        iframe
        isplitr
        · ipureintro; exact ⟨hok', hLog', hdl⟩
        · iunfold ownPending; iexists pv; iframe; ipureintro; rw [hrevP]; exact Hprev
      · wp_apply wp_check
        · ipureintro
          have hD : pend ++ List.map Change.del
              (delKeys σ.log pend (decide (sv.end' = slice.nil)) sm.key sm.e) = [] := by
            apply List.eq_nil_of_length_eq_zero
            have h0' : sint.Z (W64 0) = 0 := by decide
            have : sint.nat pv.changes'.len = (sint.Z pv.changes'.len).toNat := rfl
            omega
          rw [← hks]
          simp only [Hprev, writeRev, hD, ↓reduceIte, decide_eq_true_eq]
          have : ((σ.log.length - 1 : Nat) : Int) = (σ.log.length : Int) - 1 := by omega
          rw [this]; word
        (try wp_auto)
        iapply HΦ
        rw [hsub]
        iframe
        isplitr
        · ipureintro; exact ⟨hok', hLog', hdl⟩
        · iunfold ownPending; iexists pv; iframe; ipureintro; rw [hrevP]; exact Hprev
    · -- a range read
      simp only [hk1, _root_.decide_false]
      (try wp_auto)
      wp_apply (wp_writeRange x ks h γh mp γk (interface.mkOk tty tv) trace te σ pend Hs p P sv.q'
          sm.q hok hlen hrev hreach hLok h63) $$ [$Hrd $Hlb $Hcmp $Htx $Htrc $Hp $Hq HH]
        as ⟨Hrd, Hcmp, Htx, Htrc, Hp⟩
      · iframe
        iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hksne⟩
      (try wp_auto)
      iapply HΦ
      have hsub : subStep ks P sm = P := by unfold subStep; rw [if_neg hk0, if_neg hk1]
      rw [hsub]
      iframe
      iexists []
      simp only [List.append_nil]
      iframe
      ipureintro; exact ⟨hok, hLok, by simp⟩

end proof

end mvccfull
end EtcdGrove
end Perennial
