/- Lean-first (no Rocq counterpart). The proof of `writer.writeOp`: one operation of the write
transaction, at any point of it (the changes so far `pend`, their model `P`, `pendOk`):

- a put: `pending.put` and `Txn.Put` (its revision `len(σ.log)`, the pending one), `pendOk` kept by
  `stMatch_put` at the pending state (`pendOk_put'`), the read log's `LogOk` by
  `LogWf'.append_change`;
- a range delete: `pending.del`'s keys are `Txn.DeleteRange`'s (`delKeys_eq_match` at the pending
  state), its revision `writeRev` (the pending one once a change is pending, else the last);
- a range read: `Txn.Range` at the read log `σ.log ++ [pend]`, revision `writeRev`, against `view`'s
  states (`viewRev_writeRev`, `viewSt_match'`), by `checkRange`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__writeOp
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__view
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__newVal
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__genLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__intn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.pending__put
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.pending__del
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.checkRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Spec.context.TODO
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WriteLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section model
variable [GooseExts]

private theorem applyChanges_append (r : w64) (s : List EtcdKv) (a b : List Change) :
    applyChanges r s (a ++ b) = applyChanges r (applyChanges r s a) b := by
  simp only [applyChanges, List.foldl_append]

private theorem pendOk_rev' {σ : MvccState} {Hs : List HRev} {pend : List Change} {P : PendM}
    (hok : pendOk σ Hs pend P) : P.rev = W64 (Hs.length : Int) := by
  rw [hok.1]; exact pendOf_rev _ _ _

private theorem pendOk_chs_length' {σ : MvccState} {Hs : List HRev} {pend : List Change}
    {P : PendM} (hok : pendOk σ Hs pend P) : P.chs.length = pend.length := by
  rw [hok.1]; exact pendOf_chs_length _ _ _

/-- A put keeps the model, at any pending state. -/
private theorem pendOk_put' (σ : MvccState) (Hs : List HRev) (pend : List Change) (P : PendM)
    (hok : pendOk σ Hs pend P) (hlen : Hs.length = σ.log.length) (k v : GoString) (l : w64)
    (hk : k ∈ keyList) :
    pendOk σ Hs (pend ++ [.put k v l]) (P.put k v l) := by
  have hrev : P.rev = W64 (σ.log.length : Int) := by rw [pendOk_rev' hok, hlen]
  obtain ⟨hP, hst⟩ := hok
  refine ⟨by rw [pendOf_put, ← hP], ?_⟩
  have hs : (applyChanges (W64 (σ.log.length : Int)) (stateAfter σ.log) pend).Pairwise etcdKvLess := by
    rw [← stateAt_pend]; exact stateAt_sorted _ _
  have := stMatch_put P.st _ hs (W64 (σ.log.length : Int)) k v l hst hk
  rw [applyChanges_append]
  simpa only [PendM.put, hrev, applyChanges, List.foldl_cons, List.foldl_nil] using this

/-- A range delete keeps the model, at any pending state. -/
private theorem pendOk_del' (σ : MvccState) (Hs : List HRev) (pend : List Change) (P : PendM)
    (hok : pendOk σ Hs pend P) (endNil : Bool) (kk e : GoString)
    (hks : delKeys σ.log pend endNil kk e = matchKeys P.st endNil kk e) :
    pendOk σ Hs (pend ++ (delKeys σ.log pend endNil kk e).map Change.del) (P.del endNil kk e) := by
  obtain ⟨hP, hst⟩ := hok
  rw [hks]
  refine ⟨?_, ?_⟩
  · rw [PendM.del_eq_foldl, pendOf_append, ← hP]
  · rw [applyChanges_append]
    exact stMatch_delAll _ _ _ _ hst

/-- The revision a read in the transaction sees is `view`'s. -/
private theorem viewRev_writeRev (σ : MvccState) (Hs : List HRev) (pend : List Change) (P : PendM)
    (hok : pendOk σ Hs pend P) (hlen : Hs.length = σ.log.length) (h1 : 1 ≤ σ.log.length)
    (h63 : σ.log.length < 2 ^ 63) :
    viewRev P = W64 (writeRev σ.log pend : Int) := by
  have hnil : P.chs = [] ↔ pend = [] := by rw [hok.1]; exact pendOf_chs_nil_iff _ _ _
  unfold viewRev writeRev
  rw [pendOk_rev' hok, hlen]
  by_cases hp : pend = []
  · simp only [hnil.2 hp, hp, ↓reduceIte]
    rw [w64_pred _ h1 h63]
  · have hc : P.chs ≠ [] := fun h => hp (hnil.1 h)
    simp only [hc, hp, ↓reduceIte]

/-- The states a read in the transaction sees are the store's at its read log. -/
private theorem viewSt_match' (σ : MvccState) (Hs : List HRev) (pend : List Change) (P : PendM)
    (hok : pendOk σ Hs pend P) (hlen : Hs.length = σ.log.length) (h1 : 1 ≤ σ.log.length)
    (hrev : ∀ r < Hs.length, ∃ e, Hs[r]? = some e ∧ revOk σ.log Hs r e) :
    ∀ r : Nat, r ≤ writeRev σ.log pend →
      ∃ M, (viewSt Hs P)[r]? = some M ∧ stMatch M (stateAt (σ.log ++ [pend]) r) := by
  have hnil : P.chs = [] ↔ pend = [] := by rw [hok.1]; exact pendOf_chs_nil_iff _ _ _
  intro r hr
  by_cases hlt : r < Hs.length
  · obtain ⟨e, he, hok', -⟩ := hrev r hlt
    refine ⟨e.1, ?_, ?_⟩
    · unfold viewSt
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, he]; rfl
    · rw [stateAt_append_lt _ _ (by omega)]; exact hok'
  · have hp : pend ≠ [] := by
      intro hp; rw [writeRev, ite_eq_left hp] at hr; omega
    have hc : P.chs ≠ [] := fun h => hp (hnil.1 h)
    have hr' : r = Hs.length := by rw [writeRev, ite_eq_right hp] at hr; omega
    subst hr'
    refine ⟨P.st, ?_, ?_⟩
    · unfold viewSt; simp [hc]
    · rw [hlen, stateAt_pend]; exact hok.2

private theorem viewSt_length' (Hs : List HRev) (P : PendM) :
    (viewSt Hs P).length = Hs.length + (if P.chs = [] then 0 else 1) := by
  unfold viewSt; split <;> simp

/-- A put keeps the read log's `LogOk`. -/
private theorem logOk_put (L : Log) (pend : List Change) (hok : txn.LogOk (L ++ [pend]))
    (hne : L ≠ []) (hpl : pend.length + 1 < 2 ^ 63) (k v : GoString) (l : w64) :
    txn.LogOk (L ++ [pend ++ [.put k v l]]) := by
  refine txn.LogOk.of_cert ⟨LogWf'.append_change (LogWf'.of_wf hok.wf) hne (.put k v l)
    (fun _ h => by cases h), ?_, ?_⟩ (by simp)
  · have := hok.len; simpa using this
  · intro cs hcs
    simp only [List.mem_append, List.mem_singleton] at hcs
    rcases hcs with h | h
    · exact hok.cs cs (by simp [h])
    · subst h; simp; omega

/-- The tester's keys present and in a range: at most its six keys. -/
private theorem matchKeys_length_le (M : GMap GoString kvRec) (endNil : Bool) (kk e : GoString) :
    (matchKeys M endNil kk e).length ≤ 6 := by
  unfold matchKeys; exact Nat.le_trans (List.length_filter_le _ _) (by decide)

end model

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem writer.writeOp.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_intn : rng.intn.spec (GF := GF) (hG := hG))
    (wp_genKey : rng.genKey.spec (GF := GF) (hG := hG))
    (wp_genEnd : rng.genEnd.spec (GF := GF) (hG := hG))
    (wp_genRange : rng.genRange.spec (GF := GF) (hG := hG))
    (wp_newVal : writer.newVal.spec (GF := GF) (hG := hG))
    (wp_genLease : writer.genLease.spec (GF := GF) (hG := hG))
    (wp_put : pending.put.spec (GF := GF) (hG := hG))
    (wp_del : pending.del.spec (GF := GF) (hG := hG))
    (wp_view : writer.view.spec (GF := GF) (hG := hG))
    (wp_checkRange : checkRange.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG)) :
    writer.writeOp.spec (GF := GF) (hG := hG) := by
  intro w wv γ B f σ Hs L tw trace te p P pend n hok hLok hcrev hrev1 hpl hn0 hn1
  wp_start as ⟨Hctx, Hrd, Hidle, Htx, Htrc, Hp, ⟨%g, Hg⟩, ⟨%Lm, Hlm, %HLm⟩, Hlo, Hvals⟩
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hpkg, #Hmv, #Htu, #Hw, #Hinv, -, -, -, -⟩
  ihave #Hw2 := Hw
  iunfold writerRO at Hw2
  icases Hw2 with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  icases (persistent_entails_right (hsh.2.2.1 tw γ.kv trace (.write σ pend))) $$ Htx with ⟨%Hsht, Htx⟩
  obtain ⟨tty, tv, rfl, -, -, hRangeC, hPutC, hDelC, -, -⟩ := Hsht
  iunfold writerIdle at Hidle
  icases Hidle with ⟨Hgσ, HW, Hpv, %Hid⟩
  ihave Hidle : writerIdle γ σ Hs $$ [Hgσ HW Hpv]
  · iunfold writerIdle; iframe; ipureintro; exact Hid
  obtain ⟨Hpn, Hlen, Hbound, Hmatch⟩ := Hid
  have hl2 : 2 ≤ σ.log.length := by unfold MvccState.rev at hrev1; omega
  have hne : σ.log ≠ [] := by intro h0; rw [h0] at hl2; simp at hl2
  have hPrev := pendOk_rev' hok
  wp_auto
  wp_apply wp_intn wv.r' g (W64 3) (by decide) $$ [$Hpkg $Hg] as %x ⟨⟨%g1, Hg⟩, %Hx⟩
  (try wp_auto)
  by_cases hx0 : x = W64 0
  · -- a put
    simp only [hx0, _root_.decide_true]
    (try wp_auto)
    wp_apply wp_genKey wv.r' g1 $$ [$Hpkg $Hg] as %ks ⟨⟨%g2, Hg⟩, %kk, Hks, -, %Hkk⟩
    (try wp_auto)
    wp_apply wp_newVal w n hn0 hn1 $$ [$Hpkg $Hvals] as Hvals
    (try wp_auto)
    wp_apply wp_genLease w wv Lm g2 $$ [$Hpkg $Hw $Hlm $Hg] as %l ⟨Hlm, ⟨%g3, Hg⟩, %Hl⟩
    (try wp_auto)
    wp_apply wp_bytes_to_string ks kk (DFrac.own 1) $$ [$Hks] as Hks
    (try wp_auto)
    wp_apply wp_put p P kk (go!"v" ++ itoaM (sint.nat (n + W64 1))) l $$ [$Hpkg $Hp] as Hp
    (try wp_auto)
    wp_apply wp_string_to_bytes as %vs ⟨Hvs, -⟩
    imod ownSlice_persist $$ Hks with #Hks
    imod ownSlice_persist $$ Hvs with #Hvs
    (try wp_auto)
    have hkl := keyList_short kk Hkk
    have hlL : l = W64 0 ∨ l ∈ L := by
      rcases Hl with h | h
      · exact Or.inl h
      · exact Or.inr ((HLm l).1 h)
    wp_apply (hPutC γ.kv trace te σ pend ks vs kk (go!"v" ++ itoaM (sint.nat (n + W64 1))) l L)
      $$ [$Hmv $Htx $Htrc $Hks $Hvs $Hlo] as ⟨Htx, Htrc, Hlo⟩
    · ipureintro; exact ⟨by omega, hlL⟩
    (try wp_auto)
    iunfold ownPending at Hp
    icases Hp with ⟨%pv, Hpv, %Hprev, Hpst, Hpch, Hpcap⟩
    (try wp_auto)
    wp_apply wp_check
    · ipureintro
      simp only [PendM.put] at Hprev
      rw [Hprev, hPrev, Hlen]; simp
    (try wp_auto)
    iapply HΦ
    iexists [.put kk (go!"v" ++ itoaM (sint.nat (n + W64 1))) l],
      P.put kk (go!"v" ++ itoaM (sint.nat (n + W64 1))) l, n + W64 1
    iframe
    isplitr
    · ipureintro
      exact ⟨pendOk_put' σ Hs pend P hok Hlen _ _ _ Hkk,
        logOk_put σ.log pend hLok hne (by omega) _ _ _, by simp, Or.inr rfl⟩
    isplitl [Hpv Hpst Hpch Hpcap]
    · iunfold ownPending; iexists pv; iframe; ipureintro; exact Hprev
    ipureintro; exact HLm
  · sorry

end proof

end mvccrand
end EtcdGrove
end Perennial
