/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__appendChunk.lean`: the loop keeps the
items of `chunkL` on the key-values evaluated so far. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__appendChunk
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__processListItem
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.growSlice
public import Spec.reflect.Value__Len

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver reflectM

section pure
variable [GooseExts] {Obj : Type}

theorem decodedL_take_succ (dec : Dec Obj) (kvs : List EtcdKv) (i : Nat) (kv : EtcdKv) (o : Obj)
    (b : Bool) (hkv : kvs[i]? = some kv) (hd : dec kv.value = some (o, b)) :
    decodedL dec (kvs.take (i + 1)) =
      decodedL dec (kvs.take i) ++ [(kv.key, (o, sint.nat kv.modRev))] := by
  unfold decodedL
  rw [List.take_succ, hkv]
  simp [List.filterMap_append, hd]


theorem decodedL_append (dec : Dec Obj) (a b : List EtcdKv) :
    decodedL dec (a ++ b) = decodedL dec a ++ decodedL dec b := by
  unfold decodedL; rw [List.filterMap_append]

theorem decodedL_cons (dec : Dec Obj) (kv : EtcdKv) (r : List EtcdKv) (o : Obj) (b : Bool)
    (hd : dec kv.value = some (o, b)) :
    decodedL dec (kv :: r) = (kv.key, (o, sint.nat kv.modRev)) :: decodedL dec r := by
  simp [decodedL, hd]

theorem lstep_notfull {α O : Type} (sel : O → Bool) (lim : Nat)
    (s : k8s_etcd3.ListModel.LState α O) (ko : List α × O)
    (h : ¬(0 < lim ∧ lim ≤ s.items.length)) :
    k8s_etcd3.ListModel.lstep sel lim s ko =
      if sel ko.2 then { s with total := s.total + 1, items := ko.2 :: s.items, last := some ko.1 }
      else { s with total := s.total + 1 } := by
  simp only [k8s_etcd3.ListModel.lstep]
  rw [if_neg h]

theorem lstep_full {α O : Type} (sel : O → Bool) (lim : Nat)
    (s : k8s_etcd3.ListModel.LState α O) (ko : List α × O)
    (h : 0 < lim ∧ lim ≤ s.items.length) :
    k8s_etcd3.ListModel.lstep sel lim s ko = { s with total := s.total + 1, more := true } := by
  simp only [k8s_etcd3.ListModel.lstep]
  rw [if_pos h]

theorem w64_sint_nat (m : w64) (h : 0 ≤ sint.Z m) : W64 ((sint.nat m : Nat) : Int) = m := by
  word

/-- The loop state after the first `n` key-values of the chunk. -/
def chunkAt [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors}
    [HeapGS HasLC.hasLC GF] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] [DecidableEq Obj]
    (c : StoreCfg GF Obj) (sel : Obj → Bool) (lim : Nat)
    (st : k8s_etcd3.ListModel.LState w8 (Obj × Nat)) (kvs : List EtcdKv) (n : Nat) :
    k8s_etcd3.ListModel.LState w8 (Obj × Nat) :=
  chunkL (fun x => sel x.1) lim st (decodedL c.S.dec (kvs.take n))

/-- When the bucket is full after `n` key-values, the `n`-th's key is the last match. -/
def chunkLastOk [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors}
    [HeapGS HasLC.hasLC GF] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] [DecidableEq Obj]
    (c : StoreCfg GF Obj) (sel : Obj → Bool) (lim : Nat)
    (st : k8s_etcd3.ListModel.LState w8 (Obj × Nat)) (kvs : List EtcdKv) (n : Nat) : Prop :=
  0 < n → 0 < lim ∧ lim ≤ (chunkAt c sel lim st kvs n).items.length →
    ∃ kv, kvs[n - 1]? = some kv ∧ (chunkAt c sel lim st kvs n).last = some kv.key

section chunk
variable [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors}
    [HeapGS HasLC.hasLC GF] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] [DecidableEq Obj]

theorem chunkAt_succ (c : StoreCfg GF Obj) (sel : Obj → Bool) (lim : Nat)
    (st : k8s_etcd3.ListModel.LState w8 (Obj × Nat)) (kvs : List EtcdKv) (n : Nat) (kv : EtcdKv)
    (o : Obj) (b : Bool) (hkv : kvs[n]? = some kv) (hd : c.S.dec kv.value = some (o, b))
    (hm : (chunkAt c sel lim st kvs n).more = false) :
    chunkAt c sel lim st kvs (n + 1) =
      k8s_etcd3.ListModel.lstep (fun x => sel x.1) lim (chunkAt c sel lim st kvs n)
        (kv.key, (o, sint.nat kv.modRev)) := by
  unfold chunkAt at hm ⊢
  rw [decodedL_take_succ _ _ _ _ _ _ hkv hd, chunkL_append]
  simp [chunkL, hm]

theorem chunkAt_full (c : StoreCfg GF Obj) (sel : Obj → Bool) (lim : Nat)
    (st : k8s_etcd3.ListModel.LState w8 (Obj × Nat)) (kvs : List EtcdKv) (n : Nat) (kv : EtcdKv)
    (o : Obj) (b : Bool) (hkv : kvs[n]? = some kv) (hd : c.S.dec kv.value = some (o, b))
    (hm : (chunkAt c sel lim st kvs n).more = false)
    (hf : 0 < lim ∧ lim ≤ (chunkAt c sel lim st kvs n).items.length) :
    let s' := chunkL (fun x => sel x.1) lim st (decodedL c.S.dec kvs)
    s'.items = (chunkAt c sel lim st kvs n).items ∧ s'.last = (chunkAt c sel lim st kvs n).last ∧
      s'.more = true := by
  have hdrop : kvs.drop n = kv :: kvs.drop (n + 1) := by
    rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 hkv).1]
    rw [(List.getElem?_eq_some_iff.1 hkv).2]
  have heq : chunkL (fun x => sel x.1) lim st (decodedL c.S.dec kvs) =
      k8s_etcd3.ListModel.lstep (fun x => sel x.1) lim (chunkAt c sel lim st kvs n)
        (kv.key, (o, sint.nat kv.modRev)) := by
    conv => lhs; rw [← List.take_append_drop n kvs, hdrop, decodedL_append,
      decodedL_cons _ _ _ _ _ hd, chunkL_append]
    have hf' := hf
    unfold chunkAt at hm hf' ⊢
    simp only [chunkL, hm, Bool.false_eq_true, ↓reduceIte]
    rw [lstep_full _ _ _ _ hf']
    exact chunkL_more _ _ _ rfl _
  simp only
  rw [heq, lstep_full _ _ _ _ hf]
  exact ⟨rfl, rfl, rfl⟩

theorem chunkAt_length (c : StoreCfg GF Obj) (sel : Obj → Bool) (lim : Nat)
    (st : k8s_etcd3.ListModel.LState w8 (Obj × Nat)) (kvs : List EtcdKv) :
    chunkAt c sel lim st kvs kvs.length = chunkL (fun x => sel x.1) lim st (decodedL c.S.dec kvs) := by
  unfold chunkAt; rw [List.take_length]

theorem chunkAt_step (c : StoreCfg GF Obj) (sel : Obj → Bool) (lim : Nat)
    (st : k8s_etcd3.ListModel.LState w8 (Obj × Nat)) (kvs : List EtcdKv) (n : Nat) (kv : EtcdKv)
    (o : Obj) (b : Bool) (hkv : kvs[n]? = some kv) (hd : c.S.dec kv.value = some (o, b))
    (hm : (chunkAt c sel lim st kvs n).more = false)
    (hnf : ¬(0 < lim ∧ lim ≤ (chunkAt c sel lim st kvs n).items.length)) :
    (chunkAt c sel lim st kvs (n + 1)).more = false ∧
    itemsOf c (chunkAt c sel lim st kvs (n + 1)) =
      (if sel o then itemsOf c (chunkAt c sel lim st kvs n) ++
          [(o, c.S.fmtRV (W64 ((sint.nat kv.modRev : Nat) : Int)))]
        else itemsOf c (chunkAt c sel lim st kvs n)) ∧
    (0 < lim ∧ lim ≤ (chunkAt c sel lim st kvs (n + 1)).items.length →
      (chunkAt c sel lim st kvs (n + 1)).last = some kv.key) := by
  rw [chunkAt_succ c sel lim st kvs n kv o b hkv hd hm, lstep_notfull _ _ _ _ hnf]
  cases hs : sel o
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hm, rfl, fun h => absurd h hnf⟩
  · simp only [hs, ↓reduceIte, itemsOf, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil]
    exact ⟨hm, trivial, fun _ => trivial⟩

end chunk

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.appendChunk.wp_proof
    (wp_processListItem : store.processListItem.spec (GF := GF) (hG := hG))
    (wp_growSlice : growSlice.spec (GF := GF) (hG := hG))
    (wp_Len : reflect.Value.Len.spec (GF := GF) (hG := hG)) :
    store.appendChunk.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c L ctx ksl ps kvs pred sel emp nf ag v p paging st hdec hmod hlen hpg
  wp_start as ⟨#Hst, #Hlc, #Hsel, #Hnf, #Hctx, %hv, Hksl, #Hkvs, Hit, %hst⟩
  icases Hit with ⟨%s, Hp, Hit⟩
  ihave #Hsel' := Hsel
  iunfold selPredOk at Hsel'
  icases Hsel' with ⟨%hsel, -, #HEmp⟩
  ihave #Hlc' := Hlc
  iunfold listContractOk at Hlc'
  icases Hlc' with ⟨#Hlc'', -, -, -⟩
  ihave %Hpl := ownSlice_len _ _ _ $$ Hksl
  ihave %Hpk := (BigSepL2.bigSepL2_length (PROP := IProp GF)) $$ Hkvs
  (try wp_auto)
  wp_bind
  iapply HEmp $$ %pred_ptr %_ pred
  inext
  iintro pred
  have hkl : sint.Z ksl.len ≤ 2 ^ 41 ∧ 0 ≤ sint.Z ksl.len := by
    constructor <;> word
  ihave #Hnil : (slice.nil ↦*□ ([] : List w64) : IProp GF) $$ []
  · iapply ownSlice_nil
  cases emp
  case' false =>
    (try wp_auto)
    wp_apply wp_slice_literal (V := w64) [ksl.len]
    isplitr
    · ipureintro; rfl
    iintro %szl ⟨Hszl, -⟩
    imod ownSlice_persist _ _ _ $$ Hszl with #Hszl
    (try wp_auto)
    wp_apply (wp_growSlice Obj c.S L v_ptr v p s (itemsOf c st) (W64 2048) _ _ (by decide))
      $$ [$Hp $Hit $Hszl] as ⟨%s1, Hp, Hit⟩
    · iframe #
      ipureintro; exact hv
  case' true =>
    (try wp_auto)
    wp_apply (wp_growSlice Obj c.S L v_ptr v p s (itemsOf c st) ksl.len slice.nil [] hkl.1)
      $$ [$Hp $Hit] as ⟨%s1, Hp, Hit⟩
    · iframe #
      ipureintro; exact hv
  all_goals
    (try wp_auto)
    rename_i igo
    irename : (igo ↦ zero_val w64 : IProp GF) => Higo
    ihave IH : iprop(∃ (j k : w64) (kvl : Loc) (ps' : List Loc) (lkv : GoSlice) (s' : GoSlice),
        "i" ∷ i_ptr ↦ j ∗ "Higo" ∷ igo ↦ k ∗ "kv" ∷ kv_ptr ↦ kvl ∗
        "lastKey" ∷ lastKey_ptr ↦ lkv ∗ "evaluated" ∷ evaluated_ptr ↦ j ∗
        "Hksl" ∷ ksl ↦* ps' ∗ "Hp" ∷ p ↦ s' ∗
        "Hit" ∷ L.itemsAt s' (itemsOf c (chunkAt c sel (limN pred.Limit') st kvs (sint.nat j))) ∗
        "#Hlk" ∷ lastKeyIs lkv kvs (sint.nat j) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ kvs.length ∧ ps'.length = ps.length ∧
          (∀ m, sint.nat j ≤ m → ps'[m]? = ps[m]?) ∧
          (chunkAt c sel (limN pred.Limit') st kvs (sint.nat j)).more = false ∧
          chunkLastOk c sel (limN pred.Limit') st kvs (sint.nat j)⌝) $$ [i Higo kv lastKey evaluated Hksl Hp Hit]
    · iexists W64 0, _, _, ps, _, s1
      simp only [named]
      iframe
      have h0 : sint.nat (W64 0) = 0 := rfl
      rw [h0]
      isplitr
      · simp only [lastKeyIs, ↓reduceIte]; ipureintro; rfl
      ipureintro
      exact ⟨by decide, by omega, trivial, fun _ _ => trivial, hst, fun h => absurd h (by omega)⟩
    wp_for IH
    wp_if_destruct
    · obtain ⟨hj0, hjk, hpsl, hpse, hm, hlast⟩ := Hj
      have Hif' : sint.Z j < sint.Z ksl.len := by
        first | exact Hif | (have h := go.intoVal_inj Hif; simpa using h)
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ksl.len := ⟨hj0, Hif'⟩
      have hjlt : sint.nat j < kvs.length := by
        have h1 := Hpl.1
        rw [Hpk] at h1
        simp only [sint.nat, sint.Z] at h1 hj0 Hif' ⊢
        omega
      simp only [hb, _root_.and_self, ↓reduceIte]
      obtain ⟨kv, hkv⟩ : ∃ kv, kvs[sint.nat j]? = some kv := ⟨_, List.getElem?_eq_getElem hjlt⟩
      obtain ⟨q, hq⟩ : ∃ q, ps[sint.nat j]? = some q :=
        ⟨_, List.getElem?_eq_getElem (by rw [Hpk]; exact hjlt)⟩
      have hq' : ps'[(sint.Z j).toNat]? = some q := by rw [← hq]; exact hpse _ (Nat.le_refl _)
      wp_apply wp_load_slice_index ksl (sint.Z j) ps' _ q hj0 $$ [$Hksl] as Hksl
      · ipureintro; exact hq'
      icases (BigSepL2.bigSepL2_lookup_acc (PROP := IProp GF) hq hkv) $$ Hkvs with ⟨#Hkv, -⟩
      obtain ⟨o, bo, hdo⟩ : ∃ o b, c.S.dec kv.value = some (o, b) := by
        have := hdec kv (List.mem_of_getElem? hkv)
        cases h : c.S.dec kv.value with
        | none => exact absurd h this
        | some x => exact ⟨x.1, x.2, rfl⟩
      icases persistent_entails_left (L.itemsAt_len _ _) $$ Hit with ⟨Hit, %Hil⟩
      icases persistent_entails_left (L.itemsAt_wf _ _) $$ Hit with ⟨Hit, %Hiw⟩
      have Hil' : uint.nat s'.len = (chunkAt c sel (limN pred.Limit') st kvs (sint.nat j)).items.length := by
        rw [Hil]; simp [itemsOf]
      (try wp_auto)
      cases paging
      case' false =>
        have hnf : ¬(0 < limN pred.Limit' ∧
            limN pred.Limit' ≤ (chunkAt c sel (limN pred.Limit') st kvs (sint.nat j)).items.length) := by
          intro h
          have h0 := h.1
          simp only [limN] at h0
          split at h0
          · simp_all
          · omega
        (try wp_auto)
      case' true =>
        have hlp : 0 < sint.Z pred.Limit' := by simpa using hpg.symm
        (try wp_auto)
        wp_apply (wp_Len v_ptr _ _ v c.S.objTy p s') $$ [$v $Hp] as ⟨v, Hp⟩
        · ipureintro; exact hv
        (try wp_auto)
        wp_if_destruct
        · -- the limit is reached: return before this key-value
          have hfull : 0 < limN pred.Limit' ∧
              limN pred.Limit' ≤ (chunkAt c sel (limN pred.Limit') st kvs (sint.nat j)).items.length := by
            have hlim : limN pred.Limit' = sint.nat pred.Limit' := by simp only [limN, if_pos hlp]
            refine ⟨by rw [hlim]; word, ?_⟩
            rw [← Hil', hlim]
            word
          obtain ⟨hi, hl, hmo⟩ := chunkAt_full c sel _ st kvs _ kv o bo hkv hdo hm hfull
          (try wp_auto)
          wp_for_post
          iapply HΦ
          isplitr
          · ipureintro; exact hmo.symm
          isplitl [Hksl]
          · iexists _; iexact Hksl
          isplitl [Hp Hit]
          · iexists s'
            have hit : itemsOf c (chunkL (fun x => sel x.1) (limN pred.Limit') st (decodedL c.S.dec kvs)) =
                itemsOf c (chunkAt c sel (limN pred.Limit') st kvs (sint.nat j)) := by
              simp only [itemsOf, hi]
            rw [hit]
            iframe
          iexists sint.nat j
          iframe #
          ipureintro
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · word
          · intro h; cases h
          · intro hn _
            rw [hl]
            exact hlast hn hfull
        have hnf : ¬(0 < limN pred.Limit' ∧
            limN pred.Limit' ≤ (chunkAt c sel (limN pred.Limit') st kvs (sint.nat j)).items.length) := by
          have hlim : limN pred.Limit' = sint.nat pred.Limit' := by simp only [limN, if_pos hlp]
          intro h
          have h2 := h.2
          rw [← Hil', hlim] at h2
          apply Hif
          word
      all_goals
        ihave #Hkv' := Hkv
        iunfold txn.kvIs at Hkv'
        icases Hkv' with ⟨%ksl', %vsl, #Hkey, #Hksl', -, -, -, -, -, -, -⟩
        (try wp_auto)
        wp_apply (wp_processListItem Obj sp c L ctx q kv pred sel _ nf ag v p s' _ o ⟨bo, hdo⟩)
          $$ [$Hp $Hit] as ⟨%s'', Hp, Hit⟩
        · iframe #
          ipureintro; exact hv
        (try wp_auto)
        simp only [hb, _root_.and_self, ↓reduceIte]
        have hjps : sint.Z j < (ps'.length : Int) := by
          rw [hpsl, Hpk]; simp only [sint.nat, sint.Z] at hjlt hj0 ⊢; omega
        wp_apply (wp_store_slice_index ksl (sint.Z j) ps' (null : Loc)) $$ [$Hksl] as Hksl
        · ipureintro; exact ⟨hj0, hjps⟩
        (try wp_auto)
        wp_for_post
        obtain ⟨hm', hit', hl'⟩ := chunkAt_step c sel _ st kvs _ kv o bo hkv hdo hm hnf
        have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
          have := hlen; simp only [sint.nat, sint.Z] at hjlt hj0 ⊢; word
        iframe
        iexists j + W64 1, j, q, ps'.set (sint.Z j).toNat null, ksl', s''
        simp only [named]
        rw [hj1, hit', w64_sint_nat _ (hmod kv (List.mem_of_getElem? hkv))]
        iframe
        isplitr
        · simp only [lastKeyIs, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          iexists kv
          iframe #
          ipureintro; exact hkv
        ipureintro
        refine ⟨by word, by omega, by simp [hpsl], ?_, hm', ?_⟩
        · intro m hmj
          rw [List.getElem?_set_ne (by simp only [sint.nat, sint.Z] at hmj hj0 ⊢; omega)]
          exact hpse m (by omega)
        · intro _ hf
          exact ⟨kv, by simpa using hkv, hl' hf⟩
    · obtain ⟨hj0, hjk, -, -, hm, hlast⟩ := Hj
      have Hif' : ¬ sint.Z j < sint.Z ksl.len := by
        first | exact Hif | (intro h; apply Hif; simp [h])
      have hjl : sint.nat j = kvs.length := by
        have h1 := Hpl.1
        rw [Hpk] at h1
        have h2 := Hpl.2
        simp only [sint.nat, sint.Z] at h1 h2 hj0 hjk Hif' ⊢
        omega
      (try simp only [show decide (sint.Z j < sint.Z ksl.len) = false from decide_eq_false Hif',
        _root_.decide_true, ↓reduceIte])
      (try wp_auto)
      iapply HΦ
      rw [← chunkAt_length, ← hjl]
      isplitr
      · ipureintro; exact hm.symm
      isplitl [Hksl]
      · iexists _; iexact Hksl
      isplitl [Hp Hit]
      · iexists s'; iframe
      iexists sint.nat j
      iframe #
      ipureintro
      refine ⟨by omega, by word, fun _ => rfl, ?_⟩
      intro hn hor
      rcases hor with h | h
      · exact absurd h (by simp)
      · exact hlast hn h

end proof

end k8s
end EtcdGrove
end Perennial
