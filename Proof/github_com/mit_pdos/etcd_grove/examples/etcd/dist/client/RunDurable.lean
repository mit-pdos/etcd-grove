/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/RunDurable.lean` (#50 N9a,
`notes/etcd-dist-plan.md` §23). Lean-first (no Rocq counterpart).

`n` is clamped to `[0, 256]` (`wp_join`); the orchestrator connects (`newClient`; its error ends the workload),
defers `Close`, and allocates durable's invariant from its share's half with `n` puts' tokens
(`durInv_alloc`). The put loop keeps the acknowledgements `acks` (the slice `acked`), the tokens of the puts
not yet sent, and the fired witness of the acknowledged ones (`durFiredAll`): put `j` (`wp_cliPut` over
`KV_Put_dist`) carries its token in its one-shot update (`durPutAu`), and a `nil` reply gives `durFired`. The
range (`wp_cliGet` over `KV_Get_dist`, one `WithPrefix` option) reads `durReadOk` (`durGetAu`): its key-values
are the prefix's (`durRange_eq`), each a put's at version `1`, and every acknowledged put's key is among them.
The check loop over the reply: the inner loop finds the last `j` with `durableKey(j)` the key (it exists), whose
value is `durVal j` (`durVal_of_key`), and marks `seen[j]` (keys distinct below 256: `durKey_inj`); the last loop
finds every acknowledged put seen. Then `checked`, and the deferred `Close`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunDurable
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.durableKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.durableValue
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KVCallsDist
public import Spec.go_etcd_io.etcd.client.v3.Client__Close
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- The tokens of the puts not yet sent: the next one, and the rest. -/
theorem toks_next (γs : List GName) (k : Nat) (g : GName) (hg : γs[k]? = some g) :
    ([∗list] g' ∈ γs.drop k, token (GF := GF) g') ⊢
      token g ∗ [∗list] g' ∈ γs.drop (k + 1), token g' := by
  have hk : k < γs.length := by
    rcases Nat.lt_or_ge k γs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hg; cases hg
  have hd : γs.drop k = g :: γs.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hk]
    congr 1
    exact Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hg)
  rw [hd]
  exact BigSepL.bigSepL_cons.1

/-- **The check of one key-value** (pure): a key-value of the prefix's view is the put `j`'s for exactly
one `j < N` (`N ≤ 256`), at version `1`. -/
theorem durCheck_kv {N : Nat} (hN : N ≤ 256) {σ : KVState} {S : Nat → Prop}
    (h : durReadOk N S σ) {x : EtcdKv} (hx : x ∈ pfxView durablePfx σ) :
    ∃ j, j < N ∧ x.key = durKey j ∧ x.value = durVal j ∧ x.version = W64 1 ∧
      ∀ j', j' < N → x.key = durKey j' → j' = j := by
  obtain ⟨j, hj, hk, hv, hver⟩ := h.1 x hx
  refine ⟨j, hj, hk, hv, hver, fun j' hj' hk' => ?_⟩
  exact durKey_inj (by omega) (by omega) (hk'.symm.trans hk)

/-! Word facts for the loops (stated apart: `word` in the loops' large contexts fails). -/

theorem w_nat_lt {t l : w64} (h0 : 0 ≤ sint.Z t) (h : sint.Z t < sint.Z l) : sint.nat t < sint.nat l := by
  word

theorem w_nat_succ {t l : w64} (h0 : 0 ≤ sint.Z t) (h : sint.Z t < sint.Z l) :
    sint.nat (t + W64 1) = sint.nat t + 1 := by
  word

theorem w_succ_nonneg {t l : w64} (h0 : 0 ≤ sint.Z t) (h : sint.Z t < sint.Z l) : 0 ≤ sint.Z (t + W64 1) := by
  word

theorem w_succ_le {t l : w64} (h0 : 0 ≤ sint.Z t) (h : sint.Z t < sint.Z l) : sint.Z (t + W64 1) ≤ sint.Z l := by
  word

theorem w_nat_le {t l : w64} (hl : 0 ≤ sint.Z l) (h : ¬ sint.Z t < sint.Z l) : sint.nat l ≤ sint.nat t := by
  word

theorem w_Z_lt {t l : w64} (h0 : 0 ≤ sint.Z t) (hl : 0 ≤ sint.Z l) (h : sint.nat t < sint.nat l) :
    sint.Z t < sint.Z l := by
  word

theorem w_not_neg {t : w64} (h0 : 0 ≤ sint.Z t) : ¬ sint.Z t < sint.Z (W64 0) := by
  word

theorem w_nat_zero : sint.nat (W64 0) = 0 := by
  word

theorem w_Z_lt_nat {t l : w64} (h0 : 0 ≤ sint.Z t) (hl : 0 ≤ sint.Z l) (h : sint.nat t < sint.nat l) :
    sint.Z t < ((sint.nat l : Nat) : Int) := by
  word

set_option maxHeartbeats 3200000 in
theorem RunDurable.wp_proof
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_checked : checked.spec (GF := GF) (hG := hG))
    (wp_ended : ended.spec (GF := GF) (hG := hG))
    (wp_durableKey : durableKey.spec (GF := GF) (hG := hG))
    (wp_durableValue : durableValue.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : EtcdGrove.WithPrefix.spec (GF := GF) (hG := hG))
    (wp_Close : EtcdGrove.Client.Close.spec (GF := GF) (hG := hG))
    (wp_KV_Put : KV_Put_dist.spec (GF := GF) (hG := hG))
    (wp_KV_Get : KV_Get_dist.spec (GF := GF) (hG := hG)) :
    RunDurable.spec (GF := GF) (hG := hG) := by
  intro π eps addrs n hn hV Htb hpl hAs
  wp_start as ⟨Hlt, #Heps, Hsh⟩
  (try iunfold durableShare at Hsh)
  iunfold kvPfxShare at Hsh
  icases Hsh with ⟨%Γ, %γ, %Hauth, #Hms, #Hpfx, Hhalf⟩
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- `if n > deployment.MaxDurable { n = deployment.MaxDurable }`
  wp_join iprop(∃ m : w64, n_ptr ↦ m ∗ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ 256⌝) at next with [n]
    as ⟨%m, n, %Hm⟩
  · wp_if_destruct
    · (try wp_auto)
      wp_join_done
      (try iexists (W64 256))
      (try iframe)
      (try (ipureintro; constructor <;> word))
    · (try wp_auto)
      wp_join_done
      (try iexists n)
      (try iframe)
      (try (ipureintro; constructor <;> word))
  have hmN : sint.nat m ≤ 256 := by have h := Hm.2; word
  -- `cli, err := newClient(eps)`
  wp_apply (wp_newClient eps addrs (Classical.choice hV) Htb hpl) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, #Hnp, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hcerr
  ihave #Hcore := clientCoreAt_of_new cl addrs (Classical.choice hV) $$ [Hnc Hnp]
  · iframe #
  ihave ⟨%api, #Hkc⟩ := kvClient_of_new cl addrs (Classical.choice hV) Γ $$ [Hnc Hnp Hms]
  · iframe #
  ihave #Hnil := optsAt_nil (GF := GF)
  -- durable's invariant, with the `n` puts' tokens
  imod (durInv_alloc γ (sint.nat m) ⊤) $$ Hhalf
    with ⟨%γF, %γs, %Hγs, #Hdi, Htoks⟩
  ihave Hfa := durFiredAll_none (GF := GF) γF
  imod Hfa with #Hfa
  (try wp_auto)
  -- `acked := make([]bool, n)`
  wp_apply (wp_slice_make2 (V := Bool) m) as %asl ⟨Hasl, -⟩
  · ipureintro; exact Hm.1
  (try wp_auto)
  ihave %Haslen := ownSlice_len $$ Hasl
  -- the puts
  ihave IP : (∃ (j : w64) (acks : List Bool), "i" ∷ i_ptr ↦ j ∗
      "Hasl" ∷ asl ↦* (acks ++ List.replicate (sint.nat m - acks.length) false) ∗ "Hlt" ∷ levelTok 0 ∗
      "Htoks" ∷ ([∗list] g ∈ γs.drop acks.length, token (GF := GF) g) ∗
      "#Hfa" ∷ durFiredAll (Gg := hG.goose_globalGS) γF (fun j' => acks[j']? = some true) ∗
      "%Hj" ∷ ⌜sint.nat j = acks.length ∧ acks.length ≤ sint.nat m ∧ 0 ≤ sint.Z j⌝ : IProp GF)
    $$ [i Hasl Hlt Htoks]
  · iexists W64 0, []
    simp only [named, List.length_nil, Nat.sub_zero, List.nil_append, List.drop_zero]
    iframe
    isplitl []
    · iapply (durFiredAll_mono γF _ _ ?_) $$ Hfa
      intro j' hj'; simp at hj'
    ipureintro; refine ⟨by decide, by omega, by decide⟩
  wp_for IP
  wp_if_destruct
  · have hjm : sint.nat j < sint.nat m := by word
    have hjl : acks.length < γs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, γs[acks.length]? = some g := ⟨_, List.getElem?_eq_getElem hjl⟩
    icases toks_next γs acks.length g hg $$ Htoks with ⟨Hg, Htoks⟩
    (try wp_auto)
    -- `ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -⟩
    (try wp_auto)
    -- `cli.Put(ctx, durableKey(i), durableValue(i))`, with put `j`'s update and token
    wp_apply (wp_durableKey j Hj.2.2) as %k %Hk
    (try wp_auto)
    wp_apply (wp_durableValue j Hj.2.2) as %v %Hv
    subst Hk Hv
    (try wp_auto)
    ihave Hau := durPutAu (Gg := hG.goose_globalGS) Γ.kv γ γF γs (sint.nat m) (sint.nat j) g hmN hjm
      (by rw [Hj.1]; exact hg) $$ [Hg]
    · iframe Hg
      iframe #
    wp_apply (wp_cliPut wp_KV_Put cl api addrs (Classical.choice hV) Γ pctx pcd (durKey (sint.nat j))
        (durVal (sint.nat j)) (fun _ => durFired (Gg := hG.goose_globalGS) γF (sint.nat j))
        (dur_sizes _).1 Hauth) $$ [Hlt Hau] as %presp %perr ⟨Hlt, Hput⟩
    · iframe Hlt Hau
      iframe #
    (try wp_auto)
    wp_apply Hpcancel
    (try wp_auto)
    have Hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z asl.len := by
      have h1 := Haslen.1
      simp only [List.length_replicate] at h1
      constructor <;> word
    have hset : ∀ b : Bool, (acks ++ List.replicate (sint.nat m - acks.length) false).set (sint.Z j).toNat b =
        (acks ++ [b]) ++ List.replicate (sint.nat m - (acks ++ [b]).length) false := by
      intro b
      rw [show (sint.Z j).toNat = acks.length by rw [← Hj.1]; (try rfl)]
      exact acks_set acks (sint.nat m) b (by omega)
    have hlenA : ((acks ++ List.replicate (sint.nat m - acks.length) false)).length = sint.nat m := by
      simp; omega
    icases Hput with (⟨%Hperr, %σp, #Hfired⟩ | %Hpfail)
    · subst Hperr
      (try wp_auto)
      (try simp only [Hb, _root_.and_self, ↓reduceIte])
      wp_apply (wp_store_slice_index asl (sint.Z j) _ true) $$ [Hasl] as Hasl
      · iframe Hasl; ipureintro; rw [hlenA]; constructor <;> word
      (try wp_auto)
      ihave #Hfa2 := durFiredAll_add (Gg := hG.goose_globalGS) γF _ (sint.nat j) $$ [Hfa Hfired]
      · iframe #
      wp_for_post
      iframe
      iexists j + W64 1, acks ++ [true]
      simp only [named]
      rw [hset true]
      iframe
      isplitl [Htoks]
      · rw [List.length_append, List.length_singleton]
        iexact Htoks
      isplitl []
      · iapply (durFiredAll_mono γF _ _ ?_) $$ Hfa2
        intro j' hj'
        rcases acks_snoc_true hj' with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [h, ← Hj.1])
      ipureintro
      simp only [List.length_append, List.length_singleton]
      refine ⟨by word, by omega, by word⟩
    · obtain ⟨Hperr, -⟩ := Hpfail
      cases perr with
      | nil => exact absurd rfl Hperr
      | ok ei => ?_
      (try wp_auto)
      (try simp only [Hb, _root_.and_self, ↓reduceIte])
      wp_apply (wp_store_slice_index asl (sint.Z j) _ false) $$ [Hasl] as Hasl
      · iframe Hasl; ipureintro; rw [hlenA]; constructor <;> word
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, acks ++ [false]
      simp only [named]
      rw [hset false]
      iframe
      isplitl [Htoks]
      · rw [List.length_append, List.length_singleton]
        iexact Htoks
      isplitl []
      · iapply (durFiredAll_mono γF _ _ ?_) $$ Hfa
        intro j' hj'
        exact acks_snoc_false hj'
      ipureintro
      simp only [List.length_append, List.length_singleton]
      refine ⟨by word, by omega, by word⟩
  -- all puts sent
  have hall : acks.length = sint.nat m := by
    have h1 := Hj.1
    have h2 := Hj.2.1
    have h3 : sint.nat m ≤ sint.nat j := by word
    omega
  (try wp_auto)
  -- `resp, err := cli.Get(ctx, durablePrefix, clientv3.WithPrefix())`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
  (try wp_auto)
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  ipersist Hosl
  ihave #Hopts := optsAt_single (GF := GF) _ f1 withPrefixM $$ [Hosl Hf1]
  · iframe #
  ihave #Hopts' := optsAt_res _ _ iprop(True) $$ Hopts
  (try wp_auto)
  ihave #Hgau := durGetAu (Gg := hG.goose_globalGS) Γ.kv γ γF γs (sint.nat m)
    (fun j' => acks[j']? = some true) $$ [Hfa]
  · iframe #
  have hser : (rangeWireOf (opGetModel durablePfx [withPrefixM])).base.serializable = false := by
    first
    | (rw [durGetOp_eq]; done)
    | (rw [durGetOp_eq]; rfl)
    | simp [durGetOp_eq, txn.rangeOpOf]
  have hsz := (dur_sizes 0).2
  wp_apply (wp_cliGetR wp_KV_Get cl api addrs (Classical.choice hV) Γ gctx gcd durablePfx _ [withPrefixM]
      iprop(True) (fun σ => iprop(⌜durReadOk (sint.nat m) (fun j' => acks[j']? = some true) σ⌝))
      durGet_ok hser hsz)
    $$ [Hlt] as %gresp %gerr ⟨Hlt, -, Hget⟩
  · iframe Hlt
    iframe #
    rw [show (opGetModel durablePfx [withPrefixM]).base.sortSet = false by
      first | rfl | simp [opGetModel, opFold, withPrefixM, OpFull.getInit, OpFull.newOp, OpModel.zero]]
    iapply sortNamesIf_false
  (try wp_auto)
  wp_apply Hgcancel
  icases Hget with (⟨%Hgerr, %mr, %σ, #Hm, #HQ, %Hsel⟩ | %Hgfail)
  rotate_left
  · obtain ⟨Hgerr, -⟩ := Hgfail
    cases gerr with
    | nil => exact absurd rfl Hgerr
    | ok ei => ?_
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    wp_apply wp_Close as %ce -
    · iframe #
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hgerr
  icases HQ with %Hrd
  have Hsel' : txn.srvRangeOk (rangeWireOf (opGetModel durablePfx [withPrefixM])) σ.kvs mr.kvs mr.more := by
    have h := Hsel.1
    have e : ∀ r : w64, r = W64 0 → (σ.at (σ.readRev r)).kvs = σ.kvs := by
      intro r hr
      subst hr
      have hrr : σ.readRev (W64 0) = σ.rev := by simp [KVState.readRev]
      rw [hrr]; rfl
    rw [e OpModel.zero.rev rfl] at h
    exact h
  have hview : mr.kvs = pfxView durablePfx σ := durRange_eq σ.kvs mr.kvs mr.more Hsel'
  (try wp_auto)
  -- `seen := make([]bool, n)`
  wp_apply (wp_slice_make2 (V := Bool) m) as %ssl ⟨Hssl, -⟩
  · ipureintro; exact Hm.1
  (try wp_auto)
  iunfold rangeRespMsg at Hm
  icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hplen, #Hall⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  ihave %Hssllen := ownSlice_len $$ Hssl
  (try wp_auto)
  -- `for _, kv := range resp.Kvs`: `seen[j]` for every put whose key-value is among those checked
  ihave IR : (∃ (t : w64) (ss : List Bool) (kvp : Loc), "Hctr" ∷ i_ptr ↦ t ∗ "kv" ∷ kv_ptr ↦ kvp ∗
      "Hssl" ∷ ssl ↦* ss ∗
      "%Ht" ∷ ⌜0 ≤ sint.Z t ∧ sint.nat t ≤ mr.kvs.length ∧ ss.length = sint.nat m ∧
        ∀ j', j' < sint.nat m → (∃ x ∈ mr.kvs.take (sint.nat t), x.key = durKey j') →
          ss[j']? = some true⌝ : IProp GF) $$ [i kv Hssl]
  · iexists W64 0, _, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨by decide, by simp, by simp, ?_⟩
    intro j' _ ⟨x, hx, _⟩
    rw [w_nat_zero] at hx
    simp at hx
  wp_for IR
  wp_if_destruct
  · -- the `t`th key-value
    have HifR := Hif
    have htl : sint.nat t < mr.kvs.length := by
      have h1 := Hsll.1; rw [Hplen] at h1; have h2 := w_nat_lt Ht.1 Hif; omega
    obtain ⟨x, hx⟩ : ∃ x, mr.kvs[sint.nat t]? = some x := ⟨_, List.getElem?_eq_getElem htl⟩
    obtain ⟨p, hp⟩ : ∃ p, ps[sint.nat t]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave #Hx := Hall $$ %(sint.nat t) %p %x %hp %hx
    have hxv : x ∈ pfxView durablePfx σ := by rw [← hview]; exact List.mem_of_getElem? hx
    obtain ⟨jx, hjx, hkx, hvx, hverx, huniq⟩ := durCheck_kv hmN Hrd hxv
    have Hbt : 0 ≤ sint.Z t ∧ sint.Z t < sint.Z sl.len := ⟨Ht.1, Hif⟩
    (try simp only [Hbt, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index _ (sint.Z t) _ DFrac.discard p Ht.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; rw [show (sint.Z t).toNat = sint.nat t from rfl]; exact hp
    (try wp_auto)
    iunfold txn.kvIs at Hx
    icases Hx with ⟨%kSl, %vSl, #HkF, #HkS, -, -, #HverF, #HvF, #HvS, -, %Hpnn⟩
    -- the inner loop: `i` is the last `j < n` with `durableKey(j)` the key
    ihave IJ : (∃ (jj iv : w64), "j" ∷ j_ptr ↦ jj ∗ "i" ∷ i_ptr ↦ iv ∗
        "%Hjj" ∷ ⌜0 ≤ sint.Z jj ∧ sint.Z jj ≤ sint.Z m ∧
          (jx < sint.nat jj → 0 ≤ sint.Z iv ∧ sint.nat iv < sint.nat m ∧
            x.key = durKey (sint.nat iv))⌝ : IProp GF) $$ [j i]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro
      refine ⟨by decide, Hm.1, ?_⟩
      intro h
      have := w_nat_zero
      omega
    wp_for IJ
    wp_if_destruct
    · (try wp_auto)
      wp_apply wp_bytes_to_string kSl x.key DFrac.discard $$ [HkS] as -
      · iframe #
      (try wp_auto)
      wp_apply (wp_durableKey jj Hjj.1) as %kj %Hkj
      subst Hkj
      (try wp_auto)
      by_cases heq : x.key = durKey (sint.nat jj)
      · rw [decide_eq_true heq]
        (try wp_auto)
        wp_for_post
        iframe
        iexists jj + W64 1, jj
        simp only [named]
        iframe
        ipureintro
        refine ⟨w_succ_nonneg Hjj.1 Hif, w_succ_le Hjj.1 Hif, fun _ => ⟨Hjj.1, w_nat_lt Hjj.1 Hif, heq⟩⟩
      · rw [decide_eq_false heq]
        (try wp_auto)
        wp_for_post
        iframe
        iexists jj + W64 1, iv
        simp only [named]
        iframe
        ipureintro
        refine ⟨w_succ_nonneg Hjj.1 Hif, w_succ_le Hjj.1 Hif, fun h => ?_⟩
        by_cases hlt : jx < sint.nat jj
        · exact Hjj.2.2 hlt
        · exfalso
          have : jx = sint.nat jj := by
            have := w_nat_succ Hjj.1 Hif
            omega
          exact heq (by rw [← this]; exact hkx)
    -- after the inner loop: `i` is `jx`
    have hdone : jx < sint.nat jj := by
      have h3 := w_nat_le Hm.1 Hif
      omega
    obtain ⟨hiv0, hivm, hkiv⟩ := Hjj.2.2 hdone
    have hivx : sint.nat iv = jx := huniq _ hivm hkiv
    (try wp_auto)
    have hnneg : ¬ (sint.Z iv < sint.Z (W64 0)) := w_not_neg hiv0
    (try simp only [hnneg, decide_false, Bool.false_eq_true, ↓reduceIte])
    (try wp_auto)
    wp_apply wp_bytes_to_string vSl x.value DFrac.discard $$ [HvS] as -
    · iframe #
    (try wp_auto)
    wp_apply (wp_durableValue iv hiv0) as %vi %Hvi
    subst Hvi
    rw [hivx, ← hvx]
    (try wp_auto)
    rw [hverx]
    (try wp_auto)
    -- `seen[i] = true`
    have Hbs : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z ssl.len :=
      ⟨hiv0, w_Z_lt hiv0 Hssllen.2 (by have h := Hssllen.1; simp at h; omega)⟩
    (try simp only [Hbs, _root_.and_self, ↓reduceIte])
    wp_apply (wp_store_slice_index ssl (sint.Z iv) _ true) $$ [Hssl] as Hssl
    · iframe Hssl; ipureintro; rw [Ht.2.2.1]
      exact ⟨hiv0, w_Z_lt_nat hiv0 Hm.1 hivm⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists t + W64 1, _, p
    simp only [named]
    iframe
    ipureintro
    have htt : sint.nat (t + W64 1) = sint.nat t + 1 := w_nat_succ Ht.1 HifR
    refine ⟨w_succ_nonneg Ht.1 HifR, by rw [htt]; omega, by simp [Ht.2.2.1], ?_⟩
    intro j' hj' ⟨y, hy, hyk⟩
    rw [htt, List.take_succ, hx] at hy
    rcases List.mem_append.1 hy with hy | hy
    · have := Ht.2.2.2 j' hj' ⟨y, hy, hyk⟩
      rw [List.getElem?_set]
      by_cases hij : (sint.Z iv).toNat = j'
      · rw [if_pos hij, if_pos (by rw [Ht.2.2.1]; omega)]
      · rw [if_neg hij]; exact this
    · simp at hy
      subst hy
      have hj'x : j' = jx := huniq j' hj' hyk
      have hij : (sint.Z iv).toNat = j' := by rw [hj'x, ← hivx]; (try rfl)
      rw [List.getElem?_set, if_pos hij, if_pos (by rw [Ht.2.2.1]; omega)]
  -- after the check loop: every key-value checked
  have htall : sint.nat t = mr.kvs.length := by
    have h1 := Hsll.1; rw [Hplen] at h1; have h2 := Ht.2.1; have h3 := w_nat_le Hsll.2 Hif; omega
  (try wp_auto)
  -- the last loop: every acknowledged put is seen
  ihave IA : (∃ (q : w64), "i" ∷ i_ptr ↦ q ∗ "%Hq" ∷ ⌜0 ≤ sint.Z q⌝ : IProp GF) $$ [i]
  · iexists W64 0
    simp only [named]
    iframe
    ipureintro; decide
  wp_for IA
  wp_if_destruct
  · have HifQ : sint.Z q < sint.Z m := Hif
    have hqm : sint.nat q < sint.nat m := w_nat_lt Hq HifQ
    have Hbq : 0 ≤ sint.Z q ∧ sint.Z q < sint.Z asl.len :=
      ⟨Hq, w_Z_lt Hq Haslen.2 (by have h := Haslen.1; simp at h; omega)⟩
    obtain ⟨b, hb⟩ : ∃ b, (acks ++ List.replicate (sint.nat m - acks.length) false)[sint.nat q]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
    (try simp only [Hbq, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index asl (sint.Z q) _ _ b Hq $$ [Hasl] as Hasl
    · iframe Hasl; ipureintro; exact hb
    (try wp_auto)
    cases b
    · (try wp_auto)
      wp_for_post
      iframe
      iexists q + W64 1
      simp only [named]
      iframe
      ipureintro; exact w_succ_nonneg Hq HifQ
    · -- acknowledged: seen
      have hack : acks[sint.nat q]? = some true := by
        rwa [List.getElem?_append_left (by omega)] at hb
      obtain ⟨y, hy, hyk⟩ := Hrd.2 (sint.nat q) hack
      have hseen : ss[sint.nat q]? = some true := by
        apply Ht.2.2.2 _ hqm
        refine ⟨y, ?_, hyk⟩
        rw [htall, List.take_length, hview]
        exact hy
      have Hbq' : 0 ≤ sint.Z q ∧ sint.Z q < sint.Z ssl.len :=
        ⟨Hq, w_Z_lt Hq Hssllen.2 (by have h := Hssllen.1; simp at h; omega)⟩
      (try wp_auto)
      (try simp only [Hbq', _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index ssl (sint.Z q) _ _ true Hq $$ [Hssl] as Hssl
      · iframe Hssl; ipureintro; exact hseen
      (try wp_auto)
      wp_for_post
      iframe
      iexists q + W64 1
      simp only [named]
      iframe
      ipureintro; exact w_succ_nonneg Hq HifQ
  (try wp_auto)
  wp_apply wp_checked as %r -
  (try wp_auto)
  wp_apply wp_Close as %ce -
  · iframe #
  (try wp_auto)
  iapply HΦ; iframe Hlt

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
