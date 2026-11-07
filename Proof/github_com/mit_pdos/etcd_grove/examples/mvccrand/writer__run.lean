/- Lean-first (no Rocq counterpart). The proof of `writer.run`: the loop's invariant is `runSt` at
the index `n` last applied, with `vals ≤ v + 3n`, `nextID ≤ nid + n` and `ops - n` write tokens; each
iteration stores `n + 1` in `applying` (the writer owns it: `hookPre`), runs the operation `intn(20)`
picks (its spec; `Commit` by `KV.Commit.contract` at the tester's backend, whose commit request for
`X = Y = True` is `backend.commitReq_true`), and maybe sends the published revision on the ticks
(`writer.cur`, a tick by `writer_pub_tick`, `wp_spsc_send`); the loop ends with the channel's close
(`wp_spsc_close`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__cur
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__intn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__put
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__deleteRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__txn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__grant
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__revoke
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__checkLeases
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__read
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

private theorem hookPre_of_post (wv : writer) (i : w64) :
    hookPost (GF := GF) wv i ⊢ hookPre wv i i := by
  unfold hookPost hookPre
  iintro ⟨Ha, Hs⟩
  iframe
  ipureintro; exact Int.le_refl _

private theorem hookPre_of_or (wv : writer) (i s : w64) :
    hookPost (GF := GF) wv i ∨ hookPre wv i s ⊢ ∃ s', hookPre wv i s' := by
  iintro (H | H)
  · iexists i; iapply hookPre_of_post $$ H
  · iexists s; iexact H

/-! ### One operation of the loop, from its state at the index `i` being applied -/

section steps
variable (w : Loc) (wv : writer) (γ : RandNames) (B : KBReal) (f : GoFunc) (q : Qp) (T R : IProp GF)
  (i : w64) (nv nid : Int) (k : Nat)

private theorem step_put (wp_put : writer.put.spec (GF := GF) (hG := hG)) (hnv : nv + 3 < 2 ^ 63) :
    {{ writerCtx w wv γ (etcdStorage B) f ∗ runSt w wv γ B f q T R i nv nid k }}
      (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"put")) (Val #i))
    {{ RET #(); runSt w wv γ B f q T R i (nv + 3) (nid + 1) (k - 1) }} := by
  iintro %Φ ⟨Hctx, Hst⟩ HΦ
  iunfold runSt at Hst
  icases Hst with ⟨%σ, %Hs, %L, %n, %k', %s, %v, Hown, Hle, Hpre, Hvals, %Hb⟩
  wp_apply (wp_put w wv γ (etcdStorage B) f q σ Hs L i s v Hb.1 (by omega))
    $$ [$Hctx $Hown $Hpre $Hvals] as ⟨⟨%σ', %Hs', Hown⟩, Hpost, Hvals⟩
  iapply HΦ
  ihave Hpre := hookPre_of_post wv i $$ Hpost
  iunfold runSt
  iexists σ', Hs', L, n, k', i, v + W64 1
  iframe
  ipureintro
  have : sint.Z (v + W64 1) = sint.Z v + 1 := by word
  omega

private theorem step_deleteRange (wp_deleteRange : writer.deleteRange.spec (GF := GF) (hG := hG)) :
    {{ writerCtx w wv γ (etcdStorage B) f ∗ runSt w wv γ B f q T R i nv nid k }}
      (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"deleteRange")) (Val #i))
    {{ RET #(); runSt w wv γ B f q T R i (nv + 3) (nid + 1) (k - 1) }} := by
  iintro %Φ ⟨Hctx, Hst⟩ HΦ
  iunfold runSt at Hst
  icases Hst with ⟨%σ, %Hs, %L, %n, %k', %s, %v, Hown, Hle, Hpre, Hvals, %Hb⟩
  wp_apply (wp_deleteRange w wv γ (etcdStorage B) f q σ Hs L i s)
    $$ [$Hctx $Hown $Hpre] as ⟨⟨%σ', %Hs', Hown⟩, Hpost⟩
  iapply HΦ
  ihave Hpre := hookPre_of_post wv i $$ Hpost
  iunfold runSt
  iexists σ', Hs', L, n, k', i, v
  iframe
  ipureintro; omega

private theorem step_txn (wp_txn : writer.txn.spec (GF := GF) (hG := hG)) (hnv : nv + 3 < 2 ^ 63) :
    {{ writerCtx w wv γ (etcdStorage B) f ∗ runSt w wv γ B f q T R i nv nid k }}
      (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"txn")) (Val #i))
    {{ RET #(); runSt w wv γ B f q T R i (nv + 3) (nid + 1) (k - 1) }} := by
  iintro %Φ ⟨Hctx, Hst⟩ HΦ
  iunfold runSt at Hst
  icases Hst with ⟨%σ, %Hs, %L, %n, %k', %s, %v, Hown, Hle, Hpre, Hvals, %Hb⟩
  wp_apply (wp_txn w wv γ (etcdStorage B) f q σ Hs L i s v Hb.1 (by omega))
    $$ [$Hctx $Hown $Hpre $Hvals] as ⟨⟨%σ', %Hs', Hown⟩, Hpost, %v', Hvals, %Hv'⟩
  iapply HΦ
  icases hookPre_of_or wv i s $$ Hpost with ⟨%s', Hpre⟩
  iunfold runSt
  iexists σ', Hs', L, n, k', s', v'
  iframe
  ipureintro; omega

private theorem step_grant (wp_grant : writer.grant.spec (GF := GF) (hG := hG))
    (hnid : nid + 1 < 2 ^ 63) (hk : 1 ≤ k) :
    {{ writerCtx w wv γ (etcdStorage B) f ∗ runSt w wv γ B f q T R i nv nid k }}
      (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"grant")) (Val #i))
    {{ RET #(); runSt w wv γ B f q T R i (nv + 3) (nid + 1) (k - 1) }} := by
  iintro %Φ ⟨Hctx, Hst⟩ HΦ
  iunfold runSt at Hst
  icases Hst with ⟨%σ, %Hs, %L, %n, %k', %s, %v, Hown, Hle, Hpre, Hvals, %Hb⟩
  wp_apply (wp_grant w wv γ B f q σ Hs L n k' T R i s (by omega) (by omega))
    $$ [$Hctx $Hown $Hle $Hpre] as ⟨Hown, Hle, Hpost⟩
  iapply HΦ
  ihave Hpre := hookPre_of_post wv i $$ Hpost
  iunfold runSt
  iexists σ, Hs, L ++ [n + W64 1], n + W64 1, k' - 1, i, v
  iframe
  ipureintro
  have : sint.Z (n + W64 1) = sint.Z n + 1 := by word
  omega

private theorem step_revoke (wp_revoke : writer.revoke.spec (GF := GF) (hG := hG)) :
    {{ writerCtx w wv γ (etcdStorage B) f ∗ runSt w wv γ B f q T R i nv nid k }}
      (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"revoke")) (Val #i))
    {{ RET #(); runSt w wv γ B f q T R i (nv + 3) (nid + 1) (k - 1) }} := by
  iintro %Φ ⟨Hctx, Hst⟩ HΦ
  iunfold runSt at Hst
  icases Hst with ⟨%σ, %Hs, %L, %n, %k', %s, %v, Hown, Hle, Hpre, Hvals, %Hb⟩
  wp_apply (wp_revoke w wv γ B f q σ Hs L n k' T R i s)
    $$ [$Hctx $Hown $Hle $Hpre] as ⟨%σ', %Hs', %id, Hown, Hle, Hpost⟩
  iapply HΦ
  icases hookPre_of_or wv i s $$ Hpost with ⟨%s', Hpre⟩
  iunfold runSt
  iexists σ', Hs', L.filter (· != id), n, k', s', v
  iframe
  ipureintro; omega

private theorem step_checkLeases (wp_checkLeases : writer.checkLeases.spec (GF := GF) (hG := hG)) :
    {{ writerCtx w wv γ (etcdStorage B) f ∗ runSt w wv γ B f q T R i nv nid k }}
      (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"checkLeases")) (Val #()))
    {{ RET #(); runSt w wv γ B f q T R i (nv + 3) (nid + 1) (k - 1) }} := by
  iintro %Φ ⟨Hctx, Hst⟩ HΦ
  iunfold runSt at Hst
  icases Hst with ⟨%σ, %Hs, %L, %n, %k', %s, %v, Hown, Hle, Hpre, Hvals, %Hb⟩
  wp_apply (wp_checkLeases w wv γ B f q σ Hs L n k' T R) $$ [$Hctx $Hown $Hle] as ⟨Hown, Hle⟩
  iapply HΦ
  iunfold runSt
  iexists σ, Hs, L, n, k', s, v
  iframe
  ipureintro; omega

private theorem step_read (wp_read : writer.read.spec (GF := GF) (hG := hG)) :
    {{ writerCtx w wv γ (etcdStorage B) f ∗ runSt w wv γ B f q T R i nv nid k }}
      (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"read")) (Val #()))
    {{ RET #(); runSt w wv γ B f q T R i (nv + 3) (nid + 1) (k - 1) }} := by
  iintro %Φ ⟨Hctx, Hst⟩ HΦ
  iunfold runSt at Hst
  icases Hst with ⟨%σ, %Hs, %L, %n, %k', %s, %v, Hown, Hle, Hpre, Hvals, %Hb⟩
  wp_apply (wp_read w wv γ (etcdStorage B) f q σ Hs L) $$ [$Hctx $Hown] as Hown
  iapply HΦ
  iunfold runSt
  iexists σ, Hs, L, n, k', s, v
  iframe
  ipureintro; omega

/-- `w.kv.Commit()`: the tester's backend's commit request for `X = Y = True` is trivial. -/
private theorem step_commit (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (kty : go.GoType) (kvv : val) (hkv : wv.kv' = interface.mkOk kty kvv)
    (hCommit : mvcc.api.KV.Commit.contract (GF := GF) (hG := hG) kty kvv) :
    {{ writerCtx w wv γ (etcdStorage B) f ∗ runSt w wv γ B f q T R i nv nid k }}
      (App (Val #(methods kty go!"Commit" kvv)) (Val #()))
    {{ RET #(); runSt w wv γ B f q T R i (nv + 3) (nid + 1) (k - 1) }} := by
  haveI := fun kv γ => hpers.1 kv γ
  iintro %Φ ⟨Hctx, Hst⟩ HΦ
  iunfold writerCtx at Hctx
  icases Hctx with ⟨-, #Hmpkg, -, -, -, -, #Hkv, -, -⟩
  iunfold runSt at Hst
  icases Hst with ⟨%σ, %Hs, %L, %n, %k', %s, %v, Hown, Hle, Hpre, Hvals, %Hb⟩
  iunfold writerOwn at Hown
  icases Hown with ⟨Htt, Hrdr, Hbk, Hrd, Hidle, Hg, Hlm, Hlo⟩
  rw [hkv] at *
  ihave #Hreq : mvcc.api.storageReq (etcdStorage B) iprop(True) iprop(True) iprop(True) $$ []
  · rw [etcdStorage_req]; iapply backend.commitReq_true
  iapply (hCommit γ.kv q (etcdStorage B) iprop(True) iprop(True) iprop(True)) $$ [Htt Hrdr Hbk]
  · iframe Hmpkg Hkv Htt Hrdr Hbk Hreq
  inext
  iintro ⟨Htt, Hrdr, Hbk, -⟩
  iapply HΦ
  iunfold runSt
  iexists σ, Hs, L, n, k', s, v
  iunfold writerOwn
  iframe
  ipureintro; omega

end steps

theorem writer.run.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (wp_intn : rng.intn.spec (GF := GF) (hG := hG))
    (wp_cur : writer.cur.spec (GF := GF) (hG := hG))
    (wp_put : writer.put.spec (GF := GF) (hG := hG))
    (wp_deleteRange : writer.deleteRange.spec (GF := GF) (hG := hG))
    (wp_txn : writer.txn.spec (GF := GF) (hG := hG))
    (wp_grant : writer.grant.spec (GF := GF) (hG := hG))
    (wp_revoke : writer.revoke.spec (GF := GF) (hG := hG))
    (wp_checkLeases : writer.checkLeases.spec (GF := GF) (hG := hG))
    (wp_read : writer.read.spec (GF := GF) (hG := hG)) :
    writer.run.spec (GF := GF) (hG := hG) := by
  intro w wv γ B f q σ Hs L nid k T R s v ops γt hops0 hops1 hopsk hv0 hv1 hnid
  haveI := fun kv γ => hpers.1 kv γ
  haveI : Persistent (writerCtx (GF := GF) w wv γ (etcdStorage B) f) := by
    unfold writerCtx hookOk; infer_instance
  wp_start as ⟨#Hctx, Hown, Hle, Hpre, Hvals, Hticks⟩
  ihave #Hctx2 := Hctx
  iunfold writerCtx at Hctx2
  icases Hctx2 with ⟨#Hpkg, #Hmpkg, #Htpkg, #Hw, #Hinv, #Hhist, #Hkv, #Hhook, #Hhok⟩
  ihave #Hw2 := Hw
  iunfold writerRO at Hw2
  icases Hw2 with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  iunfold ticksW at Hticks
  icases Hticks with ⟨#Hch, %sent, Hprod⟩
  ihave #HisC : isChan wv.ticks' γt.chanName w64 $$ [Hch]
  · iunfold isTicks at Hch; iunfold isSpsc at Hch; icases Hch with ⟨$, -⟩
  ihave #Hsp : isSpsc (V := w64) γt wv.ticks' (tickP γ) (fun _ => iprop(True)) $$ [Hch]
  · iunfold isTicks at Hch; iexact Hch
  wp_auto
  -- `every`
  wp_apply (chan.wp_cap (V := w64) wv.ticks' γt.chanName) $$ [$HisC]
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun x => iprop(⌜x = executeVal⌝ ∗ ops_ptr ↦ ops ∗ w_ptr ↦ w ∗
      ∃ ev : w64, every_ptr ↦ ev ∗ ⌜1 ≤ sint.Z ops → 1 ≤ sint.Z ev⌝))) $$ [every ops w]
  · wp_if_destruct
    · wp_apply (chan.wp_cap (V := w64) wv.ticks' γt.chanName) $$ [$HisC]
      (try wp_auto)
      have hc0 : sint.Z γt.chanName.chanCap > 0 := by simpa using Hif
      simp only [show sint.Z γt.chanName.chanCap ≠ 0 by omega, ↓reduceIte]
      (try wp_auto)
      have key : 1 ≤ sint.Z (BitVec.sdiv ops γt.chanName.chanCap + W64 1) := by
        have hne : γt.chanName.chanCap ≠ -1#64 := by
          intro h; rw [h] at hc0; exact absurd hc0 (by decide)
        have hq : sint.Z (BitVec.sdiv ops γt.chanName.chanCap) =
            (sint.Z ops).tdiv (sint.Z γt.chanName.chanCap) :=
          BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr hne)
        have h1 : 0 ≤ sint.Z (BitVec.sdiv ops γt.chanName.chanCap) := by
          rw [hq]; exact Int.tdiv_nonneg hops0 (by omega)
        have h2 : sint.Z (BitVec.sdiv ops γt.chanName.chanCap) ≤ sint.Z ops := by
          rw [hq]; exact Int.tdiv_le_self _ hops0
        word
      iframe
      ipureintro
      exact ⟨rfl, fun _ => key⟩
    · (try wp_auto)
      iframe
      ipureintro; exact id
  iintro %x ⟨%hx, ops, w, %ev, every, %Hev⟩
  subst hx
  (try wp_auto)
  ihave %Hsh := hsh.1 wv.kv' γ.kv $$ Hkv
  obtain ⟨kty, kvv, hkvE, -, -, -, -, -, -, -, -, hCommitC, -⟩ := Hsh
  -- the loop
  ihave HI : (∃ (nv : w64),
      "n" ∷ n_ptr ↦ nv ∗ "ops" ∷ ops_ptr ↦ ops ∗ "w" ∷ w_ptr ↦ w ∗ "every" ∷ every_ptr ↦ ev ∗
      "Hst" ∷ runSt w wv γ B f q T R nv (sint.Z v + 3 * sint.Z nv) (sint.Z nid + sint.Z nv)
        (sint.Z ops - sint.Z nv).toNat ∗
      "Hprod" ∷ (∃ sent : List w64, spscProducer (V := w64) γt sent) ∗
      ⌜0 ≤ sint.Z nv ∧ sint.Z nv ≤ sint.Z ops⌝ : IProp GF) $$ [n ops w every Hown Hle Hpre Hvals Hprod]
  · iexists W64 0
    iframe
    isplitl [Hown Hle Hpre Hvals]
    · iunfold runSt
      iexists σ, Hs, L, nid, k, s, v
      iframe
      ipureintro
      have : sint.Z (W64 0) = 0 := rfl
      omega
    isplitl [Hprod]
    · iexists sent; iframe
    ipureintro
    have : sint.Z (W64 0) = 0 := rfl
    omega
  wp_for HI
  icases HI with %HIp
  obtain ⟨hn0, hn1⟩ := HIp
  wp_if_destruct
  · -- one more operation
    have hlt : sint.Z nv < sint.Z ops := by
      exact Classical.byContradiction fun h => absurd Hif (by simp [h])
    have hnv1 : sint.Z (nv + W64 1) = sint.Z nv + 1 := by word
    (try wp_auto)
    -- `applying.Store(n + 1)`
    iunfold runSt at Hst
    icases Hst with ⟨%σ1, %Hs1, %L1, %n1, %k1, %s1, %v1, Hown, Hle, Hpre, Hvals, %Hb⟩
    iunfold hookPre at Hpre
    icases Hpre with ⟨Happ, Hsav, %Hsle⟩
    wp_apply_core sync.atomic.Int64.wp_Store wv.applying' (nv + W64 1) $$ [] [-]
    · iPkgInit
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iexists _
    iframe Happ
    iintro Happ
    imod Hcl with -
    imodintro
    (try wp_auto)
    -- `intn(20)`
    iunfold writerOwn at Hown
    icases Hown with ⟨Htt, Hrdr, Hbk, Hrd, Hidle, ⟨%g, Hg⟩, Hlm, Hlo⟩
    wp_apply wp_intn wv.r' g (W64 20) (by decide) $$ [$Hpkg $Hg] as %x ⟨Hg, %Hx⟩
    ihave Hst : runSt w wv γ B f q T R (nv + W64 1) (sint.Z v + 3 * sint.Z nv)
        (sint.Z nid + sint.Z nv) (sint.Z ops - sint.Z nv).toNat
      $$ [Htt Hrdr Hbk Hrd Hidle Hg Hlm Hlo Hle Happ Hsav Hvals]
    · iunfold runSt
      iexists σ1, Hs1, L1, n1, k1, s1, v1
      iunfold writerOwn
      iunfold hookPre
      iframe
      ipureintro
      exact ⟨by omega, Hb⟩
    (try wp_auto)
    -- the operation
    have hb3 : sint.Z v + 3 * sint.Z nv + 3 < 2 ^ 63 := by omega
    have hb1 : sint.Z nid + sint.Z nv + 1 < 2 ^ 63 := by omega
    have hk1 : 1 ≤ (sint.Z ops - sint.Z nv).toNat := by omega
    obtain ⟨j, hj, rfl⟩ : ∃ j : Nat, j < 20 ∧ x = W64 (j : Int) :=
      ⟨(sint.Z x).toNat, by word, by word⟩
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun r => iprop(⌜r = executeVal⌝ ∗ w_ptr ↦ w ∗
        runSt w wv γ B f q T R (nv + W64 1) (sint.Z v + 3 * sint.Z nv + 3)
          (sint.Z nid + sint.Z nv + 1) ((sint.Z ops - sint.Z nv).toNat - 1)))) $$ [w i Hst]
    · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨
          j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨
          j = 18 ∨ j = 19 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      all_goals (try wp_auto)
      all_goals first
        | wp_apply (step_put w wv γ B f q T R (nv + W64 1) _ _ _ wp_put (by omega))
            $$ [$Hctx $Hst] as Hst
        | wp_apply (step_deleteRange w wv γ B f q T R (nv + W64 1) _ _ _ wp_deleteRange)
            $$ [$Hctx $Hst] as Hst
        | wp_apply (step_txn w wv γ B f q T R (nv + W64 1) _ _ _ wp_txn (by omega))
            $$ [$Hctx $Hst] as Hst
        | wp_apply (step_grant w wv γ B f q T R (nv + W64 1) _ _ _ wp_grant (by omega) hk1)
            $$ [$Hctx $Hst] as Hst
        | wp_apply (step_revoke w wv γ B f q T R (nv + W64 1) _ _ _ wp_revoke)
            $$ [$Hctx $Hst] as Hst
        | wp_apply (step_checkLeases w wv γ B f q T R (nv + W64 1) _ _ _ wp_checkLeases)
            $$ [$Hctx $Hst] as Hst
        | wp_apply (step_read w wv γ B f q T R (nv + W64 1) _ _ _ wp_read)
            $$ [$Hctx $Hst] as Hst
        | (rw [hkvE]; (try wp_auto)
           wp_apply (step_commit w wv γ B f q T R (nv + W64 1) _ _ _ hpers kty kvv hkvE hCommitC)
            $$ [$Hctx $Hst] as Hst)
      all_goals ((try wp_auto); iframe; try (ipureintro; rfl))
    iintro %r ⟨%hr, w, Hst⟩
    subst hr
    (try wp_auto)
    -- the tick: `n % every == 0 && len(w.ticks) < cap(w.ticks)`, then `w.ticks <- w.cur()`
    have hev : 1 ≤ sint.Z ev := Hev (by omega)
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun r => iprop(⌜r = executeVal⌝ ∗ w_ptr ↦ w ∗
        runSt w wv γ B f q T R (nv + W64 1) (sint.Z v + 3 * sint.Z nv + 3)
          (sint.Z nid + sint.Z nv + 1) ((sint.Z ops - sint.Z nv).toNat - 1) ∗
        (∃ sent : List w64, spscProducer (V := w64) γt sent) ∗ n_ptr ↦ nv ∗ every_ptr ↦ ev)))
      $$ [w Hst Hprod n every]
    · (try wp_auto)
      simp only [show sint.Z ev ≠ 0 by omega, ↓reduceIte]
      (try wp_auto)
      by_cases hm : BitVec.srem nv ev = W64 0
      · simp only [hm, _root_.decide_true]
        (try wp_auto)
        wp_func_call
        wp_apply (wp_Len (V := w64) (t := go.int64) wv.ticks' γt.chanName) $$ [$HisC] as %l %Hl
        (try wp_auto)
        wp_apply (chan.wp_cap (V := w64) wv.ticks' γt.chanName) $$ [$HisC]
        (try wp_auto)
        wp_if_destruct
        · -- `w.ticks <- w.cur()`: the published revision, a tick
          iunfold runSt at Hst
          icases Hst with ⟨%σ2, %Hs2, %L2, %n2, %k2, %s2, %v2, Hown, Hle, Hpre, Hvals, %Hb2⟩
          iunfold writerOwn at Hown
          icases Hown with ⟨Htt, Hrdr, Hbk, Hrd, Hidle, Hg, Hlm, Hlo⟩
          iunfold writerIdle at Hidle
          icases Hidle with ⟨Hgσ, HW, Hpv, %Hid⟩
          wp_apply wp_cur w wv γ (W64 (σ2.rev : Int)) $$ [$Hpkg $Hw $Hinv $Hpv] as Hpv
          icases Hprod with ⟨%sent2, Hprod⟩
          imod writer_pub_tick hpers wv.h' γ (W64 (σ2.rev : Int)) (sent2.length : Int)
            $$ [$Hinv $Hpv] with ⟨Hpv, #Htick⟩
          (try wp_auto)
          wp_apply (wp_spsc_send (t := go.int64) γt wv.ticks' (tickP γ) (fun _ => iprop(True))
              sent2 (W64 (σ2.rev : Int))) $$ [$Hsp $Hprod $Htick] as Hprod
          (try wp_auto)
          ihave Hst : runSt w wv γ B f q T R (nv + W64 1) (sint.Z v + 3 * sint.Z nv + 3)
              (sint.Z nid + sint.Z nv + 1) ((sint.Z ops - sint.Z nv).toNat - 1)
            $$ [Htt Hrdr Hbk Hrd Hgσ HW Hpv Hg Hlm Hlo Hle Hpre Hvals]
          · iunfold runSt
            iexists σ2, Hs2, L2, n2, k2, s2, v2
            iunfold writerOwn
            iunfold writerIdle
            iframe
            ipureintro; exact ⟨Hid, Hb2⟩
          iframe
          try (ipureintro; rfl)
        · (try wp_auto)
          iframe
      · simp only [hm, _root_.decide_false]
        (try wp_auto)
        iframe
        ipureintro; rfl
    iintro %r ⟨%hr, w, Hst, Hprod, n, every⟩
    subst hr
    (try wp_auto)
    wp_for_post
    iframe
    iexists nv + W64 1
    iframe
    isplitl [Hst]
    · have e1 : sint.Z v + 3 * sint.Z (nv + W64 1) = sint.Z v + 3 * sint.Z nv + 3 := by omega
      have e2 : sint.Z nid + sint.Z (nv + W64 1) = sint.Z nid + sint.Z nv + 1 := by omega
      have e3 : (sint.Z ops - sint.Z (nv + W64 1)).toNat = (sint.Z ops - sint.Z nv).toNat - 1 := by
        omega
      rw [e1, e2, e3]; iexact Hst
    ipureintro; omega
  · -- the loop's end: `close(w.ticks)`
    have hge : sint.Z ops ≤ sint.Z nv := Int.not_lt.mp Hif
    have hnv : nv = ops := BitVec.eq_of_toInt_eq (by show sint.Z nv = sint.Z ops; omega)
    subst hnv
    (try wp_auto)
    icases Hprod with ⟨%sent', Hprod⟩
    wp_apply (wp_spsc_close (t := go.int64) γt wv.ticks' (tickP γ) (fun _ => iprop(True)) sent')
      $$ [$Hsp $Hprod]
    (try wp_auto)
    iapply HΦ
    have e3 : (sint.Z nv - sint.Z nv).toNat = 0 := by omega
    rw [e3] at *
    iexact Hst

end proof

end mvccrand
end EtcdGrove
end Perennial
