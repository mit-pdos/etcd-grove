/-
The writer's loop (`runner.write`): the members' parts restated at a longer log. Lean-first (no
Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

theorem runM_snoc (ks : List GoString) (ops : List OpM) (o : OpM) (n : Nat) (hn : n ≤ ops.length) :
    runM ks (ops ++ [o]) n = runM ks ops n :=
  runM_prefix ks ops (ops ++ [o]) n (List.prefix_append _ _) hn

/-- **The log extended by an operation valid at its end is valid.** -/
theorem logOk_snoc (ks : List GoString) (ops : List OpM) (o : OpM) (h : logOk ks ops)
    (ho : opValid ks (runM ks ops ops.length) o) : logOk ks (ops ++ [o]) := by
  intro i o' hi
  by_cases hlt : i < ops.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [runM_snoc ks ops o i (by omega)]
    exact h i o' hi
  · have hi' : i = ops.length := by
      have := (List.getElem?_eq_some_iff.1 hi).1
      simp at this; omega
    subst hi'
    rw [List.getElem?_append_right (by omega)] at hi
    simp at hi
    subst hi
    rw [runM_snoc ks ops o ops.length (by omega)]
    exact ho

end model

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A member's part at a longer log** (its count within the shorter one). -/
theorem memCore_snoc (ks : List GoString) (γh : HistNames) (ops : List OpM) (o : OpM) (i : Nat)
    (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat)
    (hn : v.ops ≤ ops.length) :
    memCore (GF := GF) ks γh ops i mp m f v qw nw k ⊢ memCore ks γh (ops ++ [o]) i mp m f v qw nw k := by
  have h := runM_snoc ks ops o v.ops hn
  have hl : v.ops ≤ (ops ++ [o]).length := by simp; omega
  unfold memCore σOf histAt cmpAfter revAfter leasesAfter grantedAfter
  simp only [h, eq_true hn, eq_true hl]
  exact .rfl

theorem memW_snoc (ks : List GoString) (γh : HistNames) (ops : List OpM) (o : OpM) (i : Nat)
    (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat)
    (hn : v.ops ≤ ops.length) :
    memW (GF := GF) ks γh ops i mp m f v qw nw k ⊢ memW ks γh (ops ++ [o]) i mp m f v qw nw k := by
  unfold memW
  iintro ⟨Ho, Hh, Hc⟩
  iframe
  iapply memCore_snoc ks γh ops o i mp m f v qw nw k hn
  iexact Hc

/-- **The follower's part for its next operation** (`apply(f, x.log[f.ops], false)`): the log's
slice and the operation at the follower's count, the follower's `memW`, the history's reader slot
and its lower bound after that operation; and back, at the follower's new record. -/
theorem writerOwn_follower (x : Loc) (ks : List GoString) (cfg : Config) (h : Loc) (γ : FullNames)
    (mp0 mp1 : Loc) (f0 f1 : GoFunc) (ops : List OpM) (v0 v1 : MemS) (nv nb : Nat) (q qs : Qp)
    (hlt : v1.ops < v0.ops) :
    writerOwn (GF := GF) x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs ⊢
      ∃ (sl : GoSlice) (ps : List Loc) (p : Loc) (o : OpM) (qw : Qp) (nw k : Nat),
        rF go!"log" x ↦ sl ∗ sl ↦* ps ∗
        ⌜ps[v1.ops]? = some p ∧ ops[v1.ops]? = some o ∧ logOk ks ops ∧ 1 ≤ nw ∧
          (sint.Z cfg.Ops').toNat ≤ k + v1.ops ∧ v1.ops < ops.length ∧
          ops.length ≤ (sint.Z cfg.Ops').toNat⌝ ∗
        opIs p o ∗ memW ks γ.h ops 1 mp1 γ.m1 f1 v1 qw nw k ∗ histRd h γ.h ∗
        monoListLbOwn γ.h.l (histAt ks ops (v1.ops + 1)) ∗
        (∀ (v1' : MemS) (k' : Nat), rF go!"log" x ↦ sl -∗ sl ↦* ps -∗
          memW ks γ.h ops 1 mp1 γ.m1 f1 v1' qw nw k' -∗ histRd h γ.h -∗
          ⌜MemS.sameInc v1 v1' ∧ v1'.ops = v1.ops + 1 ∧ k ≤ k' + 1⌝ -∗
          writerOwn x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1' nv nb q qs) := by
  iintro Hown
  iunfold writerOwn at Hown
  icases Hown with ⟨Hms, Hreg0, Hreg1, Hlog, Hctrs, HhW, Hrd, %HopsA, %HnbA, Hfiles,
    ⟨%qw0, %nw0, %k0, Hm0, %Hl0⟩, ⟨%qw1, %nw1, %k1, Hm1, %Hl1⟩, Hss0, Hss1, Hadd⟩
  iunfold logOwn at Hlog
  icases Hlog with ⟨%sl, %ps, Hlsl, Hps, Hcap, %Hlp, #Hopis⟩
  have hl : v1.ops < ops.length := by omega
  obtain ⟨o, ho⟩ : ∃ o, ops[v1.ops]? = some o := ⟨_, List.getElem?_eq_getElem hl⟩
  obtain ⟨p, hp⟩ : ∃ p, ps[v1.ops]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hlp.1]; exact hl)⟩
  have hz : (ps.zip ops)[v1.ops]? = some (p, o) := by
    rw [List.getElem?_zip_eq_some]; exact ⟨hp, ho⟩
  ihave #Hop := (BigSepL.bigSepL_lookup (Φ := fun _ x => opIs (GF := GF) x.1 x.2) hz) $$ Hopis
  icases histW_lb γ.h _ _ $$ HhW with ⟨HhW, #Hlb⟩
  ihave #Hlb' := monoListLbOwn_le (histAt ks ops (v1.ops + 1))
    (runM_hs_prefix ks ops (v1.ops + 1) ops.length (by omega)) $$ Hlb
  iexists sl, ps, p, o, qw1, nw1, k1
  iframe Hlsl Hps Hm1 Hrd Hop Hlb'
  isplitr
  · ipureintro; exact ⟨hp, ho, Hlp.2, Hl1.2.1, Hl1.2.2, hl, HopsA.2.2⟩
  iintro %v1' %k' Hlsl Hps Hm1 Hrd %Hs
  obtain ⟨⟨hpa, hlp, hkv, hbk, hι⟩, hops, hk⟩ := Hs
  iunfold writerOwn
  dsimp only
  rw [hkv, hι]
  iframe Hms Hreg0 Hreg1 Hctrs HhW Hrd Hfiles Hss0 Hss1 Hadd
  isplitl [Hlsl Hps Hcap]
  · iunfold logOwn; iexists sl, ps; iframe; iframe #; ipureintro; exact Hlp
  isplitr
  · ipureintro; omega
  isplitr
  · ipureintro; omega
  isplitl [Hm0]
  · iexists qw0, nw0, k0; iframe; ipureintro; exact Hl0
  · iexists qw1, nw1, k'; iframe; ipureintro; exact ⟨Hl1.1, Hl1.2.1, by omega⟩

end lemmas

end mvccfull
end EtcdGrove
end Perennial
