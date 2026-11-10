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

/-- **The leader's part for a new operation** (`gen`, the log appended, `apply(l, o, true)`): the
log, the counters, the history's writer part, its reader slot, the leader's `memW`; and back at
the longer log, the leader's new record. -/
theorem writerOwn_leader (x : Loc) (ks : List GoString) (cfg : Config) (h : Loc) (γ : FullNames)
    (mp0 mp1 : Loc) (f0 f1 : GoFunc) (ops : List OpM) (v0 v1 : MemS) (nv nb : Nat) (q qs : Qp)
    (hlt : ops.length < (sint.Z cfg.Ops').toNat) :
    writerOwn (GF := GF) x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs ⊢
      ∃ (qw : Qp) (nw k : Nat), logOwn x ks ops ∗ writerCtrs x ks ops nv nb ∗
        histW γ.h (histAt ks ops ops.length) (compsAt ks ops ops.length) ∗ histRd h γ.h ∗
        memW ks γ.h ops 0 mp0 γ.m0 f0 v0 qw nw k ∗
        ⌜1 ≤ nw ∧ (sint.Z cfg.Ops').toNat ≤ k + v0.ops ∧ v0.ops = ops.length ∧ v1.ops ≤ v0.ops⌝ ∗
        (∀ (o : OpM) (v0' : MemS) (k' nv' : Nat), logOwn x ks (ops ++ [o]) -∗
          writerCtrs x ks (ops ++ [o]) nv' nb -∗
          histW γ.h (histAt ks (ops ++ [o]) (ops.length + 1)) (compsAt ks (ops ++ [o]) (ops.length + 1)) -∗
          histRd h γ.h -∗ memW ks γ.h (ops ++ [o]) 0 mp0 γ.m0 f0 v0' qw nw k' -∗
          ⌜MemS.sameInc v0 v0' ∧ v0'.ops = v0.ops + 1 ∧ k ≤ k' + 1⌝ -∗
          writerOwn x ks cfg h γ mp0 mp1 f0 f1 (ops ++ [o]) v0' v1 nv' nb q qs) := by
  iintro Hown
  iunfold writerOwn at Hown
  icases Hown with ⟨Hms, Hreg0, Hreg1, Hlog, Hctrs, HhW, Hrd, %HopsA, %HnbA, Hfiles,
    ⟨%qw0, %nw0, %k0, Hm0, %Hl0⟩, ⟨%qw1, %nw1, %k1, Hm1, %Hl1⟩, Hss0, Hss1, Hadd⟩
  iexists qw0, nw0, k0
  iframe Hlog Hctrs HhW Hrd Hm0
  isplitr
  · ipureintro; exact ⟨Hl0.2.1, Hl0.2.2, HopsA.1, HopsA.2.1⟩
  iintro %o %v0' %k' %nv' Hlog Hctrs HhW Hrd Hm0 %Hs
  obtain ⟨⟨hpa, hlp, hkv, hbk, hι⟩, hops, hk⟩ := Hs
  ihave Hm1 := memW_snoc ks γ.h ops o 1 mp1 γ.m1 f1 v1 qw1 nw1 k1 (by omega) $$ Hm1
  have hlen : (ops ++ [o]).length = ops.length + 1 := by simp
  iunfold writerOwn
  dsimp only
  rw [hkv, hι, hlen]
  iframe Hms Hreg0 Hreg1 Hlog Hctrs HhW Hrd Hfiles Hss0 Hss1 Hadd
  isplitr
  · ipureintro; omega
  isplitr
  · ipureintro; omega
  isplitl [Hm0]
  · iexists qw0, nw0, k'; iframe; ipureintro; exact ⟨Hl0.1, Hl0.2.1, by omega⟩
  · iexists qw1, nw1, k1; iframe; ipureintro; exact Hl1

/-- **The members' `ops` fields** (the loops' guards), and the counts' facts. -/
theorem writerOwn_ops (x : Loc) (ks : List GoString) (cfg : Config) (h : Loc) (γ : FullNames)
    (mp0 mp1 : Loc) (f0 f1 : GoFunc) (ops : List OpM) (v0 v1 : MemS) (nv nb : Nat) (q qs : Qp) :
    writerOwn (GF := GF) x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs ⊢
      ⌜v0.ops = ops.length ∧ v1.ops ≤ v0.ops ∧ ops.length ≤ (sint.Z cfg.Ops').toNat ∧
        nb ≤ v0.ops ∧ (nb = v0.ops → v1.ops = v0.ops)⌝ ∗
      mF go!"ops" mp0 ↦ (W64 (v0.ops : Int)) ∗ mF go!"ops" mp1 ↦ (W64 (v1.ops : Int)) ∗
      (mF go!"ops" mp0 ↦ (W64 (v0.ops : Int)) -∗ mF go!"ops" mp1 ↦ (W64 (v1.ops : Int)) -∗
        writerOwn x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs) := by
  iintro Hown
  iunfold writerOwn at Hown
  icases Hown with ⟨Hms, Hreg0, Hreg1, Hlog, Hctrs, HhW, Hrd, %HopsA, %HnbA, Hfiles,
    ⟨%qw0, %nw0, %k0, Hm0, %Hl0⟩, ⟨%qw1, %nw1, %k1, Hm1, %Hl1⟩, Hss0, Hss1, Hadd⟩
  iunfold memW at Hm0 Hm1
  icases Hm0 with ⟨Ho0, Hh0, Hc0⟩
  icases Hm1 with ⟨Ho1, Hh1, Hc1⟩
  iframe Ho0 Ho1
  isplitr
  · ipureintro; exact ⟨HopsA.1, HopsA.2.1, HopsA.2.2, HnbA⟩
  iintro Ho0 Ho1
  iunfold writerOwn
  dsimp only
  iframe Hms Hreg0 Hreg1 Hlog Hctrs HhW Hrd Hfiles Hss0 Hss1 Hadd
  isplitr
  · ipureintro; exact HopsA
  isplitr
  · ipureintro; exact HnbA
  isplitl [Ho0 Hh0 Hc0]
  · iexists qw0, nw0, k0; iunfold memW; iframe; ipureintro; exact Hl0
  · iexists qw1, nw1, k1; iunfold memW; iframe; ipureintro; exact Hl1

/-- **Member 0's store, for `checkLeases`**: its `memCore`, the history's reader slot and lower
bound at its count; and back. -/
theorem writerOwn_check0 (x : Loc) (ks : List GoString) (cfg : Config) (h : Loc) (γ : FullNames)
    (mp0 mp1 : Loc) (f0 f1 : GoFunc) (ops : List OpM) (v0 v1 : MemS) (nv nb : Nat) (q qs : Qp) :
    writerOwn (GF := GF) x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs ⊢
      ∃ (qw : Qp) (nw k : Nat), memCore ks γ.h ops 0 mp0 γ.m0 f0 v0 qw nw k ∗ histRd h γ.h ∗
        monoListLbOwn γ.h.l (histAt ks ops v0.ops) ∗ ⌜logOk ks ops⌝ ∗
        (memCore ks γ.h ops 0 mp0 γ.m0 f0 v0 qw nw k -∗ histRd h γ.h -∗
          writerOwn x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs) := by
  iintro Hown
  iunfold writerOwn at Hown
  icases Hown with ⟨Hms, Hreg0, Hreg1, Hlog, Hctrs, HhW, Hrd, %HopsA, %HnbA, Hfiles,
    ⟨%qw0, %nw0, %k0, Hm0, %Hl0⟩, ⟨%qw1, %nw1, %k1, Hm1, %Hl1⟩, Hss0, Hss1, Hadd⟩
  iunfold memW at Hm0
  icases Hm0 with ⟨Ho, Hh, Hc⟩
  ihave %Hlok : ⌜logOk ks ops⌝ $$ [Hlog]
  · iunfold logOwn at Hlog; icases Hlog with ⟨%sl, %ps, -, -, -, %Hlp, -⟩; ipureintro; exact Hlp.2
  icases histW_lb γ.h _ _ $$ HhW with ⟨HhW, #Hlb⟩
  ihave #Hlb' := monoListLbOwn_le (histAt ks ops v0.ops)
    (runM_hs_prefix ks ops v0.ops ops.length (by omega)) $$ Hlb
  iexists qw0, nw0, k0
  iframe Hc Hrd Hlb'
  isplitr
  · ipureintro; exact Hlok
  iintro Hc Hrd
  iunfold writerOwn
  dsimp only
  iframe Hms Hreg0 Hreg1 Hlog Hctrs HhW Hrd Hfiles Hss0 Hss1 Hadd
  isplitr
  · ipureintro; exact HopsA
  isplitr
  · ipureintro; exact HnbA
  isplitl [Ho Hh Hc]
  · iexists qw0, nw0, k0; iunfold memW; iframe; ipureintro; exact Hl0
  · iexists qw1, nw1, k1; iframe; ipureintro; exact Hl1

/-- **Member 1's store, for `checkLeases`**: its `memCore`, the history's reader slot and lower
bound at its count; and back. -/
theorem writerOwn_check1 (x : Loc) (ks : List GoString) (cfg : Config) (h : Loc) (γ : FullNames)
    (mp0 mp1 : Loc) (f0 f1 : GoFunc) (ops : List OpM) (v0 v1 : MemS) (nv nb : Nat) (q qs : Qp) :
    writerOwn (GF := GF) x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs ⊢
      ∃ (qw : Qp) (nw k : Nat), memCore ks γ.h ops 1 mp1 γ.m1 f1 v1 qw nw k ∗ histRd h γ.h ∗
        monoListLbOwn γ.h.l (histAt ks ops v1.ops) ∗ ⌜logOk ks ops⌝ ∗
        (memCore ks γ.h ops 1 mp1 γ.m1 f1 v1 qw nw k -∗ histRd h γ.h -∗
          writerOwn x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs) := by
  iintro Hown
  iunfold writerOwn at Hown
  icases Hown with ⟨Hms, Hreg0, Hreg1, Hlog, Hctrs, HhW, Hrd, %HopsA, %HnbA, Hfiles,
    ⟨%qw0, %nw0, %k0, Hm0, %Hl0⟩, ⟨%qw1, %nw1, %k1, Hm1, %Hl1⟩, Hss0, Hss1, Hadd⟩
  iunfold memW at Hm1
  icases Hm1 with ⟨Ho, Hh, Hc⟩
  ihave %Hlok : ⌜logOk ks ops⌝ $$ [Hlog]
  · iunfold logOwn at Hlog; icases Hlog with ⟨%sl, %ps, -, -, -, %Hlp, -⟩; ipureintro; exact Hlp.2
  icases histW_lb γ.h _ _ $$ HhW with ⟨HhW, #Hlb⟩
  ihave #Hlb' := monoListLbOwn_le (histAt ks ops v1.ops)
    (runM_hs_prefix ks ops v1.ops ops.length (by omega)) $$ Hlb
  iexists qw1, nw1, k1
  iframe Hc Hrd Hlb'
  isplitr
  · ipureintro; exact Hlok
  iintro Hc Hrd
  iunfold writerOwn
  dsimp only
  iframe Hms Hreg0 Hreg1 Hlog Hctrs HhW Hrd Hfiles Hss0 Hss1 Hadd
  isplitr
  · ipureintro; exact HopsA
  isplitr
  · ipureintro; exact HnbA
  isplitl [Hm0]
  · iexists qw0, nw0, k0; iframe; ipureintro; exact Hl0
  · iexists qw1, nw1, k1; iunfold memW; iframe; ipureintro; exact Hl1

end lemmas

end mvccfull
end EtcdGrove
end Perennial
