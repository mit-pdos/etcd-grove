/-
The registrar's `watch` (`stream.watch`): the registration's update and its pure part. Lean-first
(no Rocq counterpart).

- `regOk'_register`: registering a fresh id with its entry keeps `regOk'` (the id is in no cancel:
  `regOk'`'s third conjunct).
- `recvEvs_fresh'`: a watcher not yet registered has received nothing (`rcvKnown'`).
- `register_au'`: `Watch`'s update at the incarnation's and the stream's invariants, for a range
  not empty: the stream open (the registrar's half of the closed flag), the new watcher in the
  registry (both halves, its fragment kept in `regLock`), what the update learns of the store's
  state (its revision's lower bound, at least the floor loaded before).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.EpochLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.RecvLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- **Registering a fresh id** with its entry (unmarked) keeps the registry the stream's. -/
theorem regOk'_register (S : StreamState) (W : GMap w64 Reg) (C : List w64) (h : regOk' S W C)
    (id : w64) (hid : S.ws !! id = none) (x : Reg) (wi : WInfo)
    (hrg : wi.rg = ⟨x.key, if x.endNil then none else some x.e, x.start, id⟩)
    (hfs : wi.fs = filterFs x.filter) (hlo : wi.lo = x.lo) (hk : wi.k = x.k)
    (hlive : wi.live = true) :
    W !! id = none ∧ regOk' (S.register id wi) (<[id := x]> W) C := by
  have hW : W !! id = none := by
    cases hw : W !! id with
    | none => rfl
    | some y =>
      obtain ⟨wi', hwi', -⟩ := h.2.1 id y hw
      rw [hid] at hwi'; cases hwi'
  refine ⟨hW, ?_, ?_, ?_⟩
  · intro id' wi' hwi'
    unfold StreamState.register at hwi'
    by_cases he : id' = id
    · subst he; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hwi' ⊢
      exact h.1 id' wi' hwi'
  · intro id' y hy
    unfold StreamState.register
    by_cases he : id' = id
    · subst he
      rw [GMap.lookup_insert] at hy
      cases hy
      refine ⟨wi, by rw [GMap.lookup_insert], hrg, hfs, hlo, hk, fun _ => hlive, fun hC => ?_⟩
      have := h.2.2 id' hC
      rw [hW] at this; cases this
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hy ⊢
      exact h.2.1 id' y hy
  · intro id' hC
    by_cases he : id' = id
    · subst he; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)]; exact h.2.2 id' hC

/-- **A watcher not yet registered has received nothing**: every response but the stream's was for
a registered watcher. -/
theorem recvEvs_fresh' {rs : List WResp} {W : GMap w64 Reg} (h : rcvKnown' rs W) {id : w64}
    (hid : W !! id = none) (hne : id ≠ W64 (-1)) : recvEvs rs id = [] := by
  unfold recvEvs
  rw [List.flatten_eq_nil_iff]
  intro l hl
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hl
  obtain ⟨hr, hri⟩ := List.mem_filter.1 hr
  simp only [decide_eq_true_eq] at hri
  have := h r hr (by rw [hri]; exact hne)
  rw [hri, hid] at this
  cases this

/-- `rcvKnown'` at a larger registry. -/
theorem rcvKnown'_insert {rs : List WResp} {W : GMap w64 Reg} (h : rcvKnown' rs W) (id : w64)
    (x : Reg) : rcvKnown' rs (<[id := x]> W) := by
  intro r hr hne
  by_cases he : r.id = id
  · rw [he, GMap.lookup_insert]; rfl
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)]; exact h r hr hne

theorem register_closed' (S : StreamState) (id : w64) (w : WInfo) :
    (S.register id w).closed = S.closed := rfl

end model

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The registration's entry for the fresh id: the watcher's struct, its range and filter, its
start, its first revision `lo` and the sent count `k`, not marked. -/
def regOf (wp : Loc) (kk e : GoString) (endk : GoSlice) (st filt : w64) (lo k : Nat) : Reg :=
  ⟨wp, kk, e, decide (endk = slice.nil), st, filt, lo, k, false⟩

/-- **What `watch`'s update gives back** at a registration: the live share, the registrar's half
of the closed flag, the stream open, the id fresh (in the lock's registry too) and not `-1`, the
lock's half of the registry with the new entry, its sent count's lower bound, and the store's
revision's lower bound at the state registered at (at least the floor `n`), with its log's
bounds. -/
def regQ' (T : Strm) (q : Qp) (W : GMap w64 Reg) (wp : Loc) (kk e : GoString) (endk : GoSlice)
    (st filt : w64) (n : Nat) (σ : MvccState) (S : StreamState) (id : w64) : IProp GF :=
  iprop(ghostVar T.ep.ι.ret q () ∗ ghostVar T.σs.cl (1 : Qp).half false ∗
    ⌜S.closed = false ∧ W !! id = none ∧ id ≠ W64 (-1) ∧ n ≤ σ.rev ∧ 2 ≤ σ.log.length ∧
      σ.log.length + 3 ≤ 2 ^ 63⌝ ∗
    monoNatLbOwn T.ep.m.rev σ.rev ∗
    ∃ k : Nat, wsSentLb T.σs.ws k ∗
      regLock T.σs (<[id := regOf wp kk e endk st filt (watchLo σ st) k]> W))

/-- **`watch`'s update** (see the file header). -/
theorem register_au' (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (T : Strm) (q : Qp) (W : GMap w64 Reg) (wp : Loc) (kk e : GoString) (endk : GoSlice)
    (st filt : w64) (n : Nat) (hkk : kk ≠ []) :
    isInc (GF := GF) T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv ∗
        inv streamN (streamInv T.σs) ∗ ghostVar T.ep.ι.ret q () ∗
        ghostVar T.σs.cl (1 : Qp).half false ∗ regLock T.σs W ∗ monoNatLbOwn T.ep.m.rev n ⊢
      AU <{ ∃∃ (σ : MvccState) (S : StreamState), mvccState T.ep.ι.kv σ ∗ wsState T.σs.ws S }>
        @ ⊤ \ ↑mvccN, ∅
      <{ ∀∀ (id : w64) (k : Nat), mvccState T.ep.ι.kv σ ∗
          (if S.closed then ⌜id = W64 (-1)⌝ ∗ wsState T.σs.ws S
           else ⌜S.ws !! id = none ∧ id ≠ W64 (-1) ∧ σ.pending = none⌝ ∗ wsSentLb T.σs.ws k ∗
             wsState T.σs.ws (S.register id
               ⟨watchRangeOf kk e endk st id, filterFs filt, watchLo σ st, k, true⟩)),
        COMM regQ' T q W wp kk e endk st filt n σ S id }> := by
  haveI := streamInv_timeless hpers T.σs
  haveI := hpers.2.2.2.2.2.1
  haveI := hpers.2.2.2.2.2.2.1
  haveI : ∀ ι n, Persistent (wsSentLb (GF := GF) ι n) := hpers.2.2.1
  haveI : Timeless (memberInv (GF := GF) T.ep.ks T.ep.γh T.ep.mp T.ep.m T.ep.ι) := by
    unfold memberInv memberState; infer_instance
  haveI : Persistent (isInc (GF := GF) T.ep.ks T.ep.γh T.ep.i T.ep.mp T.ep.m T.ep.ι T.ep.kv) := by
    haveI := hpers.1; unfold isInc; infer_instance
  haveI : ∀ kv γ, Persistent (isMvcc (GF := GF) kv γ) := hpers.1
  have Hmm := memberN_mask T.ep.i
  have Hms := streamN_memberN T.ep.i (⊤ \ ↑mvccN) streamN_mvccN
  iintro ⟨#Hinc, #Hinv, Hret, Hcl, Hreg, #Hn⟩
  iauintro
  unfold atomic_acc
  ihave #Hinc' := Hinc
  iunfold isInc at Hinc'
  icases Hinc' with ⟨#Hmi, #Hkv⟩
  iinv Hmi with >Hm Hclm
  icases memberInv_live T.ep.ks T.ep.γh T.ep.mp T.ep.m T.ep.ι q $$ [$Hret $Hm] with ⟨Hret, Hm⟩
  iunfold memberState at Hm
  icases Hm with ⟨%σ, %b, %Hl, Hσ, Hgσ, Ha1, Ha2, Ha3, Ha4, Hbnd, Hmr, Hmc, Hmn, #Hlb, %Hok⟩
  iinv Hinv with >Hi Hclose
  iunfold streamInv at Hi
  icases Hi with ⟨%S, %W', %C, HS, HScl, Hreg', Hcn, Hor⟩
  ihave %Hc := ghostVar_agree T.σs.cl _ _ _ _ $$ HScl Hcl
  iunfold regLock at Hreg
  icases Hreg with ⟨Hreg, Hfr⟩
  ihave %HW := ghostMapAuth_agree T.σs.reg _ _ _ _ $$ Hreg' Hreg
  subst HW
  ihave %Hnle := monoNatLbOwn_valid T.ep.m.rev 1 σ.rev n $$ Hmr Hn
  icases monoNat_auth_lb _ _ _ $$ Hmr with ⟨#Lrev, Hmr⟩
  icases (persistent_entails_right (hreach T.ep.kv T.ep.ι.kv σ)) $$ [$Hkv $Hσ] with ⟨%Hr, -, Hσ⟩
  have hlog := (reach_bounds σ Hr.1).1
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑mvccN) \ ↑(memberN T.ep.i)) \ ↑streamN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ, S
  iframe Hσ HS
  isplit
  · iintro ⟨Hσ, HS⟩
    imod Hclose2 with -
    imod Hclose $$ [HS HScl Hreg' Hcn Hor] with -
    · inext; iunfold streamInv; iexists S, W', C; iframe
    imod Hclm $$ [Hσ Hgσ Ha1 Ha2 Ha3 Ha4 Hbnd Hmr Hmc Hmn] with -
    · inext; iunfold memberInv; ileft; iunfold memberState
      iexists σ, b, Hl; iframe; iframe #; ipureintro; exact Hok
    imodintro
    iframe
    iunfold regLock
    iframe
  · iintro %id %k ⟨Hσ, HS⟩
    rw [Hc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases HS with ⟨%Hfresh, #Hk, HS⟩
    icases Hor with (%HregOk | ⟨%Hcl1, -⟩)
    rotate_left
    · exfalso; simp_all
    obtain ⟨hW, hreg'⟩ := regOk'_register S W' C HregOk id Hfresh.1
      (regOf wp kk e endk st filt (watchLo σ st) k)
      ⟨watchRangeOf kk e endk st id, filterFs filt, watchLo σ st, k, true⟩
      (rg_eq kk e endk _ st id rfl).symm rfl rfl rfl rfl
    ihave Hfull := (ghostMapAuth_halves T.σs.reg W').2 $$ [$Hreg' $Hreg]
    imod ghost_map_insert id (regOf wp kk e endk st filt (watchLo σ st) k) hW $$ Hfull
      with ⟨Hfull, Hfrag⟩
    icases (ghostMapAuth_halves T.σs.reg _).1 $$ Hfull with ⟨Hreg', Hreg⟩
    imod Hclose2 with -
    imod Hclose $$ [HS HScl Hreg' Hcn] with -
    · inext; iunfold streamInv
      iexists S.register id ⟨watchRangeOf kk e endk st id, filterFs filt, watchLo σ st, k, true⟩,
        <[id := regOf wp kk e endk st filt (watchLo σ st) k]> W', C
      rw [register_closed', Hc]
      iframe
      ileft; ipureintro; exact hreg'
    imod Hclm $$ [Hσ Hgσ Ha1 Ha2 Ha3 Ha4 Hbnd Hmr Hmc Hmn] with -
    · inext; iunfold memberInv; ileft; iunfold memberState
      iexists σ, b, Hl; iframe; iframe #; ipureintro; exact Hok
    imodintro
    iunfold regQ'
    iframe
    iframe #
    isplitr
    · ipureintro; exact ⟨Hc, hW, Hfresh.2.1, Hnle.2, hlog, Hr.2⟩
    iunfold regLock
    iframe
    iapply BigSepM.bigSepM_insert hW
    iframe
    simp only [regOf, Bool.false_eq_true, ↓reduceIte]
    iexact Hfrag

end ghost

end mvccfull
end EtcdGrove
end Perennial
