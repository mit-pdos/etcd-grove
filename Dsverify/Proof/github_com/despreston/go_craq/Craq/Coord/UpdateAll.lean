/-
`cdr.updateAll(skip)` (lock held) with `skip` the last replica: each other replica gets its
metadata in a goroutine of its own (`updateNode`), which takes its `connected` field and role half
and a fraction of the replicas' slice; the WaitGroup gives them back.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.UpdateNode

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- The replicas field and slice, at fraction `q`. -/
def repsFrag (c : Loc) (sl : GoSlice) (locs : List Loc) (q : Qp) : IProp GF :=
  iprop(structFieldRef coordinator.Coordinator go!"replicas" c ↦{DFrac.own q} sl ∗
    sl ↦*{DFrac.own q} locs)

theorem repsFrag_half (c : Loc) (sl : GoSlice) (locs : List Loc) (q : Qp) :
    repsFrag (GF := GF) c sl locs q ⊣⊢ repsFrag c sl locs q.half ∗ repsFrag c sl locs q.half := by
  unfold repsFrag
  have h1 := typedPointsto_half_split (GF := GF)
    (structFieldRef coordinator.Coordinator go!"replicas" c) sl q
  have h2 := (ownSlice_dfractional (GF := GF) sl locs).dfractional (DFrac.own q.half)
    (DFrac.own q.half)
  rw [DFrac.op_own, Qp.half_add_half] at h2
  constructor
  · iintro ⟨H1, H2⟩
    icases h1.1 $$ H1 with ⟨H1a, H1b⟩
    icases h2.1 $$ H2 with ⟨H2a, H2b⟩
    iframe
  · iintro ⟨⟨H1a, H2a⟩, ⟨H1b, H2b⟩⟩
    isplitl [H1a H1b]
    · iapply h1.2; iframe
    · iapply h2.2; iframe

/-- What a goroutine of `updateAll` takes of a replica that is not the last: its `connected`
field and, while connected, its role half (not the tail). -/
def updIn (cfg : Cfg GF) (r : Rep) : IProp GF :=
  iprop(structFieldRef coordinator.node go!"connected" r.loc ↦ r.conn ∗
    if r.conn then iprop(∃ x : GoString, roleHalf cfg.γ r.addr (false, x)) else iprop(True))

/-- What it gives back: the role it told, while still connected. -/
def updOut (cfg : Cfg GF) (rs : List Rep) (j : Nat) (r : Rep) : IProp GF :=
  iprop(∃ c' : Bool, structFieldRef coordinator.node go!"connected" r.loc ↦ c' ∗
    if c' then roleHalf cfg.γ r.addr (false, addrAt rs (j + 1)) else iprop(True))

/-- Replica `j`'s part (none for the last). -/
def inF (cfg : Cfg GF) (rs : List Rep) (j : Nat) (r : Rep) : IProp GF :=
  if j + 1 = rs.length then iprop(True) else updIn cfg r

def outF (cfg : Cfg GF) (rs : List Rep) (j : Nat) (r : Rep) : IProp GF :=
  if j + 1 = rs.length then iprop(True) else updOut cfg rs j r

theorem bigSepL_drop_split (Φ : Nat → Rep → IProp GF) (rs : List Rep) (n : Nat) (r : Rep)
    (h : rs[n]? = some r) :
    ([∗list] j ↦ x ∈ rs.drop n, Φ (n + j) x) ⊣⊢
      Φ n r ∗ [∗list] j ↦ x ∈ rs.drop (n + 1), Φ (n + 1 + j) x := by
  obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hn]
  refine BigSepL.bigSepL_cons.trans ?_
  have e : ∀ j, n + (j + 1) = n + 1 + j := fun j => by omega
  refine ⟨sep_mono .rfl (BigSepL.bigSepL_mono_of_forall fun {j x} => ?_),
    sep_mono .rfl (BigSepL.bigSepL_mono_of_forall fun {j x} => ?_)⟩
  · rw [e j]
  · rw [e j]

theorem bigSepL_take_snoc (Φ : Nat → Rep → IProp GF) (rs : List Rep) (n : Nat) (r : Rep)
    (h : rs[n]? = some r) :
    ([∗list] j ↦ x ∈ rs.take (n + 1), Φ j x) ⊣⊢
      ([∗list] j ↦ x ∈ rs.take n, Φ j x) ∗ Φ n r := by
  obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.take_succ_eq_append_getElem hn]
  refine BigSepL.bigSepL_snoc.trans ?_
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]
  exact .rfl

theorem wp_updateAll (cfg : Cfg GF) (c : Loc) (sl : GoSlice) (rs : List Rep) (skip : w64)
    (hskip : 0 ≤ sint.Z skip ∧ sint.nat skip + 1 = rs.length)
    (hbound : rs.length < 2 ^ 31 - 1) (hch : ∀ r ∈ rs, r.addr ∈ cfg.chain) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
        structFieldRef coordinator.Coordinator go!"replicas" c ↦ sl ∗
        sl ↦* rs.map Rep.loc ∗ ([∗list] r ∈ rs, nodeFacts cfg r.loc r.addr) ∗
        [∗list] j ↦ r ∈ rs, inF cfg rs j r }}
      (App (Val (c @!! go.GoType.PointerType coordinator.Coordinator.ty @!! go!"updateAll"))
        (Val #skip))
    {{ RET #();
        structFieldRef coordinator.Coordinator go!"replicas" c ↦ sl ∗
        sl ↦* rs.map Rep.loc ∗ [∗list] j ↦ r ∈ rs, outF cfg rs j r }} := by
  wp_start as ⟨Hrep, Hsl, #Hnfs, Hin⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  simp only [List.length_map] at Hlen
  wp_auto
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, H⟩
  imod sync.join.init wg_ptr γwg $$ H with Hwg
  ipersist cdr
  ipersist skip
  ihave HI : (∃ (k : w64) (q : Qp) (na : w32) (P : IProp GF),
      "i" ∷ i_ptr ↦ k ∗
      "Hfr" ∷ repsFrag c sl (rs.map Rep.loc) q ∗
      "Hwg" ∷ sync.join.ownAdder wg_ptr na P ∗
      "Hback" ∷ (P -∗ repsFrag c sl (rs.map Rep.loc) q -∗ repsFrag c sl (rs.map Rep.loc) 1 ∗
        [∗list] j ↦ r ∈ rs.take (sint.nat k), outF cfg rs j r) ∗
      "Hin" ∷ ([∗list] j ↦ r ∈ rs.drop (sint.nat k), inF cfg rs (sint.nat k + j) r) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ rs.length ∧ 0 ≤ sint.Z na ∧ sint.Z na ≤ sint.Z k⌝ : IProp GF)
    $$ [i Hrep Hsl Hwg Hin]
  · iexists W64 0, 1, W32 0, iprop(True)
    iframe i Hwg
    isplitl [Hrep Hsl]
    · unfold repsFrag named; iframe Hrep Hsl
    isplitr
    · iintro - Hfr
      iframe Hfr
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iapply BigSepL.bigSepL_nil.2; iempintro
    isplitl [Hin]
    · simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, Nat.zero_add]
      iexact Hin
    ipureintro
    refine ⟨by decide, by simp, by decide, by decide⟩
  wp_for HI
  unfold repsFrag
  icases Hfr with ⟨Hrep, Hsl⟩
  wp_auto
  wp_if_destruct
  · -- an iteration, `k < len`
    have hlt : sint.Z k < sint.Z sl.len := by simpa [intoVal_eq_iff] using Hif
    have hkl : sint.nat k < rs.length := by word
    list_elem rs (sint.nat k) as rk
    ihave Hin := (bigSepL_drop_split (inF cfg rs) rs (sint.nat k) rk Hrk_lookup).1 $$ Hin
    icases Hin with ⟨Hk, Hin⟩
    wp_if_destruct
    · -- `k = skip`: the last replica, skipped
      subst Hif
      have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      wp_for_post
      iframe HΦ
      iexists k + W64 1, q, na, P
      unfold named
      iframe i Hwg Hrep Hsl
      isplitl [Hback]
      · iintro HP Hfr
        ihave ⟨Hfull, Hout⟩ := Hback $$ HP Hfr
        iframe Hfull
        rw [hk1]
        iapply (bigSepL_take_snoc (outF cfg rs) rs _ rk Hrk_lookup).2
        iframe Hout
        unfold outF
        rw [if_pos hskip.2]
        itrivial
      isplitl [Hin]
      · rw [hk1]; iexact Hin
      ipureintro
      refine ⟨by word, by omega, Hk.2.2.1, by word⟩
    · -- `k ≠ skip`: a goroutine for replica `k`
      have hnl : sint.nat k + 1 ≠ rs.length := by
        intro h; apply Hif; word
      have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      unfold inF
      rw [if_neg hnl]
      ihave Hfr : repsFrag c sl (rs.map Rep.loc) q $$ [Hrep Hsl]
      · unfold repsFrag; iframe
      icases (repsFrag_half c sl (rs.map Rep.loc) q).1 $$ Hfr with ⟨HfrA, HfrB⟩
      wp_apply sync.join.WaitGroup.wp_Add
        (iprop(repsFrag c sl (rs.map Rep.loc) q.half ∗ updOut cfg rs (sint.nat k) rk)) wg_ptr P na
        $$ [Hwg] as ⟨Hwg, Hdone⟩
      · iframe; ipureintro; word
      wp_apply wp_fork $$ [HfrA Hk Hdone]
      · -- the goroutine
        wp_auto
        unfold repsFrag
        icases HfrA with ⟨HrepA, HslA⟩
        unfold updIn
        icases Hk with ⟨Hconn, Hrole⟩
        have hmt : (metaOf rs (sint.nat k)).isTail = false := by
          simp only [metaOf, decide_eq_false_iff_not]; omega
        have hmn : (metaOf rs (sint.nat k)).next = addrAt rs (sint.nat k + 1) := by
          simp only [metaOf]; rw [if_pos ⟨by omega, hnl⟩]
        cases hc : rk.conn
        · wp_apply wp_updateNode cfg c sl rs (DFrac.own q.half) k rk false (false, go!"") Hk.1
            Hrk_lookup hch $$ [HrepA HslA Hconn] as %err ⟨HrepA, HslA, %b', Hconn, Hpost⟩
          · iframe; iframe Hnfs; unfold sendPre; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
          unfold sendPost
          icases Hpost with (⟨%Hc, -⟩ | ⟨%Hb, -⟩)
          · exact absurd Hc.2.1 (by simp)
          subst Hb
          wp_apply sync.join.WaitGroup.wp_Done _ wg_ptr $$ [Hdone HrepA HslA Hconn]
          · iframe Hdone; iframe; unfold updOut; iexists false; iframe
            simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
          itrivial
        · simp only [↓reduceIte]
          icases Hrole with ⟨%x, Hrole⟩
          wp_apply wp_updateNode cfg c sl rs (DFrac.own q.half) k rk true (false, x) Hk.1
            Hrk_lookup hch $$ [HrepA HslA Hconn Hrole] as %err ⟨HrepA, HslA, %b', Hconn, Hpost⟩
          · iframe; iframe Hnfs; unfold sendPre; simp only [↓reduceIte]; iframe
            unfold updDep; rw [hmt]; simp only [Bool.false_eq_true, false_and, ↓reduceIte]; itrivial
          unfold sendPost
          icases Hpost with (⟨%Hc, Hpost⟩ | ⟨%Hb, -⟩)
          · obtain ⟨-, -, rfl⟩ := Hc
            unfold updPost
            icases Hpost with ⟨Hrole, -⟩
            wp_apply sync.join.WaitGroup.wp_Done _ wg_ptr $$ [Hdone HrepA HslA Hconn Hrole]
            · iframe Hdone; iframe; unfold updOut; iexists true; iframe Hconn
              simp only [↓reduceIte]; rw [hmt, hmn]; iframe
            itrivial
          · subst Hb
            wp_apply sync.join.WaitGroup.wp_Done _ wg_ptr $$ [Hdone HrepA HslA Hconn]
            · iframe Hdone; iframe; unfold updOut; iexists false; iframe
              simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
            itrivial
      wp_for_post
      iframe HΦ
      iexists k + W64 1, q.half, na + W32 1, iprop(P ∗ (repsFrag c sl (rs.map Rep.loc) q.half ∗
        updOut cfg rs (sint.nat k) rk))
      unfold repsFrag
      icases HfrB with ⟨HrepB, HslB⟩
      unfold named
      iframe i Hwg HrepB HslB
      isplitl [Hback]
      · iintro ⟨HP, ⟨HrA, HsA⟩, Hout⟩ ⟨HrB, HsB⟩
        ihave Hfr := (repsFrag_half c sl (rs.map Rep.loc) q).2 $$ [HrA HsA HrB HsB]
        · unfold repsFrag; iframe
        unfold repsFrag
        icases Hfr with ⟨Hr, Hs⟩
        ihave ⟨Hfull, Houts⟩ := Hback $$ HP [Hr Hs]
        · iframe
        iframe Hfull
        rw [hk1]
        iapply (bigSepL_take_snoc (outF cfg rs) rs _ rk Hrk_lookup).2
        iframe Houts
        unfold outF
        rw [if_neg hnl]
        iexact Hout
      isplitl [Hin]
      · rw [hk1]; iexact Hin
      ipureintro
      refine ⟨by word, by omega, by word, by word⟩
  · -- the loop's end, `k = len`
    have hge : ¬ sint.Z k < sint.Z sl.len := by simpa [intoVal_eq_iff] using Hif
    have hkeq : sint.nat k = rs.length := by word
    rw [decide_eq_false hge]
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto_lc 1
    wp_apply sync.join.WaitGroup.wp_Wait P na wg_ptr $$ [Hwg] as ⟨HP, -⟩
    · iexact Hwg
    ihave ⟨⟨Hrep, Hsl⟩, Hout⟩ := Hback $$ HP [Hrep Hsl]
    · iframe
    rw [hkeq, List.take_length]
    iapply HΦ
    iframe

end proof

end github_com.despreston.go_craq

end Perennial
