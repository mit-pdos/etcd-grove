/-
`node.spill`'s sort, its pure side (U9k, `notes/bbolt-proof-plan.md`): **`n`'s children
permuted** (`X.setNode bl n { rn with cs := l }`, `l` a permutation of `rn.cs`, what
`sort.Sort(n.children)` leaves). Everything the spill states of the records is membership-based
in a node's children, so a permutation keeps it: the spill's global state (`spG_perm`), the frame
(`spFrame_perm`: only `n` touched), the step (`spStep_perm`), `n`'s branch facts (`uBr_perm`), its
context (`spCtx_perm`), the loop's invariant at its start (`spLoop_start`), and back: a spill
done from the permuted state is one from the start (`spDone_unperm`). A node without children is
unchanged (`setNode_perm_nil`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillLoop
public import Proof.go_etcd_io.bbolt.Rebalance.Objs
public import Proof.go_etcd_io.bbolt.Rebalance.RblKeys

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section perm
variable [GooseExts]

/-- A node's record with its children replaced by a permutation of them. -/
def nodeP (r r' : NRec) : Prop := { r' with cs := r.cs } = r ∧ r.cs.Perm r'.cs

/-- A bucket's record with its nodes' children permuted. -/
def bktP (B B' : BRec) : Prop := { B' with ns := B.ns } = B ∧ ∀ l, optRel nodeP (B.ns !! l) (B'.ns !! l)

theorem nodeP_refl (r : NRec) : nodeP r r := ⟨rfl, List.Perm.refl _⟩

theorem nodeP_nv {r r' : NRec} (h : nodeP r r') :
    r'.nv = r.nv ∧ r'.ins = r.ins ∧ r'.ws = r.ws ∧ r'.key = r.key ∧ r'.ksrc = r.ksrc ∧
      r'.capOwn = r.capOwn := by
  obtain ⟨e, -⟩ := h
  rw [← e]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nodeP_mem {r r' : NRec} (h : nodeP r r') {c : Loc} : c ∈ r.cs ↔ c ∈ r'.cs :=
  h.2.mem_iff

theorem bktP_fields {B B' : BRec} (h : bktP B B') :
    B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.nm = B.nm ∧ B'.bm = B.bm ∧ B'.ipg = B.ipg ∧ B'.isrc = B.isrc ∧
      B'.pst = B.pst := by
  have e := h.1
  rw [← e]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem optRel_isSome' {α β : Type} {R : α → β → Prop} {o : Option α} {o' : Option β}
    (h : optRel R o o') : o.isSome = o'.isSome := by
  cases o <;> cases o' <;> simp_all [optRel]

theorem descIn_perm {B B' : BRec} (h : bktP B B') {a d : Loc} (hd : descIn B a d) :
    descIn B' a d := by
  induction hd with
  | self a => exact .self a
  | child a c d r hr hc _ ih =>
    obtain ⟨r', hr', hs⟩ := optRel_some_l (hr ▸ h.2 a)
    exact .child a c d r' hr' ((nodeP_mem hs).1 hc) ih

theorem nodeRootIn_perm {B B' : BRec} (h : bktP B B') {a rt : Loc} (hd : nodeRootIn B a rt) :
    nodeRootIn B' a rt := by
  induction hd with
  | top a r hr hp =>
    obtain ⟨r', hr', hs⟩ := optRel_some_l (hr ▸ h.2 a)
    exact .top a r' hr' (by rw [(nodeP_nv hs).1]; exact hp)
  | up a rt r hr hp _ ih =>
    obtain ⟨r', hr', hs⟩ := optRel_some_l (hr ▸ h.2 a)
    have e : r'.nv.parent' = r.nv.parent' := by rw [(nodeP_nv hs).1]
    exact .up a rt r' hr' (by rw [e]; exact hp) (by rw [e]; exact ih)

/-! ## The permuted state -/

variable {X : WX} {bl n : Loc} {B : BRec} {rn : NRec} {l : List Loc}

/-- The permuted state, unfolded. -/
theorem setNode_perm_eq (hB : X.t.bs !! bl = some B) (r' : NRec) :
    X.setNode bl n r' =
      { X with t := { X.t with bs := X.t.bs.insert bl { B with ns := B.ns.insert n r' } } } := by
  unfold WX.setNode WX.setBkt
  rw [hB]

theorem bs_perm (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn) (hp : rn.cs.Perm l)
    (bl' : Loc) :
    optRel bktP (X.t.bs !! bl') ((X.t.bs.insert bl { B with ns := B.ns.insert n { rn with cs := l } }) !! bl') := by
  by_cases he : bl = bl'
  · subst he
    rw [GMap.lookup_insert, hB]
    refine ⟨rfl, fun l' => ?_⟩
    by_cases hl : n = l'
    · subst hl; rw [GMap.lookup_insert, hr]; exact ⟨rfl, hp⟩
    · rw [GMap.lookup_insert_ne _ _ hl]; exact optRel_refl nodeP_refl _
  · rw [GMap.lookup_insert_ne _ _ he]
    exact optRel_refl (fun B => ⟨rfl, fun _ => optRel_refl nodeP_refl _⟩) _

theorem node_perm_self (hB : X.t.bs !! bl = some B) :
    (X.setNode bl n { rn with cs := l }).node bl n = some { rn with cs := l } := by
  rw [setNode_perm_eq hB]
  unfold WX.node
  simp only [GMap.lookup_insert, Option.bind_some]

theorem node_perm_ne (hB : X.t.bs !! bl = some B) {bl' l' : Loc} (hne : l' ≠ n) (r' : NRec) :
    (X.setNode bl n r').node bl' l' = X.node bl' l' := by
  rw [setNode_perm_eq hB]
  unfold WX.node
  by_cases he : bl = bl'
  · subst he
    simp only [GMap.lookup_insert, hB, Option.bind_some]
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]
  · simp only
    rw [GMap.lookup_insert_ne _ _ he]

/-- A node without children: the permuted state is the state. -/
theorem setNode_perm_nil (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (h0 : rn.cs = []) (hp : rn.cs.Perm l) : X.setNode bl n { rn with cs := l } = X := by
  rw [h0] at hp
  have hl : l = [] := List.Perm.eq_nil hp.symm
  have e : ({ rn with cs := l } : NRec) = rn := by rw [hl, ← h0]
  rw [e]
  unfold WX.setNode WX.setBkt
  rw [hB]
  simp only
  rw [GMap.insert_id _ _ _ hr]
  rw [show ({ B with ns := B.ns } : BRec) = B from rfl, GMap.insert_id _ _ _ hB]

theorem objs_perm (hd : objsDisj X.t) (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (r' : NRec) : (X.setNode bl n r').t.objs = X.t.objs.insert n (.node bl r') := by
  rw [setNode_perm_eq hB]
  exact objs_setNodeT X.t bl n B rn r' hd hB hr

theorem objs_perm_none (hd : objsDisj X.t) (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (r' : NRec) {y : Loc} (hy : (X.setNode bl n r').t.objs !! y = none) : X.t.objs !! y = none := by
  rw [objs_perm hd hB hr] at hy
  by_cases e : n = y
  · subst e; rw [GMap.lookup_insert] at hy; cases hy
  · rw [GMap.lookup_insert_ne _ _ e] at hy; exact hy

/-! ## The spill's global state -/

theorem derefPre_perm (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn) (hp : rn.cs.Perm l)
    (h : derefPre X) : derefPre (X.setNode bl n { rn with cs := l }) := by
  rw [setNode_perm_eq hB]
  have hbs := bs_perm hB hr hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, h5⟩
  · intro bl0 B0 l0 r0 hB0 hr0 hl
    obtain ⟨B1, hB1, hs⟩ := optRel_some_r (hB0 ▸ hbs bl0)
    obtain ⟨r1, hr1, hrs⟩ := optRel_some_r (hr0 ▸ hs.2 l0)
    obtain ⟨a1, a2, a3, a4⟩ := h1 bl0 B1 l0 r1 hB1 hr1 hl
    obtain ⟨hnv, -, hws, hkey, -, -⟩ := nodeP_nv hrs
    refine ⟨by rw [hnv]; exact a1, by rw [hws]; exact a2, by rw [hnv, hkey]; exact a3, ?_⟩
    intro c hc
    obtain ⟨hcl, hcs⟩ := a4 c ((nodeP_mem hrs).2 hc)
    exact ⟨hcl, by rw [← optRel_isSome' (hs.2 c)]; exact hcs⟩
  · intro bl0 B0 hB0 hbl
    obtain ⟨B1, hB1, hs⟩ := optRel_some_r (hB0 ▸ hbs bl0)
    obtain ⟨a1, a2⟩ := h2 bl0 B1 hB1 hbl
    have hf := bktP_fields hs
    refine ⟨fun k c hk => ?_, fun hrn => ?_⟩
    · obtain ⟨b1, b2⟩ := a1 k c (by rw [← hf.2.2.2.1]; exact hk)
      exact ⟨b1, by rw [← optRel_isSome' (hbs c)]; exact b2⟩
    · obtain ⟨rt, hrt, hrtl⟩ := a2 (by rw [← hf.1]; exact hrn)
      exact ⟨rt, by rw [hf.1]; exact nodeRootIn_perm hs hrt, hrtl⟩
  · intro bl0 B0 hB0
    obtain ⟨B1, hB1, hs⟩ := optRel_some_r (hB0 ▸ hbs bl0)
    obtain ⟨a1, a2⟩ := h3 bl0 B1 hB1
    refine ⟨a1, ?_⟩
    have := optRel_isSome' (hs.2 null)
    rw [a2] at this
    cases e : B0.ns !! null with
    | none => rfl
    | some _ => rw [e] at this; cases this
  · show ((X.t.bs.insert bl _) !! X.rl).isSome
    rw [← optRel_isSome' (hbs X.rl)]; exact h4

theorem liveFresh_perm (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (hp : rn.cs.Perm l) (h : liveFresh X) : liveFresh (X.setNode bl n { rn with cs := l }) := by
  rw [setNode_perm_eq hB]
  have hbs := bs_perm hB hr hp
  intro bl0 B0 l0 r0 hB0 hr0 hl
  obtain ⟨B1, hB1, hs⟩ := optRel_some_r (hB0 ▸ hbs bl0)
  obtain ⟨r1, hr1, hrs⟩ := optRel_some_r (hr0 ▸ hs.2 l0)
  obtain ⟨hnv, -, hws, -, hks, -⟩ := nodeP_nv hrs
  rw [hws, hnv, hks]
  exact h bl0 B1 l0 r1 hB1 hr1 hl

theorem bktReach_perm (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (hp : rn.cs.Perm l) {d : Loc} (h : bktReach X d) :
    bktReach (X.setNode bl n { rn with cs := l }) d := by
  rw [setNode_perm_eq hB]
  have hbs := bs_perm hB hr hp
  induction h with
  | root => exact .root
  | child bl0 c B0 k hB0 hk _ ih =>
    obtain ⟨B1, hB1, hs⟩ := optRel_some_l (hB0 ▸ hbs bl0)
    exact .child bl0 c B1 k hB1 (by rw [(bktP_fields hs).2.2.2.1]; exact hk) ih

theorem liveReach_perm (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (hp : rn.cs.Perm l) (h : liveReach X) : liveReach (X.setNode bl n { rn with cs := l }) := by
  have hbr := fun d (hd : bktReach X d) => bktReach_perm (n := n) hB hr hp hd
  rw [setNode_perm_eq hB] at hbr ⊢
  have hbs := bs_perm hB hr hp
  refine ⟨fun bl0 B0 hB0 hbl => ?_, fun bl0 B0 l0 r0 hB0 hr0 hl => ?_⟩
  · obtain ⟨B1, hB1, -⟩ := optRel_some_r (hB0 ▸ hbs bl0)
    exact hbr bl0 (h.1 bl0 B1 hB1 hbl)
  · obtain ⟨B1, hB1, hs⟩ := optRel_some_r (hB0 ▸ hbs bl0)
    obtain ⟨r1, hr1, -⟩ := optRel_some_r (hr0 ▸ hs.2 l0)
    obtain ⟨rt, hrt, hd⟩ := h.2 bl0 B1 l0 r1 hB1 hr1 hl
    exact ⟨rt, by rw [(bktP_fields hs).1]; exact nodeRootIn_perm hs hrt, descIn_perm hs hd⟩

/-- **The spill's global state is kept** by a permutation of `n`'s children. -/
theorem spG_perm (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn) (hp : rn.cs.Perm l)
    {txid : w64} {ml : Nat} {fl : FLPg} (h : spG X txid ml fl) :
    spG (X.setNode bl n { rn with cs := l }) txid ml fl := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  refine ⟨?_, ?_, derefPre_perm hB hr hp a3, liveFresh_perm hB hr hp a4,
    liveReach_perm hB hr hp a5, ?_, ?_, ?_⟩ <;> rw [setNode_perm_eq hB] <;> assumption

theorem spP_perm (hB : X.t.bs !! bl = some B) (r' : NRec) : spP (X.setNode bl n r') = spP X := by
  rw [setNode_perm_eq hB]; rfl

/-! ## The frame and the step -/

/-- **The frame of the permutation**: only `n` touched. -/
theorem spFrame_perm (hd : objsDisj X.t) (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn) :
    spFrame X (X.setNode bl n { rn with cs := l }) bl [n] := by
  have ho := objs_perm hd hB hr { rn with cs := l }
  rw [setNode_perm_eq hB] at ho ⊢
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, fun _ _ h => h, fun _ _ h => h,
    ?_, ?_, ?_, fun _ _ _ => Iff.rfl, ?_, ?_⟩
  · intro bl' hne B0 hB0
    refine ⟨B0, ?_, bktSim_refl B0, fun _ => optRel_nodeSim_refl _⟩
    show (X.t.bs.insert bl _) !! bl' = some B0
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hB0
  · intro bl' hne h0
    show (X.t.bs.insert bl _) !! bl' = none
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact h0
  · intro B0 hB0
    rw [hB] at hB0; cases hB0
    refine ⟨_, GMap.lookup_insert _ _ _, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun l' hl' => ?_⟩
    have hne : n ≠ l' := fun e => hl' (by rw [e]; exact List.mem_singleton_self _)
    simp only
    rw [GMap.lookup_insert_ne _ _ hne]
    exact optRel_nodeSim_refl _
  · intro y hy
    rw [ho]
    by_cases e : n = y
    · subst e; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ e]; exact hy
  · intro bl' B0 B' l' r r' hB0 hB' hr hr' hT hv
    change (X.t.bs.insert bl _) !! bl' = some B' at hB'
    by_cases hb : bl = bl'
    · subst hb
      rw [hB] at hB0; cases hB0
      have hne : n ≠ l' := fun e => hT rfl (by rw [e]; exact List.mem_singleton_self _)
      rw [GMap.lookup_insert] at hB'; cases hB'
      simp only at hr'
      rw [GMap.lookup_insert_ne _ _ hne, hr] at hr'; cases hr'; exact hv
    · rw [GMap.lookup_insert_ne _ _ hb, hB0] at hB'; cases hB'
      rw [hr] at hr'; cases hr'; exact hv

/-- **The step of the permutation** (no freelist step). -/
theorem spStep_perm (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn) (hp : rn.cs.Perm l)
    {w : WDb} (O : List Nat) (hG : spG X w.wtxid (mapLen w.ms) w.fl) :
    spStep X (X.setNode bl n { rn with cs := l }) w w O [] := by
  have hG' := spG_perm hB hr hp hG
  have hP := spP_perm (n := n) hB { rn with cs := l }
  refine ⟨rfl, rfl, by rw [setNode_perm_eq hB], hG', ?_, fun _ h => h,
    fun x hx => absurd (by rw [hP]) hx, fun F _ hf => ?_⟩
  · rw [setNode_perm_eq hB]; exact hG.2.1
  · rw [setNode_perm_eq hB]; exact hf

/-! ## `n`'s facts -/

/-- **`n`'s branch facts are kept.** -/
theorem uBr_perm (hd : objsDisj X.t) (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (hp : rn.cs.Perm l) {hwm : Nat} {lo hi : Option (List w8)} {h : Nat} {es : List UE}
    (hb : uBr X bl (spP X) hwm n rn lo hi h es) :
    uBr (X.setNode bl n { rn with cs := l }) bl (spP (X.setNode bl n { rn with cs := l })) hwm n
      { rn with cs := l } lo hi h es := by
  have hfr := spFrame_perm (l := l) hd hB hr
  have hP := spP_perm (n := n) hB { rn with cs := l }
  have hnsp : ¬ spilledN X bl n := by
    rintro ⟨-, rc, hrc, -, hsp, -⟩
    rw [hb.node] at hrc; cases hrc
    rw [hb.un.2.2.1] at hsp; cases hsp
  have hnN : ∀ e ∈ es, n ∉ e.N := fun e he hm =>
    (List.nodup_cons.1 hb.Nnd).1 (List.mem_flatMap.2 ⟨e, he, hm⟩)
  refine ⟨node_perm_self hB, ?_, hb.leaf, hb.two, hb.len, ?_, hb.chnd, ?_, hp.nodup_iff.1 hb.csnd,
    hb.Nnd, hb.pg0⟩
  · rw [setNode_perm_eq hB]; exact hb.un
  · intro i w e hw he
    refine uEnt_move hfr (Nat.le_refl _) (hb.ent i w e hw he) (fun x _ => by rw [hP])
      (fun y hy => ?_) rfl (fun c hc => hp.mem_iff.1 hc) (bndIn_refl _)
    rw [List.mem_singleton] at hy; subst hy
    exact ⟨hnN e (List.mem_of_getElem? he), hnsp⟩
  · intro c hc
    rcases hb.cs c (hp.mem_iff.2 hc) with he | hs
    · exact Or.inl he
    · refine Or.inr (spilledN_frame hfr hs ?_)
      rw [List.mem_singleton]; rintro rfl; exact hnsp hs

/-- A chain of parents is one in a bucket with the same parents. -/
theorem onChain_of_parents {B B' : BRec}
    (hpar : ∀ a, (B'.ns !! a).map (·.nv.parent') = (B.ns !! a).map (·.nv.parent'))
    {a rt x : Loc} (h : onChain B' a rt x) : onChain B a rt x := by
  induction h with
  | self a rt => exact .self a rt
  | up a rt x r hra hne _ ih =>
    have e := hpar a
    rw [hra] at e
    cases e' : B.ns !! a with
    | none => rw [e'] at e; cases e
    | some r0 =>
      rw [e'] at e
      have : r.nv.parent' = r0.nv.parent' := Option.some.inj e
      exact .up a rt x r0 e' hne (this ▸ ih)

/-- **`n`'s context is kept** (`n` one of its tree's nodes `N`). -/
theorem spCtx_perm (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn) (hp : rn.cs.Perm l)
    {lo hi : Option (List w8)} {N : List Loc} {cs : SpCase} (hn : n ∈ N)
    (h : spCtx X bl n rn lo hi N cs) :
    spCtx (X.setNode bl n { rn with cs := l }) bl n { rn with cs := l } lo hi N cs := by
  cases cs with
  | child pl rp j plo phi =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := h
    have hpl : pl ≠ n := fun e => a3 (e ▸ hn)
    refine ⟨a1, a2, a3, by rw [node_perm_ne hB hpl]; exact a4, ?_, a6, a7, a8, a9, a10, a11, a12,
      fun c hc => a13 c (hp.mem_iff.2 hc), a14⟩
    rw [setNode_perm_eq hB]; exact a5
  | top =>
    obtain ⟨a1, B0, hB0, hrt, hch⟩ := h
    rw [hB] at hB0; cases hB0
    refine ⟨a1, _, by rw [setNode_perm_eq hB]; exact GMap.lookup_insert _ _ _, ?_⟩
    have hs : bktP B { B with ns := B.ns.insert n { rn with cs := l } } := by
      have := bs_perm hB hr hp bl
      rw [hB, GMap.lookup_insert] at this; exact this
    refine ⟨nodeRootIn_perm hs hrt, fun x hx hxn => ?_⟩
    -- the chain: the parents as before, the nodes other than `n` unchanged
    have hpar : ∀ a, (({ B with ns := B.ns.insert n { rn with cs := l } } : BRec).ns !! a).map
        (·.nv.parent') = (B.ns !! a).map (·.nv.parent') := by
      intro a
      by_cases e : n = a
      · subst e; rw [GMap.lookup_insert, hr]; rfl
      · rw [GMap.lookup_insert_ne _ _ e]
    obtain ⟨hxl, rc, hrc, hrest⟩ := hch x (onChain_of_parents hpar hx) hxn
    refine ⟨?_, rc, by rw [node_perm_ne hB hxn]; exact hrc, hrest⟩
    rw [setNode_perm_eq hB]; exact hxl

/-- **The children's loop's start** after the sort: from `n`'s unspilled tree (a branch) at the
start, its slots and freeable pages, the invariant at `0` from the permuted state. -/
theorem spLoop_start (hd : objsDisj X.t) (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (hp : rn.cs.Perm l) {w : WDb} {O : List Nat} {lo hi : Option (List w8)} {h : Nat}
    {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl (spP X) X.t.mv.pgid'.toNat n lo hi h F D N E)
    (hleaf : rn.nv.isLeaf' = false) (hG : spG X w.wtxid (mapLen w.ms) w.fl)
    (hsl : slotInv w.fl X.t.mv.pgid'.toNat (O ++ D)) (hfr : spFree X w.fl w.wtxid F) :
    ∃ h' es, h = h' + 1 ∧
      spLoop (X.setNode bl n { rn with cs := l }) w bl n { rn with cs := l } O lo hi h' D N E
        (X.setNode bl n { rn with cs := l }) w { rn with cs := l } es 0 [] [] := by
  have hrn : X.node bl n = some rn := by unfold WX.node; rw [hB]; exact hr
  obtain ⟨h', es, rfl, rfl, rfl, rfl, rfl, hb⟩ := uBr_of_uTree hu hrn hleaf
  refine ⟨h', es, rfl, ?_⟩
  have hb' := uBr_perm hd hB hr hp hb
  have hmv : (X.setNode bl n { rn with cs := l }).t.mv = X.t.mv := by rw [setNode_perm_eq hB]
  have hv : (X.setNode bl n { rn with cs := l }).v = X.v := by rw [setNode_perm_eq hB]
  have hb'' : uBr (X.setNode bl n { rn with cs := l }) bl (spP (X.setNode bl n { rn with cs := l }))
      (X.setNode bl n { rn with cs := l }).t.mv.pgid'.toNat n { rn with cs := l } lo hi h' es := by
    rw [hmv]; exact hb'
  have H := spLoop_init (w := w) (O := O) hb'' (spG_perm hB hr hp hG)
    (by rw [hmv, hv]; exact hsl)
    (by rw [setNode_perm_eq hB]; exact hfr)
  rw [hv] at H
  exact H

/-- **A spill done from the permuted state is one from the start** (`n` one of its tree's nodes
`N`). -/
theorem spDone_unperm (hd : objsDisj X.t) (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (hp : rn.cs.Perm l) {w : WDb} (hG : spG X w.wtxid (mapLen w.ms) w.fl) {Xf : WX} {wf : WDb}
    {O : List Nat} {lo hi : Option (List w8)} {h : Nat} {D : List Nat} {N : List Loc}
    {E : List El} {cs : SpCase} {st : List FLStep} (hn : n ∈ N) (hsp0 : rn.nv.spilled' = false)
    (hnc : n ∉ rn.cs) (hdone : spDone (X.setNode bl n { rn with cs := l }) Xf w wf bl n { rn with cs := l } O lo hi
      h D N E cs st) :
    spDone X Xf w wf bl n rn O lo hi h D N E cs st := by
  have hst := spStep_perm hB hr hp O hG
  have hfr := spFrame_perm (l := l) hd hB hr
  have hmv : (X.setNode bl n { rn with cs := l }).t.mv = X.t.mv := by rw [setNode_perm_eq hB]
  have hP := spP_perm (n := n) hB { rn with cs := l }
  have hnone := fun (y : Loc) (hy : (X.setNode bl n { rn with cs := l }).t.objs !! y = none) =>
    objs_perm_none hd hB hr _ hy
  obtain ⟨hstep, hcase⟩ := hdone
  have hstep' := spStep_trans hst hstep
  rw [List.nil_append] at hstep'
  refine ⟨hstep', ?_⟩
  rcases hcase with ⟨hsp, -, -⟩ | ⟨hsp, T, D', hfrm, hT, hsl, hDk, hDn, hPd, hm⟩
  · simp only at hsp; rw [hsp0] at hsp; cases hsp
  · refine Or.inr ⟨hsp, T, D', ?_, ?_, hsl, hDk, fun s hs => by rw [hmv] at hDn; exact hDn s hs,
      fun x hx => hPd x (by rw [hP]; exact hx), ?_⟩
    · exact spFrame_mono (spFrame_trans hfr hfrm) (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · rw [List.mem_singleton] at hy; subst hy; exact List.mem_append_left _ hn
        · exact hy)
    · intro y hy
      rcases hT y hy with h1 | h1 | ⟨h1, h2⟩
      · exact Or.inl (hnone y h1)
      · exact Or.inr (Or.inl h1)
      · have hyn : y ≠ n := fun e => hnc (e ▸ hp.mem_iff.2 h2.1)
        exact Or.inr (Or.inr ⟨h1, hp.mem_iff.2 h2.1, fun r hr0 =>
          h2.2 r (by rw [node_perm_ne hB hyn]; exact hr0)⟩)
    · cases cs with
      | child pl rp j plo phi =>
        obtain ⟨ps, rp', h1, h2, h3, h4, h5, h6, h7, h8⟩ := hm
        exact ⟨ps, rp', h1, h2, fun x hx => hnone x.l (h3 x hx), h4, h5, h6, h7, h8⟩
      | top => exact hm

end perm

end Spill

end bbolt
end EtcdGrove
end Perennial
