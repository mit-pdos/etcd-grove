/-
`rblX` through a node's removal (U8b, `Rebalance/RblXSteps.lean`): `X.kill bl B' n rn` (bucket
`bl`'s record `B'`, its nodes some of `B`'s but `n`, which goes dead) and one extent freed keep
`rblX` and give `rblRel`, given the bucket's own facts after the step (its `rblB`, nested
entries, finite tree, leaves, the freelist agreement, its live nodes reached): `rblX_kill`. The
registry, objects, live set and the other buckets are kept by the shape of the change.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSSim
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSDefs
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSRmT

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section kill
variable [GooseExts]

theorem kill_look (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) (c : Loc) :
    (X.kill bl B' n rn).t.bs !! c = if c = bl then some B' else X.t.bs !! c :=
  setBkt_look X bl B' c

theorem kill_live (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) (l : Loc) :
    l ∈ (X.kill bl B' n rn).live ↔ l ≠ n ∧ l ∈ X.live := by
  show ((X.live.delete n) !! l).isSome = true ↔ _
  rw [GMap.lookup_delete_iff]
  by_cases h : n = l
  · subst h; simp
  · rw [if_neg h]; exact ⟨fun h' => ⟨fun e => h e.symm, h'⟩, fun h' => h'.2⟩

theorem kill_ltree (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) :
    ltree (X.kill bl B' n rn) = ltree (X.setBkt bl B') := rfl
theorem kill_fuel (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) :
    (X.kill bl B' n rn).fuel = (X.setBkt bl B').fuel := rfl
theorem kill_rootPid (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) :
    (X.kill bl B' n rn).rootPid = (X.setBkt bl B').rootPid := rfl
theorem kill_leaves (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) :
    (X.kill bl B' n rn).leaves = (X.setBkt bl B').leaves := rfl
theorem kill_positions (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) :
    (X.kill bl B' n rn).positions = (X.setBkt bl B').positions := rfl
theorem kill_posExtent (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) :
    (X.kill bl B' n rn).posExtent = (X.setBkt bl B').posExtent := rfl
theorem kill_rtOK (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) (c : Loc) :
    rtOK (X.kill bl B' n rn) c ↔ rtOK (X.setBkt bl B') c := Iff.rfl
theorem kill_rootEnts (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) :
    rootEnts (X.kill bl B' n rn) = rootEnts (X.setBkt bl B') := rfl
theorem kill_bktLoc (X : WX) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec) :
    bktLoc (X.kill bl B' n rn) = bktLoc (X.setBkt bl B') := rfl

theorem bktReach_mono (X X' : WX) (hrl : X'.rl = X.rl)
    (hbm : ∀ bl B, X.t.bs !! bl = some B → ∃ B', X'.t.bs !! bl = some B' ∧ B'.bm = B.bm)
    (c : Loc) (h : bktReach X c) : bktReach X' c := by
  induction h with
  | root => rw [← hrl]; exact bktReach.root
  | child d e C nm hC hm _ ih =>
    obtain ⟨C', hC', he⟩ := hbm d C hC
    exact bktReach.child d e C' nm hC' (by rw [he]; exact hm) ih

theorem freePages_len (fl : FLPg) (txid E : w64) (N : Nat)
    (hlen : ∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length) :
    ∀ t p, (fl.freePages txid E N).pending !! t = some p → p.ids.length = p.alloctx.length := by
  intro t p hp
  rcases freePages_pending_lookup fl txid E N t p hp with ⟨-, h⟩ | ⟨rfl, P, hP, rfl⟩
  · exact hlen t p h
  · simp only [List.length_append, List.length_replicate, runIds, List.length_map,
      List.length_range]
    cases h : fl.pending !! t with
    | none => rw [h] at hP; simp at hP; rw [← hP]
    | some P0 => rw [h] at hP; simp at hP; rw [← hP, hlen t P0 h]

/-- **`rblX` through a node's removal** (see the module doc). -/
theorem rblX_kill (X : WX) (fl : FLPg) (bl : Loc) (dfc dfc' : Option Loc) (B B' : BRec)
    (n : Loc) (rn : NRec) (E : w64) (N : Nat) (txid : w64)
    (hI : rblX X fl bl dfc) (hb : X.t.bs !! bl = some B) (hn : (B.ns !! n).isSome = true)
    (k1 : B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.bm = B.bm)
    (k2 : ∀ y ry', B'.ns !! y = some ry' → y ≠ n ∧ ∃ ry, B.ns !! y = some ry ∧
      ry'.nv.pgid' = ry.nv.pgid')
    (k2b : ∀ y ry', B'.ns !! y = some ry' → ∀ w ∈ ry'.ws, ∃ y2 ry2, B.ns !! y2 = some ry2 ∧
      ry2.nv.isLeaf' = ry'.nv.isLeaf' ∧ w ∈ ry2.ws)
    (k3 : ∀ y ry, B.ns !! y = some ry → y ≠ n → (B'.ns !! y).isSome = true)
    (kpp : ∀ y j c, pagePosAt B' y j c → ∃ y' j', pagePosAt B y' j' c)
    (hB' : rblB X.v X.t.mv.pgid'.toNat bl B' dfc')
    (hent : ∀ k v, entryIn X.v B k v → entryIn X.v B' k v)
    (hrt : rtOK (X.kill bl B' n rn) bl)
    (hlv : ((X.kill bl B' n rn).leaves bl).flatten = (X.leaves bl).flatten)
    (hfl : flView (X.kill bl B' n rn) (fl.freePages txid E N) ∧ covU (X.kill bl B' n rn))
    (hlr : ∀ l r, B'.ns !! l = some r → l ∈ (X.kill bl B' n rn).live →
      ∃ rt, nodeRootIn B' B'.bv.rootNode' rt ∧ descIn B' rt l)
    (hcan : fl.canFree txid E N) (hpg : ∃ pg, X.v.pages !! E.toNat = some pg ∧ 1 + pageOverflow pg = N) :
    rblX (X.kill bl B' n rn) (fl.freePages txid E N) bl dfc' ∧
      rblRel X fl (X.kill bl B' n rn) (fl.freePages txid E N) txid := by
  obtain ⟨⟨htw, hpm, hhwm, htx, hrl⟩, hBk, hEB, hH, hL, hN, hV, hLR, -, -, hX, hPL, hOD, hRH, hLS,
    hPS⟩ := hI
  have hshape : leafShape (X.kill bl B' n rn) ∧ posShape (X.kill bl B' n rn) :=
    shapes_frame X (X.kill bl B' n rn) bl B B' rfl rfl hb (kill_look X bl B' n rn)
      (fun y ry' hy hl w hw => by
        obtain ⟨y2, ry2, h2, hl2, hw2⟩ := k2b y ry' hy w hw
        exact Or.inr ⟨y2, ry2, h2, by rw [hl2]; exact hl, hw2⟩)
      (posRoot_of_pagePos k1.1 k1.2.1 kpp _) hLS hPS
  have hdom : ∀ c, ((X.kill bl B' n rn).t.bs !! c).isSome = (X.t.bs !! c).isSome := by
    intro c; rw [kill_look]; split
    · subst c; rw [hb]; rfl
    · rfl
  have hnoth : ∀ c C, X.t.bs !! c = some C → c ≠ bl → C.ns !! n = none :=
    fun c C hC hc => hOD bl B hb n hn c C hC hc
  have hback : ∀ c C, (X.kill bl B' n rn).t.bs !! c = some C → ∃ C0, X.t.bs !! c = some C0 ∧
      (c = bl ∧ C0 = B ∧ C = B' ∨ c ≠ bl ∧ C = C0) := by
    intro c C hC
    rw [kill_look] at hC
    split at hC
    · subst c; cases hC; exact ⟨B, hb, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨C, hC, Or.inr ⟨‹_›, rfl⟩⟩
  have hfwd : ∀ c C0, X.t.bs !! c = some C0 → ∃ C, (X.kill bl B' n rn).t.bs !! c = some C ∧
      C.ib = C0.ib ∧ C.bv = C0.bv ∧ C.bm = C0.bm := by
    intro c C0 hC0
    by_cases hc : c = bl
    · subst hc; rw [hb] at hC0; cases hC0
      exact ⟨B', by rw [kill_look, if_pos rfl], k1.2.1, k1.1, k1.2.2⟩
    · exact ⟨C0, by rw [kill_look, if_neg hc]; exact hC0, rfl, rfl, rfl⟩
  have hnest : ∀ C0 C, bktNested X.v X.t C0 → C.bm = C0.bm →
      (∀ k v, entryIn X.v C0 k v → entryIn X.v C k v) →
      bktNested X.v (X.kill bl B' n rn).t C := by
    intro C0 C hn' hbm he k c hk
    rw [hbm] at hk
    obtain ⟨D0, v, hD0, hev, hlen, hinl, hroot, hib⟩ := hn' k c hk
    obtain ⟨D, hD, hDib, hDbv, -⟩ := hfwd c D0 hD0
    exact ⟨D, v, hD, he k v hev, hlen, hinl, by rw [hDib]; exact hroot,
      fun h => by rw [hDib]; exact hib (by rw [← hDbv]; exact h)⟩
  have hobjs : ∀ k, (X.t.objs !! k).isSome = true →
      ((X.kill bl B' n rn).t.objs !! k).isSome = true := by
    apply objs_isSome_mono X.t (X.kill bl B' n rn).t
    · intro k hk
      show ((X.t.dead.insert n (bl, rn)) !! k).isSome = true
      rw [GMap.lookup_insert_eq_iff]; split
      · rfl
      · exact hk
    · intro c C k hC hk
      by_cases hkn : k = n
      · subst hkn; left
        show ((X.t.dead.insert k (bl, rn)) !! k).isSome = true
        rw [GMap.lookup_insert]; rfl
      · right
        by_cases hc : c = bl
        · subst hc; rw [hb] at hC; cases hC
          obtain ⟨ry, hry⟩ := Option.isSome_iff_exists.1 hk
          exact ⟨c, B', by rw [kill_look, if_pos rfl], k3 k ry hry hkn⟩
        · exact ⟨c, C, by rw [kill_look, if_neg hc]; exact hC, hk⟩
  have hobjsB : ∀ k, (X.t.bobjs !! k).isSome = true →
      ((X.kill bl B' n rn).t.bobjs !! k).isSome = true :=
    bobjs_isSome_mono X.t (X.kill bl B' n rn).t (fun _ h => h) (fun c h => by rw [hdom]; exact h)
  obtain ⟨pg, hpgE, hNe⟩ := hpg
  refine ⟨⟨⟨htw, hpm, hhwm, htx, by rw [hdom]; exact hrl⟩, ?_, ?_, ?_, ?_, ?_, hV, ?_, hfl.1, hfl.2,
    hX, freePages_len fl txid E N hPL, ?_, fun c h => hRH c (by rw [← hdom]; exact h), hshape⟩, ?_⟩
  · -- the buckets
    intro c C hC
    obtain ⟨C0, hC0, hcase⟩ := hback c C hC
    obtain ⟨h1, h2, h3, h4, h5⟩ := hBk c C0 hC0
    rcases hcase with ⟨hc, hC0e, hCe⟩ | ⟨hc, rfl⟩
    · subst C; subst C0; subst c
      refine ⟨by rw [if_pos rfl]; exact hB', fun nm d hd => ?_, hnest B B' h3 k1.2.2 hent,
        hrt, fun l r hr => ?_⟩
      · rw [k1.2.2] at hd; rw [hdom]; exact h2 nm d hd
      · obtain ⟨hln, ry, hry, -⟩ := k2 l r hr
        exact (kill_live X bl B' n rn l).2 ⟨hln, h5 l ry hry⟩
    · refine ⟨by rw [if_neg hc]; rw [if_neg hc] at h1; exact h1, fun nm d hd => by
          rw [hdom]; exact h2 nm d hd, hnest C C h3 rfl (fun _ _ h => h),
        (kill_rtOK X bl B' n rn c).2 (setBkt_rtOK_other X bl B B' hb k1.2.1 c hc h4),
        fun l r hr => (kill_live X bl B' n rn l).2 ⟨(fun he => by
          rw [he, hnoth c C hC0 hc] at hr; cases hr), h5 l r hr⟩⟩
  · -- entries bounded
    intro c C hC l r hr w hw
    obtain ⟨C0, hC0, hcase⟩ := hback c C hC
    rcases hcase with ⟨hc, hC0e, hCe⟩ | ⟨hc, rfl⟩
    · subst C; subst C0; subst c
      obtain ⟨y2, ry2, hy2, -, hw2⟩ := k2b l r hr w hw
      exact hEB bl B hC0 y2 ry2 hy2 w hw2
    · exact hEB c C hC0 l r hr w hw
  · intro b nm h; exact hobjsB b (hH b nm h)
  · obtain ⟨l1, l2, l3, l4, l5⟩ := hL
    refine ⟨l1, fun l h => hobjs l (l2 l
      ((kill_live X bl B' n rn l).1 h).2), fun c C hC => ?_, fun c C l r hC hr => ?_,
      fun l hl => ?_⟩
    · obtain ⟨C0, hC0, -⟩ := hback c C hC
      exact l3 c C0 hC0
    · obtain ⟨C0, hC0, hcase⟩ := hback c C hC
      rcases hcase with ⟨hc, hC0e, hCe⟩ | ⟨hc, rfl⟩
      · subst C; subst C0; subst c
        obtain ⟨hln, ry, hry, -⟩ := k2 l r hr
        exact (kill_live X bl B' n rn l).2 ⟨hln, l4 bl B l ry hC0 hry⟩
      · exact (kill_live X bl B' n rn l).2 ⟨(fun he => by
          rw [he, hnoth c C hC0 hc] at hr; cases hr), l4 c C l r hC0 hr⟩
    · intro hlv'
      obtain ⟨hln, hlx⟩ := (kill_live X bl B' n rn l).1 hlv'
      have : (X.t.dead !! l).isSome = true := by
        have h' : ((X.t.dead.insert n (bl, rn)) !! l).isSome = true := hl
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hln)] at h'; exact h'
      exact l5 l this hlx
  · -- the registry
    intro y c p h hl
    obtain ⟨hyn, hyl⟩ := (kill_live X bl B' n rn y).1 hl
    obtain ⟨C0, r0, hC0, hr0, hp⟩ := hN y c p h hyl
    by_cases hc : c = bl
    · subst hc; rw [hb] at hC0; cases hC0
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (k3 y r0 hr0 hyn)
      obtain ⟨-, ry, hry, hpe⟩ := k2 y r' hr'
      rw [hr0] at hry; cases hry
      exact ⟨B', r', by rw [kill_look, if_pos rfl], hr', by rw [hpe]; exact hp⟩
    · exact ⟨C0, r0, by rw [kill_look, if_neg hc]; exact hC0, hr0, hp⟩
  · -- reached
    obtain ⟨r1, r2⟩ := hLR
    refine ⟨fun c C hC hl => ?_, fun c C l r hC hr hl => ?_⟩
    · obtain ⟨C0, hC0, -⟩ := hback c C hC
      refine bktReach_mono X (X.kill bl B' n rn) rfl (fun d D hD => ?_) c (r1 c C0 hC0 hl)
      obtain ⟨D', hD', -, -, hbm⟩ := hfwd d D hD
      exact ⟨D', hD', hbm⟩
    · obtain ⟨C0, hC0, hcase⟩ := hback c C hC
      rcases hcase with ⟨hc, hC0e, hCe⟩ | ⟨hc, rfl⟩
      · subst C; subst C0; subst c
        exact hlr l r hr hl
      · exact r2 c C l r hC0 hr ((kill_live X bl B' n rn l).1 hl).2
  · -- disjoint
    apply objsDisj_mono X.t (X.kill bl B' n rn).t hOD hdom
    intro c C' hC'
    obtain ⟨C0, hC0, hcase⟩ := hback c C' hC'
    refine ⟨C0, hC0, fun k hk => ?_⟩
    rcases hcase with ⟨hc, hC0e, hCe⟩ | ⟨hc, rfl⟩
    · subst hCe; subst hC0e
      obtain ⟨ry', hry'⟩ := Option.isSome_iff_exists.1 hk
      obtain ⟨-, ry, hry, -⟩ := k2 k ry' hry'
      rw [hry]; rfl
    · exact hk
  · -- the relation
    refine ⟨rfl, rfl, rfl, fun _ _ h => h, rfl, rfl, rfl, rfl, hdom, fun c C0 C hC0 hC => ?_,
      fun c => ?_, [(E, N)], ⟨hcan, trivial⟩, rfl, fun e he => ?_⟩
    · obtain ⟨C', hC', h1, h2, h3⟩ := hfwd c C0 hC0
      rw [hC'] at hC; cases hC
      exact ⟨h2, h1, h3⟩
    · by_cases hc : c = bl
      · subst hc; rw [hlv]
      · rw [kill_leaves, setBkt_leaves_other X bl B B' hb k1.2.1 c hc]
    · simp only [List.mem_singleton] at he; subst he
      exact ⟨pg, hpgE, hNe⟩

end kill

end bbolt
end EtcdGrove
end Perennial
