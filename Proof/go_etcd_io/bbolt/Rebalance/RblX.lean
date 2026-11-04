/-
`rebalance`'s invariant over the writer's records (U8b, `notes/bbolt-proof-plan.md`):
- `rblX X fl dbl dfc`: the transaction's top-level clean facts; every bucket in the rebalance's
  invariant (`rblB`, `Rebalance/RblDefs.lean`; bucket `dbl` with the deficient node `dfc`), its
  bucket cache's buckets in the transaction, its nested buckets' entries, its logical tree finite
  with its leaves at one depth (`rtOK`), its nodes live; entries bounded, handles, live set,
  registry, the view well-formed, the live objects reached, and the records agreeing with the
  writer's freelist (`flView`);
  The covered slots are covered once (`covU`).
- `rblRel X0 fl0 X fl txid`: what the steps so far kept (the view, handles, root, the
  transaction's fields, the buckets' locations, headers and bucket caches, every bucket's leaves'
  entries in order), grew (the registry) and freed (`Free` steps of base-page extents);
- `rebalOK_of_rbl`: at the end (no deficient node, no node unbalanced), `rebalOK`.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblKeys
public import Proof.go_etcd_io.bbolt.Rebalance.RTreeX

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rblx
variable [GooseExts]

/-- What covers a base slot: a position of an opened bucket's logical tree (its extent), or an
unopened top-level bucket of the root (its base tree). -/
inductive CovW where
  | pos (bl : Loc) (pid : w64)
  | bkt (n : GoString)

/-- `c` covers slot `s` in `X` (`lCovers`' two cases, with their witness). -/
def coverW (X : WX) (s : Nat) : CovW → Prop
  | .pos bl pid => X.t.bs !! bl ≠ none ∧ pid ∈ X.positions bl ∧
      ∃ e, X.posExtent bl pid = some e ∧ e.1.toNat ≤ s ∧ s < e.1.toNat + e.2
  | .bkt n => ∃ v, (n, v) ∈ rootEnts X ∧ bktLoc X n = none ∧ bucketHas X.v.pages v s

/-- **A covered slot is covered once** (no page is shared by two positions, or by a position and
an unopened bucket: what keeps `flView` when a removed node's page becomes pending). -/
def covU (X : WX) : Prop := ∀ s c1 c2, coverW X s c1 → coverW X s c2 → c1 = c2

/-- **`rebalance`'s invariant** (see the module doc). -/
def rblX (X : WX) (fl : FLPg) (dbl : Loc) (dfc : Option Loc) : Prop :=
  (X.t.t.writable' = true ∧ X.t.pm = ∅ ∧ 2 ≤ X.t.mv.pgid'.toNat ∧
    X.v.txid + 1 = X.t.mv.txid'.toNat ∧ (X.t.bs !! X.rl).isSome) ∧
  (∀ bl B, X.t.bs !! bl = some B →
    rblB X.v X.t.mv.pgid'.toNat bl B (if bl = dbl then dfc else none) ∧
    (∀ name c, B.bm !! name = some c → (X.t.bs !! c).isSome) ∧
    bktNested X.v X.t B ∧ rtOK X bl ∧ (∀ l r, B.ns !! l = some r → l ∈ X.live)) ∧
  entriesBounded X ∧ handlesOK X ∧ liveOK X ∧ nlocOK X ∧ viewWF X.v ∧ liveReach X ∧
  flView X fl ∧ covU X

/-- **What the steps so far kept, grew and freed** (see the module doc). -/
def rblRel (X0 : WX) (fl0 : FLPg) (X : WX) (fl : FLPg) (txid : w64) : Prop :=
  X.v = X0.v ∧ X.handles = X0.handles ∧ X.rl = X0.rl ∧
  (∀ x y, X0.nloc !! x = some y → X.nloc !! x = some y) ∧
  X.t.t = X0.t.t ∧ X.t.mv = X0.t.mv ∧ X.t.pm = X0.t.pm ∧ X.t.bufs = X0.t.bufs ∧
  (∀ bl, (X.t.bs !! bl).isSome = (X0.t.bs !! bl).isSome) ∧
  (∀ bl B0 B, X0.t.bs !! bl = some B0 → X.t.bs !! bl = some B →
    B.bv = B0.bv ∧ B.ib = B0.ib ∧ B.bm = B0.bm) ∧
  (∀ bl, (X.leaves bl).flatten = (X0.leaves bl).flatten) ∧
  ∃ es : List (w64 × Nat), fl0.canFreeAll txid es ∧ fl = fl0.freeAll txid es ∧
    ∀ e ∈ es, ∃ pg, X0.v.pages !! e.1.toNat = some pg ∧ 1 + pageOverflow pg = e.2

theorem rblRel_refl (X : WX) (fl : FLPg) (txid : w64) : rblRel X fl X fl txid :=
  ⟨rfl, rfl, rfl, fun _ _ h => h, rfl, rfl, rfl, rfl, fun _ => rfl,
    fun bl B0 B h0 h => by rw [h0] at h; cases h; exact ⟨rfl, rfl, rfl⟩, fun _ => rfl,
    [], trivial, rfl, fun _ h => by cases h⟩

theorem canFreeAll_append (fl : FLPg) (txid : w64) :
    ∀ (es1 es2 : List (w64 × Nat)), fl.canFreeAll txid es1 →
      (fl.freeAll txid es1).canFreeAll txid es2 → fl.canFreeAll txid (es1 ++ es2)
  | [], es2, _, h2 => h2
  | e :: es1, es2, h1, h2 => ⟨h1.1, canFreeAll_append (fl.freePages txid e.1 e.2) txid es1 es2 h1.2 h2⟩

theorem freeAll_append (fl : FLPg) (txid : w64) (es1 es2 : List (w64 × Nat)) :
    fl.freeAll txid (es1 ++ es2) = (fl.freeAll txid es1).freeAll txid es2 := by
  unfold FLPg.freeAll; rw [List.foldl_append]

theorem rblRel_trans (X0 X1 X2 : WX) (fl0 fl1 fl2 : FLPg) (txid : w64)
    (h1 : rblRel X0 fl0 X1 fl1 txid) (h2 : rblRel X1 fl1 X2 fl2 txid) : rblRel X0 fl0 X2 fl2 txid := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, i1, j1, k1, l1, es1, m1, n1, o1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, i2, j2, k2, l2, es2, m2, n2, o2⟩ := h2
  refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, fun x y h => d2 x y (d1 x y h), e2.trans e1,
    f2.trans f1, g2.trans g1, i2.trans i1, fun bl => (j2 bl).trans (j1 bl), ?_,
    fun bl => (l2 bl).trans (l1 bl), es1 ++ es2, ?_, ?_, ?_⟩
  · intro bl B0 B h0 h
    obtain ⟨B1, hB1⟩ : ∃ B1, X1.t.bs !! bl = some B1 := by
      have := j1 bl; rw [h0] at this
      exact Option.isSome_iff_exists.1 this
    obtain ⟨x1, y1, z1⟩ := k1 bl B0 B1 h0 hB1
    obtain ⟨x2, y2, z2⟩ := k2 bl B1 B hB1 h
    exact ⟨x2.trans x1, y2.trans y1, z2.trans z1⟩
  · subst n1; exact canFreeAll_append fl0 txid es1 es2 m1 m2
  · rw [n2, n1, freeAll_append]
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact o1 e he
    · obtain ⟨pg, hpg, hn⟩ := o2 e he; rw [a1] at hpg; exact ⟨pg, hpg, hn⟩

/-- The filtered entries of the leaves depend only on their concatenation. -/
theorem flatMap_filterMap_flatten {β : Type} (f : WEntry → Option β) (L : List (List WEntry)) :
    L.flatMap (fun ws => ws.filterMap f) = L.flatten.filterMap f := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.flatMap_cons, List.flatten_cons, List.filterMap_append, ih]

/-- **The data is kept** by the steps (`rblRel`). -/
theorem wtxData_rblRel (X0 X : WX) (fl0 fl : FLPg) (txid : w64) (h : rblRel X0 fl0 X fl txid) :
    wtxData X = wtxData X0 := by
  obtain ⟨hv, -, hrl, -, -, -, -, -, hsome, hbk, hlv, -⟩ := h
  apply wtxData_rebalance
  · unfold rootEnts; rw [flatMap_filterMap_flatten, flatMap_filterMap_flatten, hrl, hlv]
  · intro n
    unfold bktLoc
    rw [hrl]
    cases h0 : X0.t.bs !! X0.rl with
    | none =>
      have := hsome X0.rl; rw [h0] at this
      cases h1 : X.t.bs !! X0.rl with
      | none => rfl
      | some _ => rw [h1] at this; cases this
    | some B0 =>
      have := hsome X0.rl; rw [h0] at this
      obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 this
      rw [hB]; simp only [Option.bind_some]; rw [(hbk _ B0 B h0 hB).2.2]
  · intro n bl _
    unfold lbktEnts; rw [flatMap_filterMap_flatten, flatMap_filterMap_flatten, hlv]
  · rw [hv]

/-- **At the end, `rebalOK`** (no deficient node and no node unbalanced). -/
theorem rebalOK_of_rbl (X0 X : WX) (fl0 fl : FLPg) (dbl : Loc) (txw : w64)
    (hI : rblX X fl dbl none) (hR : rblRel X0 fl0 X fl txw)
    (hbal : ∀ bl B l r, X.t.bs !! bl = some B → B.ns !! l = some r → r.nv.unbalanced' = false) :
    rebalOK X0 X fl0 fl txw ∧ liveReach X ∧ flView X fl := by
  obtain ⟨⟨hw, hpm, hhwm, htxid, hrl⟩, hB, hEB, hH, hL, hN, hV, hLR, hFV, -⟩ := hI
  have hR' := hR
  obtain ⟨hv, hh, hrl', hnl, -, -, -, -, -, -, -, es, hcan, hfl, hes⟩ := hR'
  have hBn : ∀ bl B, X.t.bs !! bl = some B → rblB X.v X.t.mv.pgid'.toNat bl B none := by
    intro bl B hb
    have := (hB bl B hb).1
    rwa [ite_self] at this
  refine ⟨⟨⟨⟨hw, hpm, hhwm, htxid, hrl, fun bl B hb => ⟨(hBn bl B hb).1, (hB bl B hb).2.1⟩⟩,
      fun bl B hb => ⟨?_, (hB bl B hb).2.2.1⟩, ?_, hEB, hH, hL, hN, hV⟩,
    wtxData_rblRel X0 X fl0 fl txw hR, hv, hh, hrl', hnl, ?_, ?_, ⟨es, hcan, hfl, hes⟩, ?_⟩,
    hLR, hFV⟩
  · obtain ⟨-, ⟨bnd, hk⟩, ha, -⟩ := hBn bl B hb
    exact bktKeys_of_rbl X.v B bnd hk ha
  · intro bl B hb l r hr hleaf w hw
    obtain ⟨-, ⟨bnd, hk⟩, -, -⟩ := hBn bl B hb
    exact ((hk.2.2 l r hr).2.2.2.2 hleaf w hw).1
  · intro bl B hb l r hr _
    obtain ⟨-, ⟨bnd, hk⟩, -, -⟩ := hBn bl B hb
    have hn := hk.2.2 l r hr
    have hne : (none : Option Loc) ≠ some l := fun h => by cases h
    refine ⟨fun hp => ?_, fun hbr => (hn.2.2.1 hbr).1 hne⟩
    cases hlf : r.nv.isLeaf' with
    | true => exact hn.2.2.2.1 hne hlf (hbal bl B l r hb hr) hp
    | false => have := (hn.2.2.1 hlf).1 hne; omega
  · intro bl hne _
    obtain ⟨B, hb⟩ := Option.ne_none_iff_exists'.1 hne
    exact leafDepthOK_rt X bl (hB bl B hb).2.2.2.1
  · intro s hs
    rw [← hv] at hs
    exact flView_cover X fl hFV s hs

end rblx

end bbolt
end EtcdGrove
end Perennial
