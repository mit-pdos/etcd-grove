/-
**The API proof's store ghost state** (stage 1, 2026-11-03; `notes/mvcc-api-invariants.md` §1 and
§2, round 16). Lean-first (no Rocq counterpart). A module of the API's parallel internals
(`Proof/.../mvcc/Api/`, `notes/decisions.md`, "parallel internals"): today's internals are
untouched.

* `γ.abs`: the client's view of the committed history and the compaction revision (`σ.log`,
  `σ.crev`), a ghost variable: ½ the client (`mvccState`), ¼ `s.revMu`'s resource, ¼ the writer's
  state.
* `γ.pnd`: the pending revision (`σ.pending`): ½ the client, the rest the writer's state and (a
  watchable store) `watchStoreBody`.
* `γ.crevLb`: a monotone lower bound of `σ.crev + 1`, its authority split ½ the client, ¼ the
  compaction right, ¼ `s.revMu`'s resource.
* `γ.tok`: the backend share token, of total 1 (round 16, the review's F2): `mvccBackend γ q`
  holds `q` of it, so the whole share excludes every step that changes the history.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.MonoNat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI

/-- The API's ghost names of a store. -/
structure AbsNames where
  abs : GName
  pnd : GName
  crevLb : GName
  tok : GName

/-- A compaction revision as the lower bound's count (`-1` is `0`). -/
def crevN (c : Int) : Nat := (c + 1).toNat

section ghost
variable {GF : BundledGFunctors} [AllG GF]

/-- A share of the client's view of the history and compaction revision. -/
def absPart (γ : AbsNames) (q : Qp) (L : Log) (c : Int) : IProp GF := ghostVar γ.abs q (L, c)

/-- A share of the pending revision. -/
def pndPart (γ : AbsNames) (q : Qp) (p : Option (List Change)) : IProp GF := ghostVar γ.pnd q p

/-- A share of the compaction revision's authority. -/
def crevAuth (γ : AbsNames) (q : Qp) (c : Int) : IProp GF := monoNatAuthOwn γ.crevLb q (crevN c)

/-- The compaction revision is at least `c` (persistent). -/
def crevAtLeast (γ : AbsNames) (c : Int) : IProp GF := monoNatLbOwn γ.crevLb (crevN c)

/-- A share `q` of the backend share token. -/
def shareTok (γ : AbsNames) (q : Qp) : IProp GF := dghostVar γ.tok (.own q) ()

instance crevAtLeast_persistent (γ : AbsNames) (c : Int) : Persistent (crevAtLeast (GF := GF) γ c) := by
  unfold crevAtLeast; infer_instance

instance absPart_timeless (γ : AbsNames) (q : Qp) (L : Log) (c : Int) :
    Timeless (absPart (GF := GF) γ q L c) := by unfold absPart; infer_instance
instance pndPart_timeless (γ : AbsNames) (q : Qp) (p : Option (List Change)) :
    Timeless (pndPart (GF := GF) γ q p) := by unfold pndPart; infer_instance
instance crevAuth_timeless (γ : AbsNames) (q : Qp) (c : Int) :
    Timeless (crevAuth (GF := GF) γ q c) := by unfold crevAuth; infer_instance
instance shareTok_timeless (γ : AbsNames) (q : Qp) : Timeless (shareTok (GF := GF) γ q) := by
  unfold shareTok; infer_instance

/-- The share token splits. -/
theorem shareTok_split (γ : AbsNames) (q1 q2 : Qp) :
    shareTok (GF := GF) γ (q1 + q2) ⊢ shareTok γ q1 ∗ shareTok γ q2 := by
  unfold shareTok
  have h : (DFrac.own q1 • DFrac.own q2 : DFrac) = DFrac.own (q1 + q2) := rfl
  rw [← h]
  iintro H
  iapply dghostVar_split γ.tok () (.own q1) (.own q2) $$ H

/-- **The whole share excludes any other** (the frozen writer state's contradiction). -/
theorem shareTok_excl (γ : AbsNames) (q : Qp) :
    shareTok (GF := GF) γ 1 ∗ shareTok γ q ⊢ False := by
  unfold shareTok
  iintro ⟨H1, H2⟩
  ihave %H := dghostVar_valid_2 γ.tok () (.own 1) () (.own q) $$ H1 H2
  exfalso
  have := DFrac.valid_own_op H.1
  simp at this

/-- Two shares of the view agree. -/
theorem absPart_agree (γ : AbsNames) (q1 q2 : Qp) (L1 L2 : Log) (c1 c2 : Int) :
    absPart (GF := GF) γ q1 L1 c1 ∗ absPart γ q2 L2 c2 ⊢ ⌜L1 = L2 ∧ c1 = c2⌝ := by
  unfold absPart
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  ipureintro
  exact Prod.mk.inj H.2

/-- Two shares of the pending revision agree. -/
theorem pndPart_agree (γ : AbsNames) (q1 q2 : Qp) (p1 p2 : Option (List Change)) :
    pndPart (GF := GF) γ q1 p1 ∗ pndPart γ q2 p2 ⊢ ⌜p1 = p2⌝ := by
  unfold pndPart
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  ipureintro
  exact H.2

/-- The view's shares join and split (the two quarters inside are joined before an update). -/
instance absPart_fractional (γ : AbsNames) (L : Log) (c : Int) :
    Fractional (fun q => absPart (GF := GF) γ q L c) := by
  unfold absPart; infer_instance

instance pndPart_fractional (γ : AbsNames) (p : Option (List Change)) :
    Fractional (fun q => pndPart (GF := GF) γ q p) := by
  unfold pndPart; infer_instance

instance crevAuth_fractional (γ : AbsNames) (c : Int) :
    Fractional (fun q => crevAuth (GF := GF) γ q c) := by
  unfold crevAuth; infer_instance

/-- **The view's update**, from two shares making the whole (the client's half and the
internals' half). -/
theorem absPart_update (γ : AbsNames) (q1 q2 : Qp) (h : q1 + q2 = 1) (L1 L2 L' : Log)
    (c1 c2 c' : Int) :
    absPart (GF := GF) γ q1 L1 c1 ∗ absPart γ q2 L2 c2 ⊢
      |==> (absPart γ q1 L' c' ∗ absPart γ q2 L' c') := by
  unfold absPart
  iintro ⟨H1, H2⟩
  iapply ghostVar_update_2 (L', c') γ.abs (L1, c1) q1 (L2, c2) q2 h $$ H1 H2

/-- **The pending revision's update**, from two shares making the whole. -/
theorem pndPart_update (γ : AbsNames) (q1 q2 : Qp) (h : q1 + q2 = 1) (p1 p2 p' : Option (List Change)) :
    pndPart (GF := GF) γ q1 p1 ∗ pndPart γ q2 p2 ⊢
      |==> (pndPart γ q1 p' ∗ pndPart γ q2 p') := by
  unfold pndPart
  iintro ⟨H1, H2⟩
  iapply ghostVar_update_2 p' γ.pnd p1 q1 p2 q2 h $$ H1 H2

/-- **Raising the compaction revision**, with the whole authority. -/
theorem crevAuth_update (γ : AbsNames) (c c' : Int) (h : c ≤ c') :
    crevAuth (GF := GF) γ 1 c ⊢ |==> (crevAuth γ 1 c' ∗ crevAtLeast γ c') := by
  unfold crevAuth crevAtLeast
  iintro H
  iapply mono_nat_own_update (γ := γ.crevLb) (crevN c') (by unfold crevN; omega) $$ H

/-- A lower bound below the authority's value. -/
theorem crevAtLeast_valid (γ : AbsNames) (q : Qp) (c c0 : Int) (hc : -1 ≤ c) :
    crevAuth (GF := GF) γ q c ∗ crevAtLeast γ c0 ⊢ ⌜c0 ≤ c⌝ := by
  unfold crevAuth crevAtLeast
  iintro ⟨H1, H2⟩
  ihave %H := monoNatLbOwn_valid γ.crevLb q (crevN c) (crevN c0) $$ H1 H2
  ipureintro
  unfold crevN at H
  omega

/-- **The store's API ghost state at a new store** (`NewStore`, at `mvccStart`): the view, the
pending revision, the compaction authority and the whole share token. -/
theorem absNames_alloc (L : Log) (c : Int) (p : Option (List Change)) :
    ⊢ |==> ∃ γ : AbsNames, absPart (GF := GF) γ 1 L c ∗ pndPart γ 1 p ∗ crevAuth γ 1 c ∗
      crevAtLeast γ c ∗ shareTok γ 1 := by
  imod ghostVar_alloc (GF := GF) (L, c) with ⟨%ga, Ha⟩
  imod ghostVar_alloc (GF := GF) p with ⟨%gp, Hp⟩
  imod mono_nat_own_alloc (GF := GF) (crevN c) with ⟨%gc, Hc, Hlb⟩
  imod dghostVar_alloc (GF := GF) () with ⟨%gt, Ht⟩
  imodintro
  iexists ⟨ga, gp, gc, gt⟩
  unfold absPart pndPart crevAuth crevAtLeast shareTok
  iframe

end ghost

end api
end mvcc
end EtcdGrove
end Perennial
