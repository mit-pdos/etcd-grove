/-
**The API proof's store ghost state** (stage 1, 2026-11-03; `notes/mvcc-api-invariants.md` §1 and
§2, round 16). Lean-first (no Rocq counterpart). Imported by `InvStore` (2026-11-03, in-place slots: `StoreNames.api`, the slot
functions `slotX`/`slotY`/...; `notes/decisions.md`, "slots in place"), so it imports only the model.

* `γ.abs`: the client's view of the committed history and the compaction revision (`σ.log`,
  `σ.crev`), a ghost variable: ½ the client (`mvccState`), ¼ `s.revMu`'s resource, ¼ the writer's
  state.
* `γ.pnd`: the pending revision (`σ.pending`): ½ the client, the rest the writer's state and (a
  watchable store) `watchStoreBody`.
* `γ.crevLb`: a monotone lower bound of `σ.crev + 1`, its authority split ½ the client, ¼ the
  compaction right, ¼ `s.revMu`'s resource.
* `γ.tok`: the backend share token, of total 1 (round 16, the review's F2): `mvccBackend γ q`
  holds `q` of it, so the whole share excludes every step that changes the history.
* `γ.frz`: the writer's frozen flag (a `Bool` ghost variable): whole at `false` in the writer's
  invariant while not frozen, half at `true` there and half the freezer's while frozen
  (`Api/InvStoreX.lean`, `writerInvBodyX`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.MonoList

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
  frz : GName
  /-- the notified log (`σ.notifiedLog`), a monotone list: its authority whole in `mvccState`
  (stage 2, the watch chain, 2026-11-04: a send records a lower bound of it, which the client
  compares with its state in `wsRecv_ok.law`'s plain entailment) -/
  nl : GName
  /-- the store's location (`KV.Compact.contract`, 2026-11-06: a read-only ghost variable,
  `locIs`): the handle's (`isMvcc`) and the open token's (`mvccOpen`) agree on the store they are
  of (the inner store of a watchable one) -/
  loc : GName := 0

instance absNames_countable : Pos.Countable AbsNames :=
  countableOfLeftInverse (fun x : AbsNames => (x.abs, x.pnd, x.crevLb, x.tok, x.frz, x.nl, x.loc))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩)
    (fun _ => rfl)

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

/-- The notified log's authority, at `N`. -/
def nlAuth (γ : AbsNames) (q : Qp) (N : Log) : IProp GF := monoListAuthOwn γ.nl q N

/-- **The store is at `l`** (persistent; `AbsNames.loc`). -/
def locIs (γ : AbsNames) (l : Loc) : IProp GF := dghostVar γ.loc DFrac.discard l

instance locIs_persistent (γ : AbsNames) (l : Loc) : Persistent (locIs (GF := GF) γ l) := by
  unfold locIs; infer_instance

/-- Two facts of the store's location agree. -/
theorem locIs_agree (γ : AbsNames) (l l' : Loc) : locIs (GF := GF) γ l ∗ locIs γ l' ⊢ ⌜l = l'⌝ := by
  unfold locIs
  iintro ⟨H1, H2⟩
  iapply dghostVar_agree γ.loc l DFrac.discard l' DFrac.discard $$ H1 H2

/-- A lower bound of the notified log (persistent). -/
def nlLb (γ : AbsNames) (N : Log) : IProp GF := monoListLbOwn γ.nl N

instance nlLb_persistent (γ : AbsNames) (N : Log) : Persistent (nlLb (GF := GF) γ N) := by
  unfold nlLb; infer_instance
instance nlLb_timeless (γ : AbsNames) (N : Log) : Timeless (nlLb (GF := GF) γ N) := by
  unfold nlLb; infer_instance
instance nlAuth_timeless (γ : AbsNames) (q : Qp) (N : Log) : Timeless (nlAuth (GF := GF) γ q N) := by
  unfold nlAuth; infer_instance

/-- A lower bound is a prefix of the authority's log. -/
theorem nlLb_valid (γ : AbsNames) (q : Qp) (N L : Log) :
    nlAuth (GF := GF) γ q N ∗ nlLb γ L ⊢ ⌜L <+: N⌝ := by
  unfold nlAuth nlLb
  iintro ⟨H1, H2⟩
  ihave %h := mono_list_auth_lb_valid γ.nl q N L $$ H1 H2
  ipureintro; exact h.2

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
pending revision, the compaction authority, the whole share token and the frozen flag (down). -/
theorem absNames_alloc (L : Log) (c : Int) (p : Option (List Change)) (N : Log) (l : Loc) :
    ⊢ |==> ∃ γ : AbsNames, absPart (GF := GF) γ 1 L c ∗ pndPart γ 1 p ∗ crevAuth γ 1 c ∗
      crevAtLeast γ c ∗ shareTok γ 1 ∗ ghostVar γ.frz 1 false ∗ nlAuth γ 1 N ∗ locIs γ l := by
  imod ghostVar_alloc (GF := GF) (L, c) with ⟨%ga, Ha⟩
  imod ghostVar_alloc (GF := GF) p with ⟨%gp, Hp⟩
  imod mono_nat_own_alloc (GF := GF) (crevN c) with ⟨%gc, Hc, Hlb⟩
  imod dghostVar_alloc (GF := GF) () with ⟨%gt, Ht⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%gf, Hf⟩
  imod mono_list_own_alloc (GF := GF) N with ⟨%gn, Hn, -⟩
  imod dghostVar_alloc (GF := GF) l with ⟨%gl, Hl⟩
  imod dghostVar_persist gl _ _ $$ Hl with #Hl
  imodintro
  iexists ⟨ga, gp, gc, gt, gf, gn, gl⟩
  unfold absPart pndPart crevAuth crevAtLeast shareTok nlAuth locIs
  iframe
  iexact Hl

/-- **`s.revMu`'s part of the API's ghost state** at fraction `q` (§1): a quarter of `q` of the
view at the lock's log and compaction revision, and of the compaction revision's authority. -/
def revMuAbs (a : AbsNames) (q : Qp) (L : Log) (c : Int) : IProp GF :=
  iprop(absPart a q.half.half L c ∗ crevAuth a q.half.half c)

instance revMuAbs_fractional (a : AbsNames) (L : Log) (c : Int) :
    Fractional (fun q => revMuAbs (GF := GF) a q L c) where
  fractional q1 q2 := by
    have ha := (absPart_fractional (GF := GF) a L c).fractional q1.half.half q2.half.half
    have hc := (crevAuth_fractional (GF := GF) a c).fractional q1.half.half q2.half.half
    unfold revMuAbs
    rw [Qp_half_add, Qp_half_add]
    constructor
    · iintro ⟨Ha, Hc⟩
      icases ha.1 $$ Ha with ⟨Ha1, Ha2⟩
      icases hc.1 $$ Hc with ⟨Hc1, Hc2⟩
      isplitl [Ha1 Hc1]
      · iframe Ha1 Hc1
      · iframe Ha2 Hc2
    · iintro ⟨⟨Ha1, Hc1⟩, ⟨Ha2, Hc2⟩⟩
      isplitl [Ha1 Ha2]
      · iapply ha.2; iframe Ha1 Ha2
      · iapply hc.2; iframe Hc1 Hc2

/-- `s.revMu`'s part gives a lower bound of the compaction revision (D2: `syncWatchers` mints one
under `s.revMu`). -/
theorem revMuAbs_crevLb (a : AbsNames) (q : Qp) (L : Log) (c : Int) :
    revMuAbs (GF := GF) a q L c ⊢ revMuAbs a q L c ∗ crevAtLeast a c := by
  unfold revMuAbs crevAuth crevAtLeast
  iintro ⟨Ha, Hc⟩
  ihave #Hlb := monoNatLbOwn_get a.crevLb _ _ $$ Hc
  iframe Ha Hc Hlb

/-- **The writer's part of the API's ghost state** at its log (§1): a quarter of the view, at some
compaction revision, and its part `pw` of the pending revision, at `none` (while checked in). -/
def writerAbs (a : AbsNames) (pw : Qp) (L : Log) : IProp GF :=
  iprop(∃ c : Int, absPart a (1 : Qp).half.half L c ∗ pndPart a pw none)

/-- **The client's parts of a new store's API ghost state** (`absNames_alloc_store`'s, which `NewStore`
returns since M3, 2026-11-06): half the view, the pending revision's part `pr`, half and a quarter (the
compaction right's) of the compaction authority and its lower bound, the whole share token, the
notified log's authority and the store's location. -/
def newClient (a : AbsNames) (L : Log) (c : Int) (pr : Qp) (l : Loc) : IProp GF :=
  iprop(absPart a (1 : Qp).half L c ∗ pndPart a pr none ∗ crevAuth a (1 : Qp).half c ∗
    crevAuth a (1 : Qp).half.half c ∗ crevAtLeast a c ∗ shareTok a 1 ∗ nlAuth a 1 L ∗ locIs a l)

/-- **A new store's API ghost state, split as §1 gives** (strict M1, 2026-11-04: `NewStore`): the
lock's slot (`revMuAbs` at the whole lock), the writer's (`writerAbs` at its part `pw` of the
pending revision), the frozen flag down; and the client's parts (half the view, the pending
revision's rest `pr`, half the compaction authority and its lower bound, the whole share token)
and the compaction right's quarter of the authority. -/
theorem absNames_alloc_store (L : Log) (c : Int) (pw pr : Qp) (hp : pw + pr = 1) (l : Loc) :
    ⊢ |==> ∃ a : AbsNames, revMuAbs (GF := GF) a 1 L c ∗
      (absPart a (1 : Qp).half.half L c ∗ pndPart a pw none) ∗ ghostVar a.frz 1 false ∗
      absPart a (1 : Qp).half L c ∗ pndPart a pr none ∗ crevAuth a (1 : Qp).half c ∗
      crevAuth a (1 : Qp).half.half c ∗ crevAtLeast a c ∗ shareTok a 1 ∗ nlAuth a 1 L ∗
      locIs a l := by
  iintro
  imod absNames_alloc (GF := GF) L c none L l with ⟨%a, Ha, Hp, Hc, #Hlb, Ht, Hf, Hn, #Hl⟩
  have ha1 := (absPart_fractional (GF := GF) a L c).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at ha1
  icases ha1.1 $$ Ha with ⟨Ha1, Ha2⟩
  have ha2 := (absPart_fractional (GF := GF) a L c).fractional (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at ha2
  icases ha2.1 $$ Ha2 with ⟨Ha3, Ha4⟩
  have hc1 := (crevAuth_fractional (GF := GF) a c).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hc1
  icases hc1.1 $$ Hc with ⟨Hc1, Hc2⟩
  have hc2 := (crevAuth_fractional (GF := GF) a c).fractional (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at hc2
  icases hc2.1 $$ Hc2 with ⟨Hc3, Hc4⟩
  have hp' := (pndPart_fractional (GF := GF) a none).fractional pw pr
  rw [hp] at hp'
  icases hp'.1 $$ Hp with ⟨Hpw, Hpr⟩
  imodintro
  iexists a
  iframe Hf Ha1 Hpr Hc1 Hc4 Ht Hlb Hn Hl
  isplitl [Ha3 Hc3]
  · iunfold revMuAbs; iframe Ha3 Hc3
  · iframe Ha4 Hpw

end ghost

end api
end mvcc
end EtcdGrove
end Perennial
