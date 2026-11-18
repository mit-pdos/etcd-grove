/-
Lean-first (no Rocq counterpart).

# The bridge to Kubernetes' checker, B4: the replay's checks (k8s 7g step 4)

`notes/k8s-7g-scope.md` §2.3, B4. A unary operation answered at the driver's configuration `h` (its output
`kstepL`'s at `h`, its real answer what the output encodes) passes `Replay.Validate` on any replay that agrees
with `h` (`ReplayAt`, B3b): a write passes; a stale get finds the state at `h`'s revision, whose `get` is its
answer; an `Exact` list finds the state at the requested revision (at least the seed's: the floor), a
`NotOlderThan` one the state at `h`'s revision, and the checker's list there is its answer (B1-list's
`rlistL_eq_rawRel`).

- `HistCfgOk h`: a configuration's history fits it (`hlen`, `hlast`) and its stores are as B1 needs;
- `rgetL_absR`, `rlistL_eq_rawRel`: the checker's get and list on a store's abstraction are the real answer;
- **`rvalidateL_point`**.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealLin
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealReplay

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-- **A configuration's history, as B4 needs it**: one store per revision, the last the current one, and
each store sorted, unannotated and with objects `encodeItems` is injective on. -/
def HistCfgOk (h : HSt) : Prop :=
  h.hist.length = uint.nat h.st.rv ∧ h.hist.getLast? = some h.st ∧
    ∀ q : w64, 0 < uint.nat q → uint.nat q ≤ uint.nat h.st.rv →
      StOk (histAtL h.hist q) ∧ ∀ it ∈ (histAtL h.hist q).items, itemOk it.obj'

/-- **The floor** (departure D7g-1): a requested resource version is `0` or at least the seed's. -/
def FloorOk (s0 : w64) (x : Input) : Prop :=
  ∀ q, parseRVD x.MinRV' = some q → q = 0 ∨ uint.nat s0 ≤ uint.nat q

/-- The checker's list on a store's abstraction is the real answer the driver's list there encodes. -/
theorem rlistL_eq_rawRel (x : Input) (st : GSt) (p : GoString) (c : RCons) (rq : w64) (r : RResp)
    (h4 : x.Kind' = W64 4) (hp : k8s.prepareKeyM [] x.ListKey' x.Recursive' = some p)
    (hc : listConsL x = some (c, rq)) (hle : ¬ uint.nat st.rv < uint.nat rq) (hst : StOk st)
    (hio : ∀ it ∈ st.items, itemOk it.obj')
    (hrel : RawRel x (listOutL x st (listLoopL x st.items) p) r) :
    rlistL x (absR st) = r := by
  obtain ⟨its, hio', hits, hr⟩ := rawRel_listOutL x st p r h4 hrel
  have hii : its = (listLoopL x st.items).items.reverse := by
    apply encItemsL_inj _ _ hio' _ hits
    intro o ho
    obtain ⟨-, -, -, h4'⟩ := listLoopL_inv x st.items p [] hp
    obtain ⟨it, hit, rfl⟩ := h4' o (List.mem_reverse.1 ho)
    exact hio it hit
  subst hii
  rw [rlistL_cur x st p c rq hp hc hle hst.1, hr]

/-- The checker's get on a store's abstraction is the real answer the driver's get there encodes (below
the store's revision). -/
theorem rgetL_absR (x : Input) (st : GSt) (r : RResp) (req : w64) (h4 : x.Kind' ≠ W64 4)
    (hk : keyOkL (storeKeyL x.Key') = true) (hst : StOk st) (hp : parseRVD x.MinRV' = some req)
    (hle : ¬ uint.nat st.rv < uint.nat req) (hrel : RawRel x (mgetL x st) r) :
    rgetL x (absR st) = r := by
  unfold mgetL at hrel
  rw [hp] at hrel
  simp only at hrel
  rw [if_neg hle] at hrel
  unfold rgetL
  simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hp]
  rw [if_neg (show ¬ uint.nat (absR st).rv < uint.nat req from hle), absR_items]
  by_cases hf : (lookupL st.items x.Key').2 = true
  · have ha := lookupL_ann st hst x.Key' hf
    simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
    simp only [RawRel, objOutL, h4, if_true, if_false] at hrel
    subst hrel
    have e := objOfL_objOutL _ ha; simp only [objOutL] at e; rw [e]
  · have hf' : (lookupL st.items x.Key').2 = false := by simpa using hf
    simp only [hf', Bool.not_false, ↓reduceIte] at hrel ⊢
    cases hig : x.IgnoreNotFound'
    · simp only [hig, Bool.false_eq_true, ↓reduceIte] at hrel ⊢
      simp [RawRel, notFoundL, errOutL] at hrel
      subst hrel
      rfl
    · simp only [hig, ↓reduceIte] at hrel ⊢
      simp only [RawRel, zeroOutL, errOutL, h4, ↓reduceIte, if_true, if_false] at hrel
      subst hrel
      rfl

theorem respEqL_self (r : RResp) (d : DeepV) (h : r.err = .deep d) : respEqL r r = true := by
  unfold respEqL; rw [h]; simp

/-- A list answer's shape: a list at the store's revision, no error. -/
theorem rawRel_listOutL_shape (x : Input) (st : GSt) (p : GoString) (r : RResp) (h4 : x.Kind' = W64 4)
    (hrel : RawRel x (listOutL x st (listLoopL x st.items) p) r) :
    ∃ its c rem, r = ⟨.list (some its) st.rv c rem, .none⟩ := by
  obtain ⟨its, -, -, hr⟩ := rawRel_listOutL x st p r h4 hrel
  split at hr <;> exact ⟨its, _, _, hr⟩

/-- `Replay.validateList`'s check at a state the replay has at the answer's revision. -/
theorem rreplayListL_at (R : RReplay) (x : Input) (st : GSt) (p : GoString) (c : RCons) (rq : w64)
    (r : RResp) (h4 : x.Kind' = W64 4) (hp : k8s.prepareKeyM [] x.ListKey' x.Recursive' = some p)
    (hc : listConsL x = some (c, rq)) (hcne : c ≠ .consistent) (hle : ¬ uint.nat st.rv < uint.nat rq)
    (hst : StOk st) (hio : ∀ it ∈ st.items, itemOk it.obj')
    (hrel : RawRel x (listOutL x st (listLoopL x st.items) p) r)
    (hR : R.states !! st.rv = some (absR st)) :
    rreplayListL R x r = true := by
  obtain ⟨its, cc, rem, hr⟩ := rawRel_listOutL_shape x st p r h4 hrel
  have heq := rlistL_eq_rawRel x st p c rq r h4 hp hc hle hst hio hrel
  unfold rreplayListL
  rw [hr]
  simp only [errNonNil, Bool.false_eq_true, ↓reduceIte, hc]
  cases c with
  | consistent => exact absurd rfl hcne
  | exact | notOlderThan =>
    simp only [hR]
    unfold equalListRespL
    rw [heq, hr]; simp [respEqL, absR_rv]

/-- **B4, one operation**: a unary operation answered at the driver's configuration `h` passes
`Replay.Validate` on a replay that agrees with `h` from the seed's revision `s0` on. -/
theorem rvalidateL_point (s0 : w64) (R : RReplay) (h : HSt) (x : Input) (y : Output) (r : RResp)
    (hk5 : x.Kind' ≠ W64 5) (hop : OpOk (x, y, r)) (hcfg : CfgOk h) (hhc : HistCfgOk h)
    (hR : ReplayAt s0 R h) (hs0 : uint.nat s0 ≤ uint.nat h.st.rv) (hfl : FloorOk s0 x)
    (hy : y = (kstepL x h).2) :
    rvalidateL R x r = true := by
  obtain ⟨-, hop⟩ := hop
  obtain ⟨hrel, hlist, hkey⟩ := hop hk5
  obtain ⟨hst, hio, hwf, hpos, hhist⟩ := hcfg
  obtain ⟨hlen, hlast, hhs⟩ := hhc
  simp only at hrel hlist hkey
  have hcur : histAtL h.hist h.st.rv = h.st := histAtL_last _ _ _ hlen hlast
  have hRcur : R.states !! h.st.rv = some (absR h.st) := by
    rw [hR.1 h.st.rv hs0 (Nat.le_refl _), hcur]
  unfold rvalidateL
  by_cases h4 : x.Kind' = W64 4
  · rw [if_pos h4]
    obtain ⟨hm, hcons, hkp⟩ := hlist h4
    have hks : kstepL x h = (h, mlistL x h) := by unfold kstepL; rw [if_pos h4]
    rw [hks] at hy
    subst hy
    obtain ⟨⟨c, rq⟩, hc⟩ := Option.isSome_iff_exists.1 hcons
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hkp
    have hparse := listConsL_parse x c rq hc
    obtain ⟨hpast, hex0⟩ := listConsL_past x c rq hm hc
    unfold mlistL at hrel
    rw [hparse] at hrel
    simp only at hrel
    by_cases hlt : uint.nat h.st.rv < uint.nat rq
    · rw [if_pos hlt] at hrel
      simp [RawRel, tooLargeL, errOutL] at hrel
      subst hrel
      simp [rreplayListL, errNonNil, tooLargeE]
    rw [if_neg hlt] at hrel
    cases hpo : k8s.prepareKeyM go!"/objs" x.ListKey' x.Recursive' with
    | none => rw [hpo] at hrel; simp [RawRel, otherL, errOutL] at hrel
    | some p' =>
      rw [hpo] at hrel; simp only at hrel
      have hpp : p = p' := by
        have e := prepareKeyM_nil hpo; rw [hp] at e; exact Option.some.inj e
      subst hpp
      cases c with
      | consistent =>
        unfold rreplayListL
        rw [hc]
        cases errNonNil r.err <;> rfl
      | exact =>
        have hrq0 := hex0 rfl
        have hpr : pastReadL x rq = true := hpast.2 rfl
        unfold listStL at hrel
        rw [if_pos hpr] at hrel
        have hrq : 0 < uint.nat rq := by
          rcases Nat.eq_zero_or_pos (uint.nat rq) with e | e
          · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using e) hrq0
          · exact e
        have hrv : (histAtL h.hist rq).rv = rq := hhist rq hrq (Nat.le_of_not_lt hlt)
        have hsq : uint.nat s0 ≤ uint.nat rq := by
          rcases hfl rq hparse with e | e
          · exact absurd e hrq0
          · exact e
        obtain ⟨hst', hio'⟩ := hhs rq hrq (Nat.le_of_not_lt hlt)
        apply rreplayListL_at R x _ p .exact rq r h4 hp hc (by simp) (by rw [hrv]; omega) hst' hio' hrel
        rw [hrv, hR.1 rq hsq (Nat.le_of_not_lt hlt)]
      | notOlderThan =>
        have hpr : pastReadL x rq = false := by
          cases e : pastReadL x rq
          · rfl
          · cases hpast.1 e
        unfold listStL at hrel
        rw [if_neg (by simp [hpr])] at hrel
        exact rreplayListL_at R x _ p .notOlderThan rq r h4 hp hc (by simp) hlt hst hio hrel hRcur
  · rw [if_neg h4]
    by_cases hw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2
    · rw [if_pos hw]
    rw [if_neg hw]
    rw [kstepL_get x h hw h4] at hy
    subst hy
    unfold rreplayGetL
    by_cases hmv : x.MinRV' = []
    · rw [if_pos hmv]
    rw [if_neg hmv]
    cases hp : parseRVD x.MinRV' with
    | none => rfl
    | some req =>
      simp only
      by_cases hlt : uint.nat h.st.rv < uint.nat req
      · unfold mgetL at hrel
        rw [hp] at hrel
        simp only [hlt, if_true] at hrel
        simp [RawRel, tooLargeL, errOutL] at hrel
        subst hrel
        simp [isTooLargeE, tooLargeE]
      have heq := rgetL_absR x h.st r req h4 (hkey h4) hst hp hlt hrel
      have hmem : (h.st.rv, absR h.st) ∈ R.states.toList := (GMap.mem_toList _ _ _).2 hRcur
      have hself : respEqL (rgetL x (absR h.st)) r = true := by
        rw [heq]
        rw [← heq]
        unfold rgetL
        simp only [hkey h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hp]
        rw [if_neg (show ¬ uint.nat (absR h.st).rv < uint.nat req from hlt)]
        split
        · split
          · exact respEqL_self _ .nil rfl
          · exact respEqL_self _ _ rfl
        · exact respEqL_self _ .nil rfl
      apply Bool.or_eq_true_iff.2 (Or.inr _)
      apply List.any_eq_true.2
      refine ⟨_, hmem, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
      exact ⟨Nat.le_of_not_lt hlt, Or.inl hself⟩

end go

end k8s_correctness
end EtcdGrove
end Perennial
