/-
**What a registered watcher's authorization says** (the auth plan's A4, 2026-10-24;
`notes/decisions.md`, "A4 of the auth plan"). Lean-first (no Rocq counterpart).

`recvLoop` checks a create request (`isWatchPermitted`: `IsRangePermitted` of the request's key,
normalized, and its range end as given) before it rewrites the range end for mvcc and registers
the watcher, and a created response's description (`ctrlWatcher`) carries the check's class
(`watchAuthed`: `apply.watchClass` in the mode the store's owner tag names). This file turns that
into the statement over the watcher's range: **every key the registered watcher covers**
(`mvcc.WatchRange.covers`) **is in the interval the check saw** (`createRangeOk_inRange`: the
interval the check saw is the interval mvcc registers, for every request shape -- a point, a
proper range, `WithFromKey`'s `"\x00"` end, the empty key; what GHSA-xg4h-6gfc-h4m8 broke was the
order of the check and the rewrite, which this lemma would not survive), so that in the mode
`on γa` a recorded state permitted the read of every covered key to the principal the check saw
(`ctrlWatcher_authorized`): auth disabled at that state, or the principal a user with the root
role, or one whose roles' permissions of type READ cover each covered key.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatchStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode

/-! ## The interval the check saw covers the registered range (pure) -/

theorem goEmpty_eq : (go!"" : GoString) = [] := rfl

/-- `k ≤ x` (Go's order) from `¬ affLt x k` for a non-empty `x`. -/
theorem goStringLe_of_not_affLt {k x : GoString} (hx : x ≠ []) (h : ¬ adt.affLt x k) :
    go.GoStringLe k x := by
  unfold adt.affLt at h
  rw [goEmpty_eq] at h
  by_cases hlt : go.GoStringLt k x
  · exact Or.inr hlt
  · left
    apply go.goStringLt_eq_of_not_lt hlt
    intro hxk
    apply h
    exact ⟨hx, Or.inr hxk⟩

/-- **Every key the registered watcher covers is in the interval the check saw**: the range
`r` a create request `c` registers (`createRangeOk`) covers only keys of `[watchKey c.key,
c.rangeEnd)` in the model's sense (`auth.inRange`: the point, from the key on for `"\x00"`, the
range otherwise). -/
theorem createRangeOk_inRange (c : CreateReqM) (id : w64) (r : mvcc.WatchRange) (x : GoString)
    (h : createRangeOk c id r) (hx : r.covers x = true) :
    auth.inRange (apply.watchKey c.key) c.rangeEnd x := by
  unfold createRangeOk at h
  obtain ⟨hk, -, -, he⟩ := h
  have hk' : r.key = apply.watchKey c.key := hk
  unfold mvcc.WatchRange.covers at hx
  unfold auth.inRange
  by_cases h1 : c.rangeEnd = []
  · simp only [h1, ↓reduceIte] at he ⊢
    rw [he] at hx
    simp only [decide_eq_true_eq] at hx
    rw [hx, hk']
  · simp only [h1, ↓reduceIte]
    cases he' : r.end? with
    | none =>
      rw [he'] at hx he
      simp only [decide_eq_true_eq] at hx
      rcases Classical.em (c.rangeEnd = [W8 0]) with h2 | h2
      · rw [hx, hk']
        exact ⟨Or.inl rfl, Or.inl (by rw [h2]; rfl)⟩
      · simp only [h1, h2, ↓reduceIte] at he
        cases he
    | some e =>
      rw [he'] at hx he
      simp only [decide_eq_true_eq] at hx
      obtain ⟨hge, hlt⟩ := hx
      have hlt' := (adt.affCmp_neg_iff x e).1 hlt
      have hge' := (adt.affCmp_nonneg_iff x r.key).1 hge
      have hxne : x ≠ [] := by
        have := hlt'.1
        rwa [goEmpty_eq] at this
      refine ⟨by rw [← hk']; exact goStringLe_of_not_affLt hxne hge', ?_⟩
      by_cases h2 : c.rangeEnd = [W8 0]
      · left; rw [h2]; rfl
      · right
        simp only [h1, h2, ↓reduceIte, Option.some.injEq] at he
        subst he
        rcases hlt'.2 with h3 | h3
        · exact absurd (by rw [goEmpty_eq] at h3; exact h3) h1
        · exact h3

/-- **A permitted request's principal may read every key its watcher covers**, at the state
that permitted it: auth disabled there, or the principal (with a non-zero revision) a user with
the root role, or one whose roles' permissions of type READ cover each key the watcher covers. -/
theorem watch_permitted_covers (st : auth.AuthState) (ai : auth.AuthInfoM) (c : CreateReqM)
    (id : w64) (r : mvcc.WatchRange)
    (hp : auth.permitted st ai (apply.watchKey c.key) c.rangeEnd .read)
    (hs : auth.reqShape (apply.watchKey c.key) c.rangeEnd)
    (hr : createRangeOk c id r) :
    st.enabled = false ∨
      (ai.rev ≠ 0 ∧ ∃ u, st.users !! ai.user = some u ∧
        (auth.isRoot u ∨ ∀ x, r.covers x = true →
          ∃ p ∈ auth.userPerms st u, p.covers .read x)) := by
  unfold auth.permitted auth.granted at hp
  rcases hp with hp | ⟨hrev, u, hu, hroot | hcov⟩
  · exact Or.inl hp
  · exact Or.inr ⟨hrev, u, hu, Or.inl hroot⟩
  · right
    refine ⟨hrev, u, hu, Or.inr ?_⟩
    intro x hx
    have hin := createRangeOk_inRange c id r x hr hx
    have hc := hcov hs
    unfold auth.covers at hc
    by_cases h1 : c.rangeEnd = []
    · simp only [h1, ↓reduceIte] at hc
      unfold auth.inRange at hin
      simp only [h1, ↓reduceIte] at hin
      subst hin
      exact hc
    · simp only [h1, ↓reduceIte] at hc
      exact hc x hin

/-! ## The authorization of a created response, in the mode `on γa` -/

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- In the mode `on γa` (the server's, by the store's tag), a registered watcher's authorization
names a recorded state that permitted the request's read to some principal. -/
theorem watchAuthed_on (γ : mvcc.WsNames) (γa : auth.AuthNames) (c : CreateReqM) :
    ⊢ auth.modeTag (GF := GF) γ.tag (.on γa) -∗ watchAuthed γ c -∗
      ∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (i : Nat) (st : auth.AuthState),
        auth.authStateAt γa i st ∗
        ⌜auth.permitted st (auth.authInfoM info) (apply.watchKey c.key) c.rangeEnd .read ∧
          auth.reqShape (apply.watchKey c.key) c.rangeEnd⌝ := by
  iintro #Htag H
  iunfold watchAuthed at H
  icases H with ⟨%M, %info, #Htag', #Hcl, %Hs⟩
  ihave %HM := auth.modeTag_agree γ.tag (.on γa) M $$ Htag Htag'
  subst HM
  ihave ⟨%i, %st, #Hst, %Hp⟩ := apply.watchClass_on γa info c.key c.rangeEnd $$ Hcl
  iexists info, i, st
  iframe #
  ipureintro
  exact ⟨Hp, Hs⟩

/-- **A created response's watcher was authorized** (the auth plan's A4, the `Watch` row of
`notes/auth-matrix.md`): in the mode `on γa`, for the mvcc watcher `w` of range `r` a created,
not canceled, response `m` to the create request `c` names (`ctrlWatcher`), some principal
`info` (the stream's context's auth info, or the empty one) and a recorded state `st` at which
auth was disabled, or `info` named a user with the root role, or one whose READ permissions
covered every key `r` covers. -/
theorem ctrlWatcher_authorized (γ : mvcc.WsNames) (γo : mvcc.WsStreamNames)
    (γa : auth.AuthNames) (c : CreateReqM) (m : WatchRespM) (h : m.canceled = false) :
    auth.modeTag (GF := GF) γ.tag (.on γa) ∗ ctrlWatcher γ γo (.create c) m ⊢
      ∃ (w : Loc) (r : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (i : Nat) (st : auth.AuthState),
        ⌜createRangeOk c m.watchId r⌝ ∗ mvcc.watcherIs γ w r fcs lo ∗
        mvcc.idAssigned γo m.watchId w ∗ auth.authStateAt γa i st ∗
        ⌜st.enabled = false ∨
          ((auth.authInfoM info).rev ≠ 0 ∧
            ∃ u, st.users !! (auth.authInfoM info).user = some u ∧
              (auth.isRoot u ∨ ∀ x, r.covers x = true →
                ∃ p ∈ auth.userPerms st u, p.covers .read x))⌝ := by
  iintro ⟨#Htag, H⟩
  unfold ctrlWatcher
  rw [h]
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases H with ⟨%w, %rg, %fcs, %lo, %Hrg, #Hwi, -, -, #Hia, -, #Hau, -⟩
  ihave ⟨%info, %i, %st, #Hst, %Hp, %Hs⟩ := watchAuthed_on γ γa c $$ Htag Hau
  iexists w, rg, fcs, lo, info, i, st
  iframe #
  ipureintro
  exact ⟨Hrg, watch_permitted_covers st (auth.authInfoM info) c m.watchId rg Hp Hs Hrg⟩

end iris

end v3rpc
end EtcdGrove
end Perennial
