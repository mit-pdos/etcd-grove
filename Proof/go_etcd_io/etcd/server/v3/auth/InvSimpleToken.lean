/-
The simple token provider (`server/auth/simple_token.go`; pr-verify etcd#22560, 2026-10-16): its
lock, what the lock holds, and who may write what. Lean-first (no Rocq counterpart).

**The provider** `t` (a `*tokenSimple`; `isTS t γ γk`, persistent):
- `lg`, `indexWaiter`: read-only;
- `simpleTokensMu` (a `sync.Mutex`) guards (`stLockP`) the token table `simpleTokens` (token ->
  user), the PR's `expiredTokens` (the tokens the TTL keeper has expired: token -> user), the TTL
  `simpleTokenTTL` (written by `enable`), half of `simpleTokenKeeper` and every keeper's own
  `tokens` map (deadlines; a keeper's goroutine sweeps it under `tm.mu`, which is
  `&t.simpleTokensMu`, until `stop` returns, also after `disable` has dropped the keeper);
- the other half of `simpleTokenKeeper` is the **admin's** (`tsAdmin`): `enable`, `disable` and
  `invalidateUser` read the field without the lock (`invalidateUser`'s first line) or write it
  (under the lock, with both halves). In etcd the admin is the apply goroutine: `AuthEnable`,
  `AuthDisable`, `UserDelete`, `UserChangePassword`, `Authenticate` (`assign`) and `Recover` all
  run there (and `NewAuthStore`, before it starts).

**The ghost table** `γ` (a `ghostVar` of a map token -> user, halves in the lock and in
`tsAdmin`): the tokens the admin allows, `A`. The admin adds a token on `assign`, removes a
user's on `invalidateUser`, empties it on `disable`; the invariant is that both maps are below
`A` (`live ⊆ A`, `expired ⊆ A`). So what `renew` can accept (a token of either map) was assigned
and neither invalidated nor disabled since; the TTL is not part of it (the keeper only moves
tokens from `simpleTokens` to `expiredTokens`, or drops them).

**The keepers** (`γk`, a ghost map of every keeper ever created, with persistent elements): each
one's `tokens` map is in the lock (`keeperMap`), the current one's read-only fields in the lock too
(`keeperRO`): `mu = &t.simpleTokensMu`, its channels, `simpleTokenTTL` and `deleteTokenFunc`,
`enable`'s closure `delf`, whose contract `delfOk` is the PR's change to the keeper: it keeps the
tables below `A`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Perennial.Proof.time
public import Perennial.Golang.Theory.Chan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section fields
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&t.<f>` (a `*tokenSimple`) -/
abbrev tF (f : GoString) (t : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.auth.tokenSimple f t

/-- `&tm.<f>` (a `*simpleTokenTTLKeeper`) -/
abbrev kF (f : GoString) (k : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper f k

/-- `&t.simpleTokensMu` -/
abbrev tMu (t : Loc) : Loc := tF go!"simpleTokensMu" t

end fields

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The two token maps, both below the allowed table `A`. -/
def stTables (t : Loc) (A : GMap GoString GoString) : IProp GF :=
  iprop(∃ (sp ep : GoMap) (live exp : GMap GoString GoString),
    tF go!"simpleTokens" t ↦ sp ∗ sp ↦$ live ∗ tF go!"expiredTokens" t ↦ ep ∗ ep ↦$ exp ∗
    ⌜live ⊆ A ∧ exp ⊆ A⌝)

/-- **The keeper's callback** `f` (`enable`'s `delf`): called with the lock held on a token, it
keeps the tables below any `A`. -/
def delfOk (t : Loc) (f : GoFunc) : IProp GF :=
  iprop(□ (∀ (A : GMap GoString GoString) (tk : GoString),
    {{ stTables t A }} (App (Val #f) (Val #tk)) {{ RET #(); stTables t A }}))

instance delfOk_persistent (t : Loc) (f : GoFunc) : Persistent (delfOk (GF := GF) t f) := by
  unfold delfOk; infer_instance

/-- A keeper's deadlines (in the lock). -/
def keeperMap (k : Loc) : IProp GF :=
  iprop(∃ (m : GoMap) (M : GMap GoString time.Time), kF go!"tokens" k ↦ m ∗ m ↦$ M)

/-- A keeper's read-only fields: its lock is `t`'s, its callback `delfOk`, its two unbuffered
`chan struct{}`s. -/
def keeperRO (t k : Loc) : IProp GF :=
  iprop(⌜k ≠ null⌝ ∗ kF go!"mu" k ↦□ tMu t ∗
    (∃ f : GoFunc, kF go!"deleteTokenFunc" k ↦□ f ∗ delfOk t f) ∗
    (∃ d : time.Duration, kF go!"simpleTokenTTL" k ↦□ d) ∗
    (∃ (c : Loc) (γc : ChanNames), kF go!"donec" k ↦□ c ∗ isChan c γc Unit) ∗
    (∃ (c : Loc) (γc : ChanNames), kF go!"stopc" k ↦□ c ∗ isChan c γc Unit))

instance keeperRO_persistent (t k : Loc) : Persistent (keeperRO (GF := GF) t k) := by
  unfold keeperRO; infer_instance

/-- A keeper's two channels, as `make(chan struct{})` returns them (the keeper's goroutine gets
them). -/
def keeperChans (k : Loc) : IProp GF :=
  iprop((∃ (c : Loc) (γc : ChanNames), kF go!"donec" k ↦□ c ∗ isChan c γc Unit ∗
      ownChan γc Unit ChanState.Idle) ∗
    (∃ (c : Loc) (γc : ChanNames), kF go!"stopc" k ↦□ c ∗ isChan c γc Unit ∗
      ownChan γc Unit ChanState.Idle))

/-- **What `simpleTokensMu` guards.** -/
def stLockP (t : Loc) (γ γk : GName) : IProp GF :=
  iprop(∃ (kp : Loc) (A : GMap GoString GoString) (K : GMap Loc Unit) (ttl : time.Duration),
    tF go!"simpleTokenKeeper" t ↦{DFrac.own (1 : Qp).half} kp ∗ ghostVar γ (1 : Qp).half A ∗
    stTables t A ∗ tF go!"simpleTokenTTL" t ↦ ttl ∗
    ghostMapAuth γk 1 K ∗ ([∗map] k ↦ _u ∈ K, k ↪[γk]□ ()) ∗ ([∗map] k ↦ _u ∈ K, keeperMap k) ∗
    (⌜kp = null⌝ ∨ ⌜K !! kp = some ()⌝ ∗ keeperRO t kp))

/-- **The provider** `t` (persistent). -/
def isTS (t : Loc) (γ γk : GName) : IProp GF :=
  iprop(⌜t ≠ null⌝ ∗ (∃ lg : Loc, tF go!"lg" t ↦□ lg ∗ ⌜lg ≠ null⌝) ∗
    sync.isMutex (tMu t) (stLockP t γ γk))

instance isTS_persistent (t : Loc) (γ γk : GName) : Persistent (isTS (GF := GF) t γ γk) := by
  unfold isTS; infer_instance

/-- **The admin's share**: the other half of `simpleTokenKeeper` (`kp`) and of the allowed table
(`A`). -/
def tsAdmin (t : Loc) (γ : GName) (A : GMap GoString GoString) (kp : Loc) : IProp GF :=
  iprop(tF go!"simpleTokenKeeper" t ↦{DFrac.own (1 : Qp).half} kp ∗ ghostVar γ (1 : Qp).half A)

/-- `err` is the error variable `g` (`errors.New`, read-only). -/
def errVarIs (g : GoString) (err : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝)

instance errVarIs_persistent (g : GoString) (err : GoInterface) :
    Persistent (errVarIs (GF := GF) g err) := by
  unfold errVarIs; infer_instance

/-- A whole typed points-to is two halves (the admin's and the lock's `simpleTokenKeeper`). -/
theorem ts_ptsto_halves {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    (l ↦ v : IProp GF) ⊣⊢
      l ↦{DFrac.own (1 : Qp).half} v ∗ l ↦{DFrac.own (1 : Qp).half} v := by
  have h : (DFrac.own 1 : DFrac) = DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half := by
    rw [DFrac.op_own, Qp.half_add_half]
  rw [h]
  exact (typedPointsto_dfractional (GF := GF) l v).dfractional _ _

/-- A new keeper joins the keepers (`enable`): its deadline map goes in the lock, and it gets its
persistent membership. (A keeper already there keeps its slot; the new map is dropped: it is the
same location, whose points-to the lock already holds.) -/
theorem keepers_join (γk : GName) (K : GMap Loc Unit) (k : Loc) :
    ⊢ ghostMapAuth (GF := GF) γk 1 K -∗ ([∗map] k ↦ _u ∈ K, k ↪[γk]□ ()) -∗
      ([∗map] k ↦ _u ∈ K, keeperMap (GF := GF) k) -∗ keeperMap k ==∗
      ∃ K' : GMap Loc Unit, ghostMapAuth γk 1 K' ∗ ([∗map] k ↦ _u ∈ K', k ↪[γk]□ ()) ∗
        ([∗map] k ↦ _u ∈ K', keeperMap k) ∗ ⌜K' !! k = some ()⌝ ∗ k ↪[γk]□ () := by
  iintro HK #HKe HKm Hk
  cases hK : K !! k with
  | some u =>
    ihave #Hel := BigSepM.bigSepM_lookup (Φ := fun k (_ : Unit) => iprop(k ↪[γk]□ () : IProp GF))
      hK $$ HKe
    imodintro
    iexists K
    iframe
    iframe HKe Hel
    ipureintro; cases u; exact hK
  | none =>
    imod ghost_map_insert_persist k () hK $$ HK with ⟨HK, #Hel⟩
    imodintro
    iexists GMap.insert k () K
    iframe HK Hel
    isplitr
    · iapply (BigSepM.bigSepM_insert (Φ := fun k (_ : Unit) => iprop(k ↪[γk]□ () : IProp GF)) hK).2
      iframe HKe Hel
    isplitl
    · iapply (BigSepM.bigSepM_insert (Φ := fun k (_ : Unit) => keeperMap (GF := GF) k) hK).2
      iframe
    · ipureintro; exact GMap.lookup_insert _ _ _

end defs

/-! ### Pure facts about the table -/

theorem subseteq_insert_insert {K V : Type} [DecidableEq K] {m A : GMap K V} (k : K) (v : V)
    (h : m ⊆ A) : GMap.insert k v m ⊆ GMap.insert k v A := by
  intro k' v' hk
  by_cases hkk : k = k'
  · subst hkk; simpa [GMap.lookup_insert] using hk
  · rw [GMap.lookup_insert_ne _ _ hkk] at hk ⊢; exact h k' v' hk

theorem subseteq_delete_insert {K V : Type} [DecidableEq K] {m A : GMap K V} (k : K) (v : V)
    (h : m ⊆ A) : GMap.delete k m ⊆ GMap.insert k v A := by
  intro k' v' hk
  by_cases hkk : k = k'
  · subst hkk; simp at hk
  · rw [GMap.lookup_delete_ne _ hkk] at hk; rw [GMap.lookup_insert_ne _ _ hkk]; exact h k' v' hk

theorem subseteq_delete {K V : Type} [DecidableEq K] {m A : GMap K V} (k : K)
    (h : m ⊆ A) : GMap.delete k m ⊆ A := by
  intro k' v' hk
  by_cases hkk : k = k'
  · subst hkk; simp at hk
  · rw [GMap.lookup_delete_ne _ hkk] at hk; exact h k' v' hk

theorem subseteq_empty {K V : Type} [DecidableEq K] (A : GMap K V) : (∅ : GMap K V) ⊆ A := by
  intro k v hk; simp at hk

/-- What `renew` accepts is allowed: a token of either map is in `A`. -/
theorem renewable_allowed {K V : Type} [DecidableEq K] {live exp A : GMap K V} {k : K} {v : V}
    (hl : live ⊆ A) (he : exp ⊆ A) (h : live !! k = some v ∨ exp !! k = some v) :
    A !! k = some v := by
  rcases h with h | h
  · exact hl k v h
  · exact he k v h

/-! ### `invalidateUser`'s loops: no visited key keeps the user -/

/-- The loop invariant of `invalidateUser`'s two loops: no key among the first `i` maps to `u`. -/
def noUserBelow {V : Type} (keys : List GoString) (i : Nat) (m : GMap GoString V) (u : V) : Prop :=
  ∀ (j : Nat) (k : GoString), j < i → keys[j]? = some k → m !! k ≠ some u

theorem noUserBelow_zero {V : Type} (keys : List GoString) (m : GMap GoString V) (u : V) :
    noUserBelow keys 0 m u := fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)

/-- The body deleted the `i`-th key (its value was `u`). -/
theorem noUserBelow_delete {V : Type} (keys : List GoString) (i : Nat)
    (key : GoString) (m : GMap GoString V) (u : V) (hk : keys[i]? = some key)
    (H : noUserBelow keys i m u) : noUserBelow keys (i + 1) (GMap.delete key m) u := by
  intro j k hj hkj
  by_cases hjk : k = key
  · subst hjk; simp
  · rw [GMap.lookup_delete_ne _ (Ne.symm hjk)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact H j k hj hkj
    · subst hj; rw [hk] at hkj; cases hkj; exact absurd rfl hjk

/-- The body kept the `i`-th key (its value `v` is not `u`). -/
theorem noUserBelow_keep {V : Type} (keys : List GoString) (i : Nat)
    (key : GoString) (m : GMap GoString V) (u v : V) (hk : keys[i]? = some key)
    (hv : m !! key = some v) (hvu : v ≠ u)
    (H : noUserBelow keys i m u) : noUserBelow keys (i + 1) m u := by
  intro j k hj hkj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · exact H j k hj hkj
  · subst hj; rw [hk] at hkj; cases hkj; rw [hv]; intro h; cases h; exact hvu rfl

/-- At the end of the loop over `m0`'s keys, the map (below `m0`) has no key mapping to `u`. -/
theorem noUserBelow_end {V : Type} (keys : List GoString) (m0 m : GMap GoString V) (u : V)
    (hmem : ∀ k, k ∈ keys ↔ (m0 !! k).isSome) (hsub : m ⊆ m0)
    (H : noUserBelow keys keys.length m u) : ∀ k, m !! k ≠ some u := by
  intro k hk
  have hin : k ∈ keys := (hmem k).2 (by rw [hsub k u hk]; rfl)
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hin
  exact H j k hj (by rw [List.getElem?_eq_getElem hj, hjk]) hk

/-- A map below `A` with no key mapping to `u` is below `A` without `u`'s keys. -/
theorem subseteq_filter_user (m A : GMap GoString GoString) (u : GoString) (hsub : m ⊆ A)
    (hno : ∀ k, m !! k ≠ some u) : m ⊆ GMap.filter (fun _ v => decide (v ≠ u)) A := by
  intro k v hk
  rw [GMap.lookup_filter, hsub k v hk]
  have : v ≠ u := fun h => hno k (h ▸ hk)
  simp [this]

theorem subseteq_trans' {K V : Type} {m1 m2 m3 : GMap K V} (h1 : m1 ⊆ m2) (h2 : m2 ⊆ m3) :
    m1 ⊆ m3 := fun k v h => h2 k v (h1 k v h)

end auth
end EtcdGrove
end Perennial
