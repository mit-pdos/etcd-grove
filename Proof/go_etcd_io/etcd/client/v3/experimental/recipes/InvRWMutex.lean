/-
`client/v3/experimental/recipes`' `RWMutex` (`rwmutex.go`): the vocabulary of
`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/{NewRWMutex,RWMutex__*}.lean` and
**exclusion**. Lean-first (no Rocq counterpart). See `decisions.md`, "Recipes", "Units 1b, 2 and 3".

**The protocol.** An `RWMutex` on the prefix `pfx` (`NewRWMutex`'s argument with a `/`) creates a
fresh ephemeral key `pfx/read/<n>` (`RLock`) or `pfx/write/<n>` (`Lock`) with its session's lease
(`newUniqueEphemeralKey`), created at `c`; then, until done, it gets the key with the greatest mod
revision below `c` among the blocking keys (`waitOnLastRev`: `WithLastRev()` and
`WithMaxModRev(c - 1)`; a reader is blocked by the keys with prefix `pfx/write`, a writer by every
key under `pfx`) and, if there is one, waits for its deletion; done when there is none.

**The ownership fact** `rwHeldAt pfx role key c R` (persistent): the holder's key, under
`pfx/<role>/`, was created at `c ≤ R`, and at revision `R` no key it is blocked by has a mod
revision below `c` (`RWBlockFree`). It says nothing of the holder's own key at `R`: neither `RLock`
nor `Lock` checks its key after the wait (a session expiry may have deleted it), so the results are
about keys present in a state, as `Mutex`'s.

**Exclusion** (`rwHeldAt_write_exclusion`, `rwHeldAt_read_write_exclusion`): a writer and any other
holder with a different create revision are never both present in a state at a revision at or
after both `R`s; two readers may be (a reader is not blocked by a read key). As the mutex's
`lockedAt_excludes_earlier`, from the history law `etcdState_create_persist`: if both were present
at `a`, the key created first was present at the later-created holder's `R` with the same create
revision, and blocked it, **provided its mod revision there is still its create revision**: the
recipe's get filters by mod revision (`WithMaxModRev`), not by create revision as `Mutex`'s
(`WithMaxCreateRev`), so a key under the prefix rewritten by someone (a plain `Put`, which keeps
its create revision and moves its mod revision past a later holder's) is invisible to the later
holder. Hence the premise `keyUnmodified pfx key c` on the earlier key: etcd's history never shows
`key`, created at `c`, with another mod revision. True of the recipe's keys, which it only creates
and deletes; a premise on the other clients, as the session-lease premise.

**The mutex** (`isRWMutex m s γ client id pfx`, persistent: its session, its context
(`context.TODO()`), its prefix, the client bundle at the prefix) and its **key** (`rwMyKey m pfx o`,
exclusive: the `myKey` field, `none` for a pointer the proof does not track, `some (ek, st)` for an
owned `*EphemeralKV` with its record).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3
open concurrency

/-! ## Roles and the blocking keys (pure) -/

/-- A holder's role: a reader (`RLock`) or a writer (`Lock`). -/
inductive RWRole where
  | read
  | write
  deriving DecidableEq

/-- The path segment of a role's keys (`pfx/read/<n>`, `pfx/write/<n>`). -/
def RWRole.name : RWRole → GoString
  | .read => go!"read"
  | .write => go!"write"

/-- The prefix of the keys that block a holder (`waitOnLastRev`'s argument): the write keys'
`pfx ++ "write"` for a reader, every key under `pfx` for a writer. -/
def RWRole.blockPfx (pfx : GoString) : RWRole → GoString
  | .read => pfx ++ go!"write"
  | .write => pfx

/-- In the state `s`, no key with the prefix `bp` has a mod revision below `c`. -/
def RWBlockFree (bp : GoString) (c : w64) (s : List EtcdKv) : Prop :=
  ∀ v ∈ s, bp <+: v.key → sint.Z c ≤ sint.Z v.modRev

/-- The get `OpGet(bp, WithLastRev()..., WithMaxModRev(n))` of `waitOnLastRev`. -/
def lastRevOp (bp : GoString) (n : w64) : OpFull :=
  opGetModel bp (withTopM (W64 3) (W64 2) ++ [withMaxModRevM n])

theorem lastRevOp_fields (bp : GoString) (n : w64) (hp : bp ≠ []) :
    (lastRevOp bp n).key = bp ∧ (lastRevOp bp n).base.rangeEnd = prefixRangeEnd bp ∧
    (lastRevOp bp n).base.limit = W64 1 ∧ (lastRevOp bp n).base.countOnly = false ∧
    (lastRevOp bp n).keysOnly = false ∧ (lastRevOp bp n).base.minModRev = W64 0 ∧
    (lastRevOp bp n).base.maxModRev = n ∧ (lastRevOp bp n).base.minCreateRev = W64 0 ∧
    (lastRevOp bp n).base.maxCreateRev = W64 0 := by
  simp [lastRevOp, opGetModel, opFold, withTopM, withPrefixM, withSortM, withLimitM,
    withMaxModRevM, OpFull.getInit, OpFull.newOp, OpModel.zero, hp]

theorem lastRevOp_t (bp : GoString) (n : w64) : (lastRevOp bp n).t = W64 1 := by
  by_cases h : bp = [] <;> simp [lastRevOp, opGetModel, opFold, withTopM, withPrefixM, withSortM,
    withLimitM, withMaxModRevM, OpFull.getInit, OpFull.newOp, OpModel.zero, h]

theorem lastRevOp_rev (pfx bp : GoString) (n : w64) :
    (lastRevOp bp n).base.rev = W64 0 ∧ (lastRevOp bp n).base.serializable = false ∧
      (lastRevOp bp n).isPrefixGet pfx = false := by
  by_cases h : bp = [] <;> simp [lastRevOp, opGetModel, opFold, withTopM, withPrefixM, withSortM,
    withLimitM, withMaxModRevM, OpFull.getInit, OpFull.newOp, OpModel.zero, h, OpFull.isPrefixGet]

theorem lastRevOp_not_panics (n : w64) :
    ¬ opGetPanics (withTopM (W64 3) (W64 2) ++ [withMaxModRevM n]) := by
  simp [opFold, withTopM, withPrefixM, withSortM, withLimitM, withMaxModRevM, OpFull.newOp,
    OpModel.zero, opGetPanics]

theorem lastRevOp_under (pfx bp : GoString) (n : w64) (hp : bp ≠ []) (h : pfx <+: bp) :
    KeyRangeUnder pfx (lastRevOp bp n).key (lastRevOp bp n).base.rangeEnd := by
  obtain ⟨hk, he, -⟩ := lastRevOp_fields bp n hp
  rw [hk, he]
  intro k hk'
  exact h.trans (keyRangeUnder_prefix bp hp k hk')

/-- **`waitOnLastRev`'s get** (`OpGet(bp, WithLastRev()..., WithMaxModRev(n))`; `n = 0` is no
filter): nothing means no key with the prefix `bp` has a mod revision at most `n` (or, with no
filter, no key has the prefix); anything listed is in the state. -/
theorem lastRevOp_kvs (bp : GoString) (n : w64) (s kvs : List EtcdKv) (hp : bp ≠ [])
    (h : rangeKvsOk (lastRevOp bp n) (rangeSel s (lastRevOp bp n)) kvs) :
    (kvs = [] → ∀ v ∈ s, bp <+: v.key → n ≠ W64 0 ∧ sint.Z n < sint.Z v.modRev) ∧
      ∀ w ∈ kvs, w ∈ s := by
  obtain ⟨hkey, he, hl, hc, hko, h1, h2, h3, h4⟩ := lastRevOp_fields bp n hp
  have hmem : ∀ v, v ∈ rangeSel s (lastRevOp bp n) ↔
      v ∈ s ∧ bp <+: v.key ∧ (n = W64 0 ∨ sint.Z v.modRev ≤ sint.Z n) := by
    intro v
    unfold rangeSel rangeIn
    rw [List.mem_filter, List.mem_filter, hkey, he, inRange_prefix bp v.key hp]
    simp only [kvFilterOk, h1, h2, h3, h4]
    by_cases hn0 : n = W64 0
    · simp [hn0]
    · simp [_root_.and_assoc]
  obtain ⟨l, hperm, -, -, -, rfl⟩ := h
  simp only [hc, hl, hko] at *
  refine ⟨fun h0 v hv hvp => ?_, fun w hw => ?_⟩
  · by_cases hn0 : n = W64 0
    · exfalso
      have := hperm.symm.subset ((hmem v).2 ⟨hv, hvp, Or.inl hn0⟩)
      cases l with
      | nil => simp at this
      | cons x l' => simp at h0
    · refine ⟨hn0, Int.lt_of_not_ge fun hle => ?_⟩
      have := hperm.symm.subset ((hmem v).2 ⟨hv, hvp, Or.inr hle⟩)
      cases l with
      | nil => simp at this
      | cons x l' => simp at h0
  · simp at hw
    have := List.mem_of_mem_take hw
    exact ((hmem w).1 (hperm.subset this)).1

/-- A role's keys block a writer, and a writer's keys block every role. -/
theorem rwRole_key_blockPfx (pfx key : GoString) (role : RWRole)
    (h : (pfx ++ role.name) ++ go!"/" <+: key) : RWRole.blockPfx pfx .write <+: key :=
  (List.prefix_append pfx role.name).trans ((List.prefix_append _ _).trans h)

theorem rwRole_write_key_blockPfx (pfx key : GoString) (role : RWRole)
    (h : (pfx ++ RWRole.name .write) ++ go!"/" <+: key) : role.blockPfx pfx <+: key := by
  cases role
  · exact (List.prefix_append _ _).trans h
  · exact rwRole_key_blockPfx pfx key .write h

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-! ## The ownership fact -/

/-- **`key` holds the RWMutex on `pfx` in the role `role` since revision `R`, created at `c`**
(persistent): `key` is under `pfx/<role>/`, `0 < c ≤ R`, and at `R` no key blocking the role
(`role.blockPfx pfx`) has a mod revision below `c` (`RWBlockFree`). -/
def rwHeldAt (pfx : GoString) (role : RWRole) (key : GoString) (c R : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState R pfx s ∗
    ⌜(pfx ++ role.name) ++ go!"/" <+: key ∧ 0 < sint.Z c ∧ sint.Z c ≤ sint.Z R ∧
      RWBlockFree (role.blockPfx pfx) c s⌝)

instance rwHeldAt_persistent (pfx : GoString) (role : RWRole) (key : GoString) (c R : w64) :
    Persistent (rwHeldAt (GF := GF) pfx role key c R) := by
  unfold rwHeldAt; infer_instance

/-- **The key `key` created at `c` is never modified** (persistent; a premise on etcd's history,
that is, on the other clients: see the module docstring): in etcd's state at any revision, a
key-value of `key` with create revision `c` has mod revision `c`. -/
def keyUnmodified (pfx key : GoString) (c : w64) : IProp GF :=
  iprop(□ ∀ (r : w64) (s : List EtcdKv), □ etcdState r pfx s -∗
    ⌜∀ v ∈ s, v.key = key → v.createRev = c → v.modRev = c⌝)

instance keyUnmodified_persistent (pfx key : GoString) (c : w64) :
    Persistent (keyUnmodified (GF := GF) pfx key c) := by
  unfold keyUnmodified; infer_instance

/-- One direction of exclusion: a holder `(k2, c2)` since `R2`, in the role `role`, excludes at any
`a ≥ R2` an unmodified key `k1` created before `c2` with the prefix that blocks the role. -/
theorem rwHeldAt_excludes_earlier (pfx k1 k2 : GoString) (role : RWRole) (c1 c2 R2 a : w64)
    (s : List EtcdKv) (hc : sint.Z c1 < sint.Z c2) (ha : sint.Z R2 ≤ sint.Z a)
    (hk1 : role.blockPfx pfx <+: k1) :
    rwHeldAt (GF := GF) pfx role k2 c2 R2 ∗ keyUnmodified pfx k1 c1 ∗ etcdState a pfx s ⊢
      ⌜¬ HasKeyAt k1 c1 s⌝ := by
  unfold rwHeldAt keyUnmodified
  iintro ⟨⟨%s2, #Hs2, %Hl⟩, #Hu, Hs⟩
  ihave %Hun := Hu $$ %R2 %s2 Hs2
  ihave %Hp := etcdState_create_persist a R2 pfx s s2 $$ [$Hs $Hs2]
  ipureintro
  rintro ⟨v, hv, hk, hc1⟩
  obtain ⟨-, -, hc2R, hfree⟩ := Hl
  obtain ⟨v', hv', hk', hv'c⟩ := Hp v hv (by rw [hc1]; omega) ha
  rw [hc1] at hv'c
  have hm := Hun v' hv' (by rw [hk', hk]) hv'c
  have := hfree v' hv' (by rw [hk', hk]; exact hk1)
  rw [hm] at this
  omega

/-- **Writer exclusion**: a writer `(k1, c1)` since `R1` and a holder `(k2, c2)` since `R2` in any
role, with different create revisions and both keys unmodified (`keyUnmodified`), are never both
present in etcd's state at a revision `a` at or after `R1` and `R2`. -/
theorem rwHeldAt_write_exclusion (pfx k1 k2 : GoString) (role : RWRole) (c1 c2 R1 R2 a : w64)
    (s : List EtcdKv) (hne : c1 ≠ c2) (h1 : sint.Z R1 ≤ sint.Z a) (h2 : sint.Z R2 ≤ sint.Z a) :
    rwHeldAt (GF := GF) pfx .write k1 c1 R1 ∗ rwHeldAt pfx role k2 c2 R2 ∗
      keyUnmodified pfx k1 c1 ∗ keyUnmodified pfx k2 c2 ∗ etcdState a pfx s ⊢
      ⌜¬ (HasKeyAt k1 c1 s ∧ HasKeyAt k2 c2 s)⌝ := by
  iintro ⟨#H1, #H2, #Hu1, #Hu2, Hs⟩
  ihave #H1' := H1
  iunfold rwHeldAt at H1'
  icases H1' with ⟨%s1, -, %Hl1⟩
  ihave #H2' := H2
  iunfold rwHeldAt at H2'
  icases H2' with ⟨%s2, -, %Hl2⟩
  have Hk1 := Hl1.1
  have Hk2 := Hl2.1
  have hz : sint.Z c1 ≠ sint.Z c2 := fun h => hne (by word)
  rcases Int.lt_or_gt_of_ne hz with hlt | hgt
  · ihave %H := rwHeldAt_excludes_earlier pfx k1 k2 role c1 c2 R2 a s hlt h2
      (rwRole_write_key_blockPfx pfx k1 role Hk1) $$ [$H2 $Hu1 $Hs]
    ipureintro; exact fun ⟨h, _⟩ => H h
  · ihave %H := rwHeldAt_excludes_earlier pfx k2 k1 .write c2 c1 R1 a s hgt h1
      (rwRole_key_blockPfx pfx k2 role Hk2) $$ [$H1 $Hu2 $Hs]
    ipureintro; exact fun ⟨_, h⟩ => H h

/-- **Reader-writer exclusion**: a reader `(k1, c1)` since `R1` and a writer `(k2, c2)` since `R2`,
with different create revisions and both keys unmodified, are never both present in etcd's state
at a revision `a` at or after `R1` and `R2`. (Two readers may be: a read key does not block a
reader.) -/
theorem rwHeldAt_read_write_exclusion (pfx k1 k2 : GoString) (c1 c2 R1 R2 a : w64)
    (s : List EtcdKv) (hne : c1 ≠ c2) (h1 : sint.Z R1 ≤ sint.Z a) (h2 : sint.Z R2 ≤ sint.Z a) :
    rwHeldAt (GF := GF) pfx .read k1 c1 R1 ∗ rwHeldAt pfx .write k2 c2 R2 ∗
      keyUnmodified pfx k1 c1 ∗ keyUnmodified pfx k2 c2 ∗ etcdState a pfx s ⊢
      ⌜¬ (HasKeyAt k1 c1 s ∧ HasKeyAt k2 c2 s)⌝ := by
  iintro ⟨#H1, #H2, #Hu1, #Hu2, Hs⟩
  ihave %H := rwHeldAt_write_exclusion pfx k2 k1 .read c2 c1 R2 R1 a s (Ne.symm hne) h2 h1
    $$ [$H2 $H1 $Hu2 $Hu1 $Hs]
  ipureintro; exact fun ⟨a1, a2⟩ => H ⟨a2, a1⟩

/-! ## The mutex -/

/-- **The RWMutex** `m` (persistent): its session `s` (of `client`, with the lease `id`), its
context (`context.TODO()`) and its prefix `pfx` (with `NewRWMutex`'s `/`), read-only; the client's
recipes contracts for `pfx` (`isEtcdRecipesClient`: under the premise that a watch channel is
never closed) and `context`'s package fact `WaitEvents` needs. -/
def isRWMutex (m s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) :
    IProp GF :=
  iprop(structFieldRef RWMutex go!"s" m ↦□ s ∗
    structFieldRef RWMutex go!"ctx" m ↦□ GoInterface.ok todoCtxVal ∗
    structFieldRef RWMutex go!"pfx" m ↦□ pfx ∗ ⌜pfx ≠ []⌝ ∗
    isSession s γ client id ∗ isEtcdRecipesClient client pfx ∗ context.isClosedchanInit)

instance isRWMutex_persistent (m s : Loc) (γ : SessionNames) (client : Loc) (id : w64)
    (pfx : GoString) : Persistent (isRWMutex (GF := GF) m s γ client id pfx) := by
  unfold isRWMutex; infer_instance

/-- **The RWMutex's key** (exclusive): the field `myKey` holds `ek`; for `some (ek, st)`, the
proof owns the `*EphemeralKV` `ek` with the record `st` (a key under `pfx`, whose `KV`, if any,
has the recipes' contracts); for `none`, a pointer the proof does not track (nil after
`NewRWMutex`). -/
def rwMyKey (m : Loc) (pfx : GoString) : Option (Loc × RemoteKVSt) → IProp GF
  | none => iprop(∃ ek : Loc, structFieldRef RWMutex go!"myKey" m ↦ ek)
  | some (ek, st) => iprop(structFieldRef RWMutex go!"myKey" m ↦ ek ∗ ownEphemeralKV ek st ∗
      isRecipesKV st.kv pfx ∗ ⌜pfx <+: st.key⌝)

/-- The field `myKey` of any key state (dropping the key's ownership). -/
theorem rwMyKey_field (m : Loc) (pfx : GoString) (o : Option (Loc × RemoteKVSt)) :
    rwMyKey (GF := GF) m pfx o ⊢ ∃ ek : Loc, structFieldRef RWMutex go!"myKey" m ↦ ek := by
  rcases o with _ | ⟨ek, st⟩
  · unfold rwMyKey; iintro H; iexact H
  · unfold rwMyKey; iintro ⟨H, -⟩; iexists ek; iexact H

/-- The key a successful `newUniqueEphemeralKey(s, kp)` returns, with the client's `KV`, as
`myKey`'s state. -/
theorem rwMyKey_new (m client : Loc) (pfx kp key : GoString) (kv : GoInterfaceOk) (ek : Loc)
    (r : w64) (hp : pfx <+: kp) (hk : kp ++ go!"/" <+: key) :
    structFieldRef RWMutex go!"myKey" m ↦ ek ∗ ownEphemeralKV (GF := GF) ek ⟨GoInterface.ok kv, key, r, []⟩ ∗
      clientKVAddr client ↦□ GoInterface.ok kv ∗ isEtcdRecipesClient client pfx ⊢
      rwMyKey m pfx (some (ek, ⟨GoInterface.ok kv, key, r, []⟩)) := by
  iintro ⟨Hmk, Hek, #HKVf, #Hcl⟩
  ihave ⟨%kv', #HKVf', #Hkvc⟩ := isEtcdRecipesClient_kv client pfx $$ Hcl
  icombine HKVf HKVf' gives %Heq
  cases Heq
  simp only [rwMyKey]
  iframe Hmk Hek Hkvc
  ipureintro
  exact hp.trans ((List.prefix_append _ _).trans hk)

/-- **What `RLock`/`Lock` return** (`role` `.read`/`.write`), called knowing etcd has reached `lo`:
`nil` with a fresh key `st.key` (created at `st.rev ≥ lo` with the session's lease `id`, its
record's `KV` not nil, so that `Unlock` deletes it) in `myKey`, holding the mutex in the role since some `R` (`rwHeldAt`); or an error, with `myKey`
anything (the previous key if `newUniqueEphemeralKey` failed, the new one if a wait failed). -/
def rwLockResult (m : Loc) (pfx : GoString) (id : w64) (role : RWRole) (lo : w64)
    (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ (ek : Loc) (st : RemoteKVSt) (R : w64),
      rwMyKey m pfx (some (ek, st)) ∗ keyCreatedAt pfx st.key [] id st.rev ∗ etcdReached R ∗
      rwHeldAt pfx role st.key st.rev R ∗
      ⌜sint.Z lo ≤ sint.Z st.rev ∧ st.kv ≠ GoInterface.nil⌝) ∨
    (⌜err ≠ GoInterface.nil⌝ ∗ ∃ o : Option (Loc × RemoteKVSt), rwMyKey m pfx o))

/-- **What `RUnlock`/`Unlock` return** for the key record `st` (its `Delete`): if the key was
deleted already (no `KV`), `nil`; otherwise an error, or `nil` with the key absent at some
revision at least `lo` that etcd has reached. -/
def rwUnlockResult (pfx : GoString) (st : RemoteKVSt) (lo : w64) (err : GoInterface) : IProp GF :=
  match st.kv with
  | .nil => iprop(⌜err = GoInterface.nil⌝)
  | .ok _ => iprop(⌜err ≠ GoInterface.nil⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ r : w64, etcdReached r ∗ etcdAbsent pfx st.key r ∗
        ⌜sint.Z lo ≤ sint.Z r⌝))

end defs

end recipes
end EtcdGrove
end Perennial
