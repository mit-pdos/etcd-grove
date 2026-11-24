/-
**A new cluster before it is shared** (claim #34, stage 2, 2026-11-25; `notes/bootstrap-proof-plan.md`
§7.4): the vocabulary of the specs of `NewClusterFromURLsMap` and of what it calls (`NewCluster`,
`NewMember`, `computeMemberID`, `genID`, `MemberIDs`), of `MemberByName` and of `SetID`, at the etcd
pin (`server/etcdserver/api/membership/{cluster,member,cluster_opts}.go`). Lean-first. A defs module.

- `memberIDOf strs token`: `computeMemberID`'s id of the peer URLs' strings `strs` (`now = nil`): the
  first eight bytes, big-endian, of the SHA-1 (Perennial's `crypto.sha1.sha1`, FIPS 180-4) of the
  strings sorted (Go's string order) and joined, then the token.
- `memberOfURLs name us token`: `NewMember(name, us, token, nil)`'s value (`urlStrOf`: `URL.String()`
  of a plain URL, `http.urlRootPlain`).
- `memOfList L`: the members map of the members `L`, each under its id.
- `idsSorted mem ids`: `MemberIDs()`' answer: the keys of `mem`, ascending.
- `clusterIdOf ids`: `genID()`'s id of the sorted ids.
- `clusterOwned c ml ms mem cid`: the cluster `c` owned field by field, as `NewCluster`'s literal and
  the members' insertions leave it (`etcdserver.clusterBuilt` at the boot values), its mutex zero (no
  lock invariant yet: `MemberIDs`, `MemberByName` lock and unlock it owned, `ownedMutex_lock`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex
public import Proof.net.http.Boundary
public import Perennial.Proof.crypto.sha1.Fips180

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

/-! ### Pure values -/

/-- Go's string order (`sort.Strings`), decided. -/
def membership.strLeB (a b : GoString) : Bool := decide (go.GoStringLe a b)

/-- `url.URL.String()` of a plain URL (`http.urlRootPlain`): `http://` and the host. -/
def membership.urlStrOf [GooseExts] (u : _root_.Perennial.net.url.URL) : GoString :=
  go!"http://" ++ u.Host'

/-- **`computeMemberID(peerURLs, token, nil)`** of the peer URLs' strings `strs`: the first eight
bytes, big-endian, of `sha1(join(sort(strs), "") ++ token)`. -/
def membership.memberIDOf (strs : List GoString) (token : GoString) : w64 :=
  beToU64 ((crypto.sha1.sha1 ((strs.mergeSort membership.strLeB).flatten ++ token)).take 8)

/-- **`NewMember(name, us, token, nil)`'s member**: its id, its peer URLs' strings, a voter, its
name, no client URLs. -/
def membership.memberOfURLs [GooseExts] (name : GoString) (us : List _root_.Perennial.net.url.URL)
    (token : GoString) : apply.MemberM :=
  ⟨membership.memberIDOf (us.map membership.urlStrOf) token, us.map membership.urlStrOf, false, name,
    []⟩

/-- **The members map of `L`**, each member under its id (`c.members[m.ID] = m`, in `L`'s order). -/
def membership.memOfList (L : List apply.MemberM) : GMap w64 apply.MemberM :=
  L.foldl (fun mem m => mem.insert m.id m) ∅

/-- **`MemberIDs()`' answer of the members `mem`**: their ids, each once, ascending. -/
def membership.idsSorted (mem : GMap w64 apply.MemberM) (ids : List w64) : Prop :=
  ids.Nodup ∧ (∀ k, k ∈ ids ↔ (mem !! k).isSome) ∧ ids.Pairwise (fun a b => a.toNat < b.toNat)

/-- **`genID()`'s id of the sorted ids `ids`**: the first eight bytes, big-endian, of the SHA-1 of
the ids' big-endian bytes. -/
def membership.clusterIdOf (ids : List w64) : w64 :=
  beToU64 ((crypto.sha1.sha1 (ids.flatMap u64Be)).take 8)

/-- Each member of `mem` is under its own id. -/
def membership.memIdsOk (mem : GMap w64 apply.MemberM) : Prop :=
  ∀ k m, mem !! k = some m → m.id = k

/-- No two members of `mem` share a name (`MemberByName`'s `lg.Panic` otherwise). -/
def membership.memNamesUniq (mem : GMap w64 apply.MemberM) : Prop :=
  ∀ k1 k2 m1 m2, mem !! k1 = some m1 → mem !! k2 = some m2 → m1.name = m2.name → k1 = k2

/-! ### The cluster, owned -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The cluster `c`, owned field by field** (not shared: no lock invariant), with `maxLearners`
`ml`, the members `ms` holding the values `mem` (`memAt` at `1`), the cluster id `cid`, and every
other field as `NewCluster`'s literal leaves it (`cluster.go:105-119`: the logger a zap logger, the
local id `0`, no backend, the mutex unlocked, no version, an empty removed map, the downgrade info
`{Enabled: false}`, no version notifier). -/
def membership.clusterOwned (c : Loc) (ml : w64) (ms : GMap w64 Loc)
    (mem : GMap w64 apply.MemberM) (cid : w64) : IProp GF :=
  iprop(∃ (lgc rp dp : Loc),
    membership.rcLgAddr c ↦ lgc ∗ zapLoggerOk lgc ∗
    membership.rcLocalIDAddr c ↦ (W64 0 : w64) ∗
    membership.rcCidAddr c ↦ cid ∗
    membership.rcBeAddr c ↦ (GoInterface.nil : GoInterface) ∗
    membership.rcMutexAddr c ↦ (zero_val _root_.Perennial.sync.Mutex) ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster go!"version" c ↦
      (null : Loc) ∗
    membership.memAt c 1 ms mem ∗
    membership.rcRemovedAddr c ↦ rp ∗ rp ↦$ (∅ : GMap w64 Bool) ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster go!"downgradeInfo" c ↦
      dp ∗
    dp ↦ (go_etcd_io.etcd.server.v3.etcdserver.version.DowngradeInfo.mk [] false) ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster go!"maxLearners" c ↦
      ml ∗
    membership.rcVersionChangedAddr c ↦ (null : Loc))

/-- **A cluster option setting `maxLearners` to `ml`** (persistent; `WithMaxLearners(ml)`'s closure,
`cluster_opts.go:39-43`): called on a `*ClusterOptions`, it stores `ml` in its field. -/
def membership.clusterOptMax (f : GoFunc) (ml : w64) : IProp GF :=
  iprop(□ ∀ (p : Loc) (ml0 : w64) (Φ : val → IProp GF),
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterOptions go!"maxLearners" p ↦
      ml0 -∗
    ▷ (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.membership.ClusterOptions go!"maxLearners" p ↦
      ml -∗ Φ #()) -∗
    WP (App (Val #f) (Val #p)) {{ Φ }})

instance membership.clusterOptMax_persistent (f : GoFunc) (ml : w64) :
    Persistent (membership.clusterOptMax (GF := GF) f ml) := by
  unfold membership.clusterOptMax; infer_instance

end defs

section loop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A range loop over a slice the loop only reads** (`for i, x := range s { body }`): `P i` holds
before the `i`-th iteration, and the body ends normally. (A copy of
`Proof/k8s_io/api/DeepCopyBase.lean`'s `wp_slice_for_range`, as `raft/v3/DescribeConfChange.lean`'s;
a caller disables `pure_wp_slice_for_range` so that `wp_auto` leaves the loop to it.) -/
theorem membership.wp_slice_for_range_ro {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (dq : DFrac) (body : GoFunc)
    (P : Nat → IProp GF) (Φ : val → IProp GF) :
    sl ↦*{dq} vs -∗ P 0 -∗
    □ (∀ (i : Nat) (x : V), ⌜vs[i]? = some x⌝ -∗ P i -∗ sl ↦*{dq} vs -∗
        WP (App (App (Val #body) (Val #(W64 i))) (Val #x))
          {{ bv, ⌜bv = executeVal⌝ ∗ P (i + 1) ∗ sl ↦*{dq} vs }}) -∗
    (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) -∗
    WP (App (App (Val (slice.forRange t)) (Val #sl)) (Val #body)) {{ Φ }} := by
  iintro Hs HP #Hiter HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  unfold slice.forRange
  wp_auto
  ihave Hinv : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 j ∗ "HP" ∷ P j ∗ "Hs" ∷ sl ↦*{dq} vs ∗
      "HΦ" ∷ (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) ∗ "%Hj" ∷ ⌜j ≤ vs.length⌝ :
      IProp GF) $$ [i HP Hs HΦ]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for Hinv
  by_cases hj : j < vs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, vs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index (t := t) sl (sint.Z (W64 (j : Int))) vs dq x h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    iapply wp_wand $$ (Hiter $$ %j %x %hx HP Hs)
    iintro %bv ⟨%hbv, HP, Hs⟩
    subst hbv
    iapply wp_for_post_do
    wp_auto
    iframe
    iexists (j + 1)
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    have hj1 : j + 1 ≤ vs.length := hj
    iframe
    ipureintro; exact hj1
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = vs.length := by omega
    subst hjl
    iapply HΦ $$ HP Hs

end loop

end EtcdGrove
end Perennial
