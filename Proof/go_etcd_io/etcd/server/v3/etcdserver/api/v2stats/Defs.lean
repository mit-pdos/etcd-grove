/-
The leader's stats (`*v2stats.LeaderStats`) as the transport uses them (D43 M5a, 2026-10-26).
Lean-first (no Rocq counterpart).

* `v2stats.isLeaderStats ls` (persistent): the stats' embedded `sync.Mutex`, guarding nothing the
  proofs need (`Follower` takes it).
* `v2stats.lsFollowers ls q` (fractional): the `Followers` field (written only by the constructor,
  read-only) and its map at the fraction `q`, its values non-nil follower stats
  (`v2stats.isFollowerStats`).
* `v2stats.isFollowerStats fs` (persistent; prove-ps2, 2026-11-21): the follower stats' embedded
  `sync.Mutex`, guarding the failure count `Counts.Fail` (what `Fail` writes; `Succ`, assumed, writes
  only the other fields). `Follower` allocates it with the stats (`&FollowerStats{}`). The map's writers are
  the transport's (`AddPeer`'s `Follower` call and `removePeer`'s unlocked `delete`), both under the
  transport's write lock, which therefore owns it (`trLockP`), not the stats' own mutex.
* `v2stats.isServerStats ss` (persistent; prove-ps2-v2stats, 2026-11-21, until then opaque): the
  stats' embedded `sync.Mutex`, owning the embedded `serverStats` (`ssLockR`), whose two rate queues
  are fixed (`NewServerStats` allocates them, no method writes them), each a `statsQueue` whose
  `RWMutex` owns its fields (`isStatsQueue`). Only the writers' half of the `RWMutex` is kept (its
  guard: `Insert` and `Clear` take the write lock; `Rate`'s readers are not verified).
* `v2stats.sqOk`: the ring's invariant: `0 ≤ size ≤ 200`, `front` an index, `back` an index or
  `-1` (initially), `back + 1 ≡ front + size (mod 200)`, and the `size` slots from `front` on
  non-nil (`Insert` reads `items[front].Size` when the ring is full). Every slot is nil or points to
  a `RequestStats` (persistently: nothing writes one after `Insert` stores it).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

abbrev v2stats.lsFollowersAddr (ls : Loc) : Loc :=
  structFieldRef v2stats.leaderStats go!"Followers"
    (structFieldRef v2stats.LeaderStats go!"leaderStats" ls)

abbrev v2stats.lsMutexAddr (ls : Loc) : Loc := structFieldRef v2stats.LeaderStats go!"Mutex" ls

abbrev v2stats.fsMutexAddr (fs : Loc) : Loc := structFieldRef v2stats.FollowerStats go!"Mutex" fs

abbrev v2stats.fsFailAddr (fs : Loc) : Loc :=
  structFieldRef v2stats.CountsStats go!"Fail" (structFieldRef v2stats.FollowerStats go!"Counts" fs)

abbrev v2stats.ssInnerAddr (ss : Loc) : Loc := structFieldRef v2stats.ServerStats go!"serverStats" ss

abbrev v2stats.ssMutexAddr (ss : Loc) : Loc := structFieldRef v2stats.ServerStats go!"Mutex" ss

abbrev v2stats.sqRwlAddr (q : Loc) : Loc := structFieldRef v2stats.statsQueue go!"rwl" q

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The leader's stats `ls`** (persistent): see the file header. -/
def v2stats.isLeaderStats (ls : Loc) : IProp GF :=
  sync.isMutex (v2stats.lsMutexAddr ls) iprop(True)

instance v2stats.isLeaderStats_persistent (ls : Loc) :
    Persistent (v2stats.isLeaderStats (GF := GF) ls) := by
  unfold v2stats.isLeaderStats; infer_instance

/-- **The follower stats `fs`** (persistent): see the file header. -/
def v2stats.isFollowerStats (fs : Loc) : IProp GF :=
  sync.isMutex (v2stats.fsMutexAddr fs) iprop(∃ c : w64, v2stats.fsFailAddr fs ↦ c)

instance v2stats.isFollowerStats_persistent (fs : Loc) :
    Persistent (v2stats.isFollowerStats (GF := GF) fs) := by
  unfold v2stats.isFollowerStats; infer_instance

/-- **The followers' map of `ls`** at the fraction `q`: see the file header. -/
def v2stats.lsFollowers (ls : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (fm : Loc) (FM : GMap GoString Loc), v2stats.lsFollowersAddr ls ↦□ fm ∗
    ownMap fm (DFrac.own q) FM ∗ ⌜∀ k v, FM !! k = some v → v ≠ null⌝ ∗
    □ (∀ k v, ⌜FM !! k = some v⌝ → v2stats.isFollowerStats v))

instance v2stats.lsFollowers_fractional (ls : Loc) :
    Fractional (v2stats.lsFollowers (GF := GF) ls) where
  fractional q1 q2 := by
    unfold v2stats.lsFollowers
    refine ⟨?_, ?_⟩
    · iintro ⟨%fm, %FM, #Hf, Hm, %Hnn, #Hfs⟩
      icases ((ownMap_fractional (GF := GF) fm FM).fractional q1 q2).1 $$ Hm with ⟨H1, H2⟩
      isplitl [H1]
      · iexists fm, FM; iframe; iframe #; ipureintro; exact Hnn
      · iexists fm, FM; iframe; iframe #; ipureintro; exact Hnn
    · iintro ⟨⟨%fm, %FM, #Hf, H1, %Hnn, #Hfs⟩, ⟨%fm', %FM', #Hf', H2, -, -⟩⟩
      ihave %Hfa := typedPointsto_agree_wand _ _ _ _ _ $$ Hf Hf'
      subst Hfa
      ihave %HMa := ownMap_agree fm _ _ FM FM' $$ [H1 H2]
      · iframe
      subst HMa
      iexists fm, FM
      iframe #
      isplitl
      · iapply ((ownMap_fractional (GF := GF) fm FM).fractional q1 q2).2
        iframe
      ipureintro; exact Hnn

/-- The ring's invariant (see the file header), over `items`, `size`, `front` and `back`. -/
def v2stats.sqOk (it : List Loc) (sz fr bk : w64) : Prop :=
  0 ≤ sint.Z sz ∧ sint.Z sz ≤ 200 ∧ 0 ≤ sint.Z fr ∧ sint.Z fr < 200 ∧ -1 ≤ sint.Z bk ∧
    sint.Z bk < 200 ∧ (sint.Z bk + 1) % 200 = (sint.Z fr + sint.Z sz) % 200 ∧
    ∀ k : Int, 0 ≤ k → k < sint.Z sz → it.getD ((sint.Z fr + k) % 200).toNat null ≠ null

/-- A slot of the ring: nil, or a `RequestStats` (persistent). -/
def v2stats.sqSlot (x : Loc) : IProp GF :=
  iprop(⌜x = null⌝ ∨ ∃ rs : v2stats.RequestStats, x ↦□ rs)

instance v2stats.sqSlot_persistent (x : Loc) : Persistent (v2stats.sqSlot (GF := GF) x) := by
  unfold v2stats.sqSlot; infer_instance

/-- The queue `q`'s fields (but its `RWMutex`) at the fraction `f`, at the values `x` (`items`,
`size`, `front`, `back`, `totalReqSize`). -/
def v2stats.sqBody (q : Loc) (x : GoArray Loc 200 × w64 × w64 × w64 × w64) (f : Qp) :
    IProp GF :=
  iprop(structFieldRef v2stats.statsQueue go!"items" q ↦{DFrac.own f} x.1 ∗
    structFieldRef v2stats.statsQueue go!"size" q ↦{DFrac.own f} x.2.1 ∗
    structFieldRef v2stats.statsQueue go!"front" q ↦{DFrac.own f} x.2.2.1 ∗
    structFieldRef v2stats.statsQueue go!"back" q ↦{DFrac.own f} x.2.2.2.1 ∗
    structFieldRef v2stats.statsQueue go!"totalReqSize" q ↦{DFrac.own f} x.2.2.2.2 ∗
    ⌜v2stats.sqOk x.1.arr x.2.1 x.2.2.1 x.2.2.2.1⌝ ∗
    [∗list] y ∈ x.1.arr, v2stats.sqSlot y)

/-- What the queue `q`'s `RWMutex` owns, at the fraction `f`. -/
def v2stats.sqP (q : Loc) (f : Qp) : IProp GF :=
  iprop(∃ x, v2stats.sqBody q x f)

instance v2stats.sqSlot_timeless (x : Loc) : Timeless (v2stats.sqSlot (GF := GF) x) := by
  unfold v2stats.sqSlot; infer_instance

instance v2stats.sqP_timeless (q : Loc) (f : Qp) : Timeless (v2stats.sqP (GF := GF) q f) := by
  unfold v2stats.sqP v2stats.sqBody; infer_instance

instance v2stats.sqP_fractional (q : Loc) : Fractional (v2stats.sqP (GF := GF) q) := by
  unfold v2stats.sqP
  exact fractional_exists_agree (fun x f => v2stats.sqBody (GF := GF) q x f)
    (fun x => ⟨fun q1 q2 => by
      unfold v2stats.sqBody
      constructor
      · iintro ⟨Hi, Hs, Hf, Hb, Ht, %Hok, #Hel⟩
        icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hi with ⟨Hi1, Hi2⟩
        icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hs with ⟨Hs1, Hs2⟩
        icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hf with ⟨Hf1, Hf2⟩
        icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hb with ⟨Hb1, Hb2⟩
        icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Ht with ⟨Ht1, Ht2⟩
        isplitl [Hi1 Hs1 Hf1 Hb1 Ht1]
        · iframe Hi1 Hs1 Hf1 Hb1 Ht1 Hel; ipureintro; exact Hok
        · iframe Hi2 Hs2 Hf2 Hb2 Ht2 Hel; ipureintro; exact Hok
      · iintro ⟨⟨Hi1, Hs1, Hf1, Hb1, Ht1, %Hok, #Hel⟩, ⟨Hi2, Hs2, Hf2, Hb2, Ht2, -, -⟩⟩
        iframe Hel
        isplitl [Hi1 Hi2]
        · iapply (typedPointsto_frac_add _ _ q1 q2).2 $$ [$Hi1 $Hi2]
        isplitl [Hs1 Hs2]
        · iapply (typedPointsto_frac_add _ _ q1 q2).2 $$ [$Hs1 $Hs2]
        isplitl [Hf1 Hf2]
        · iapply (typedPointsto_frac_add _ _ q1 q2).2 $$ [$Hf1 $Hf2]
        isplitl [Hb1 Hb2]
        · iapply (typedPointsto_frac_add _ _ q1 q2).2 $$ [$Hb1 $Hb2]
        isplitl [Ht1 Ht2]
        · iapply (typedPointsto_frac_add _ _ q1 q2).2 $$ [$Ht1 $Ht2]
        ipureintro; exact Hok⟩)
    (fun x y q1 q2 => by
      unfold v2stats.sqBody
      iintro ⟨⟨Hi1, Hs1, Hf1, Hb1, Ht1, -⟩, ⟨Hi2, Hs2, Hf2, Hb2, Ht2, -⟩⟩
      icombine Hi1 Hi2 gives %H1
      icombine Hs1 Hs2 gives %H2
      icombine Hf1 Hf2 gives %H3
      icombine Hb1 Hb2 gives %H4
      icombine Ht1 Ht2 gives %H5
      ipureintro
      obtain ⟨x1, x2, x3, x4, x5⟩ := x
      obtain ⟨y1, y2, y3, y4, y5⟩ := y
      simp only at H1 H2 H3 H4 H5
      subst H1 H2 H3 H4 H5; rfl)

/-- **A rate queue `q`** (persistent): see the file header. -/
def v2stats.isStatsQueue (q : Loc) : IProp GF :=
  sync.isRWMutexGuard (v2stats.sqRwlAddr q) (v2stats.sqP q)

instance v2stats.isStatsQueue_persistent (q : Loc) :
    Persistent (v2stats.isStatsQueue (GF := GF) q) := by
  unfold v2stats.isStatsQueue; infer_instance

/-- What the server stats' mutex owns: the embedded `serverStats`, its queues `sq` and `rq`. -/
def v2stats.ssLockR (ss sq rq : Loc) : IProp GF :=
  iprop(∃ v : v2stats.serverStats, v2stats.ssInnerAddr ss ↦ v ∗
    ⌜v.sendRateQueue' = sq ∧ v.recvRateQueue' = rq⌝)

/-- **The server's stats `ss`, as `NewServerStats` makes them** (persistent): see the file
header. -/
def v2stats.isServerStats (ss : Loc) : IProp GF :=
  iprop(∃ sq rq : Loc, sync.isMutex (v2stats.ssMutexAddr ss) (v2stats.ssLockR ss sq rq) ∗
    v2stats.isStatsQueue sq ∗ v2stats.isStatsQueue rq)

instance v2stats.isServerStats_persistent (ss : Loc) :
    Persistent (v2stats.isServerStats (GF := GF) ss) := by
  unfold v2stats.isServerStats; infer_instance

end defs

end EtcdGrove
end Perennial
