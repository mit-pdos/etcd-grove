/-
The leader's stats (`*v2stats.LeaderStats`) as the transport uses them (D43 M5a, 2026-10-26).
Lean-first (no Rocq counterpart).

* `v2stats.isLeaderStats ls` (persistent): the stats' embedded `sync.Mutex`, guarding nothing the
  proofs need (`Follower` takes it).
* `v2stats.lsFollowers ls q` (fractional): the `Followers` field (written only by the constructor,
  read-only) and its map at the fraction `q`, its values non-nil. The map's writers are
  the transport's (`AddPeer`'s `Follower` call and `removePeer`'s unlocked `delete`), both under the
  transport's write lock, which therefore owns it (`trLockP`), not the stats' own mutex.
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
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev v2stats.lsFollowersAddr (ls : Loc) : Loc :=
  structFieldRef v2stats.leaderStats go!"Followers"
    (structFieldRef v2stats.LeaderStats go!"leaderStats" ls)

abbrev v2stats.lsMutexAddr (ls : Loc) : Loc := structFieldRef v2stats.LeaderStats go!"Mutex" ls

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The leader's stats `ls`** (persistent): see the file header. -/
def v2stats.isLeaderStats (ls : Loc) : IProp GF :=
  sync.isMutex (v2stats.lsMutexAddr ls) iprop(True)

instance v2stats.isLeaderStats_persistent (ls : Loc) :
    Persistent (v2stats.isLeaderStats (GF := GF) ls) := by
  unfold v2stats.isLeaderStats; infer_instance

/-- **The followers' map of `ls`** at the fraction `q`: see the file header. -/
def v2stats.lsFollowers (ls : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (fm : Loc) (FM : GMap GoString Loc), v2stats.lsFollowersAddr ls ↦□ fm ∗
    ownMap fm (DFrac.own q) FM ∗ ⌜∀ k v, FM !! k = some v → v ≠ null⌝)

instance v2stats.lsFollowers_fractional (ls : Loc) :
    Fractional (v2stats.lsFollowers (GF := GF) ls) where
  fractional q1 q2 := by
    unfold v2stats.lsFollowers
    refine ⟨?_, ?_⟩
    · iintro ⟨%fm, %FM, #Hf, Hm, %Hnn⟩
      icases ((ownMap_fractional (GF := GF) fm FM).fractional q1 q2).1 $$ Hm with ⟨H1, H2⟩
      isplitl [H1]
      · iexists fm, FM; iframe; iframe #; ipureintro; exact Hnn
      · iexists fm, FM; iframe; iframe #; ipureintro; exact Hnn
    · iintro ⟨⟨%fm, %FM, #Hf, H1, %Hnn⟩, ⟨%fm', %FM', #Hf', H2, -⟩⟩
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

end defs

end EtcdGrove
end Perennial
