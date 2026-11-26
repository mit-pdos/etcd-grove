/-
**The server's image row of the apply protocol** (T10 session 9, 2026-11-26; ledger 2026-11-25 "the
backend's image row lives in the apply protocol's `consInv`"): the row `Rw.IR eff p` that `consInv γ Rw`
(`InvApply.lean`) keeps at the protocol's `(eff, p)`. `srvImgRow γ M e p`: a committed prefix `A` of the
server's log reaching `p` (`p = ai0 + |A|`), whose models `M` (the image's: `srvImgModel`) are unchanged
at every index of `[e, p]` (the entries `e+1 … p` wrote nothing), so a commit storing any index
`m ∈ [e, p]` stores an image of `A`'s prefix at `m`. The steps that keep it: `srvImgRow_at` (an entry's
writes done, `writes_doneR`; a snapshot's swap, `ci_swap_auR`), `srvImgRow_nil` (the boot,
`consInv_allocR`), `srvImgRow_skip` (an entry with no writes, `skip_doneR`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-- **The models an image of a committed prefix `A` is of** (the mode-off server's: `bkImg`'s and
`imageRestAt`'s): the KV model, its compaction revision, the lease table and the rest buckets of the
full log `pre ++ A`. -/
def srvImgModel [GooseExts] (γr : ReadNames) (A : List EntryModel) :
    mvcc.Log × Int × LeaseTable × apply.RestM :=
  (kvModel γr.kv A, crevOf γr.kv A, kvLeases γr.kv (γr.raft.pre ++ A),
    restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The image row at `(e, p)`** over the models `M`: a committed prefix `A` reaching `p`, its models
the same at every index of `[e, p]` (`A`'s prefix at `m` is `A.take (m - ai0)`). -/
def srvImgRow {α : Type} (γ : ServerRaftNames) (M : List EntryModel → α) (e p : w64) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γ A ∗
    ⌜uint.Z p = uint.Z γ.ai0 + A.length ∧ ∀ m : w64, uint.Z e ≤ uint.Z m → uint.Z m ≤ uint.Z p →
      M (A.take (uint.nat m - uint.nat γ.ai0)) = M A⌝)

instance srvImgRow_timeless {α : Type} (γ : ServerRaftNames) (M : List EntryModel → α) (e p : w64) :
    Timeless (srvImgRow (GF := GF) γ M e p) := by
  unfold srvImgRow; infer_instance

instance srvImgRow_persistent {α : Type} (γ : ServerRaftNames) (M : List EntryModel → α) (e p : w64) :
    Persistent (srvImgRow (GF := GF) γ M e p) := by
  unfold srvImgRow; infer_instance

/-- **The row at `(k, k)`** from a committed prefix reaching `k` (an entry's writes done; a snapshot's
swap at its index). -/
theorem srvImgRow_at {α : Type} (γ : ServerRaftNames) (M : List EntryModel → α) (k : w64)
    (A : List EntryModel) (h : uint.Z k = uint.Z γ.ai0 + A.length) :
    srvRLogLb (GF := GF) γ A ⊢ srvImgRow γ M k k := by
  iintro #HA
  unfold srvImgRow
  iexists A
  iframe HA
  ipureintro
  refine ⟨h, fun m h1 h2 => ?_⟩
  have hm : uint.nat m - uint.nat γ.ai0 = A.length := by
    have : uint.Z m = uint.Z k := by omega
    have e1 : (uint.nat m : Int) = uint.Z m := by simp [uint.nat]
    have e2 : (uint.nat γ.ai0 : Int) = uint.Z γ.ai0 := by simp [uint.nat]
    omega
  rw [hm, List.take_length]

/-- **The row at the boot** (`p = ai0`): the empty prefix, every index's prefix empty. -/
theorem srvImgRow_nil {α : Type} (γ : ServerRaftNames) (M : List EntryModel → α) (e p : w64)
    (h : uint.Z p = uint.Z γ.ai0) :
    srvRLogLb (GF := GF) γ [] ⊢ srvImgRow γ M e p := by
  iintro #HA
  unfold srvImgRow
  iexists []
  iframe HA
  ipureintro
  refine ⟨by simp [h], fun m _ _ => ?_⟩
  simp

/-- **An entry that changes no model keeps the row** (`skip_doneR`'s step): the processed entry `i =
p + 1` ends the committed prefix `A ++ [x]`, whose models are `A`'s. The row's prefix is `A` (two
committed prefixes of one length). -/
theorem srvImgRow_skip {α : Type} (γ : ServerRaftNames) (M : List EntryModel → α) (e p i : w64)
    (A : List EntryModel) (x : EntryModel) (hi : uint.Z i = uint.Z p + 1)
    (hA : uint.Z i = uint.Z γ.ai0 + A.length + 1) (hM : M (A ++ [x]) = M A) :
    srvRLogLb (GF := GF) γ (A ++ [x]) ⊢ srvImgRow γ M e p -∗ srvImgRow γ M e i := by
  iintro #HA #Hrow
  unfold srvImgRow
  icases Hrow with ⟨%A0, #H0, %hp, %hrow⟩
  icases srvRLogLb_prefix γ A0 (A ++ [x]) $$ [H0 HA] with %hpre
  · iframe H0 HA
  iexists A ++ [x]
  iframe HA
  ipureintro
  have hl : A0.length = A.length := by omega
  have hA0 : A0 = A := by
    rcases hpre with ⟨t, ht⟩ | ⟨t, ht⟩
    · have h1 := congrArg (List.take A.length) ht
      rwa [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
        List.take_append_of_le_length (by omega), List.take_length] at h1
    · have := congrArg List.length ht
      simp only [List.length_append, List.length_singleton] at this
      omega
  subst hA0
  refine ⟨by simp only [List.length_append, List.length_singleton]; push_cast; omega, fun m h1 h2 => ?_⟩
  have e1 : (uint.nat m : Int) = uint.Z m := by simp [uint.nat]
  have e2 : (uint.nat γ.ai0 : Int) = uint.Z γ.ai0 := by simp [uint.nat]
  by_cases hmi : uint.Z m = uint.Z i
  · have hm : uint.nat m - uint.nat γ.ai0 = (A0 ++ [x]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [hm, List.take_length]
  · have hm : uint.nat m - uint.nat γ.ai0 ≤ A0.length := by omega
    rw [List.take_append_of_le_length hm, hrow m h1 (by omega), hM]

/-- **The row as the apply protocol's bundle** (T10 step 3): `consInv γ (srvImgRowT γr M)`. -/
def srvImgRowT {α : Type} (γ : ServerRaftNames) (M : List EntryModel → α) : TRow GF :=
  ⟨srvImgRow γ M, fun _ _ => inferInstance⟩

@[simp] theorem srvImgRowT_IR {α : Type} (γ : ServerRaftNames) (M : List EntryModel → α) (e p : w64) :
    (srvImgRowT (GF := GF) γ M).IR e p = srvImgRow γ M e p := rfl

end defs

end EtcdGrove
end Perennial
