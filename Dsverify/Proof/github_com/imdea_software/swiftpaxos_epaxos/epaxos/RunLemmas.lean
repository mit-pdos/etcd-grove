/-
Facts the run loop uses: the peer order step at each lock acquisition (`lock_peerOrder`: the
model's `peerOrder` step to the order `ComputeClosestPeers` fixed, so that the handlers see
`σ.peerOrder` equal to the heap's `PreferredPeerOrder`), the commit's outputs (no send, no
broadcast).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RunSpec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

/-- The order `ComputeClosestPeers` leaves (a permutation of the ids, `i` last) is one the model
accepts. -/
theorem peerOrderOk_of (i : Nat) (ord : List w32) (hi : i < nR)
    (hp : (ord.map (fun x => sint.nat x)).Perm (List.range nR))
    (hl : ord[nR - 1]? = some (W32 (i : Int))) :
    Sys.peerOrderOk i (ord.map (fun x => sint.nat x)) := by
  obtain ⟨o, ho⟩ : ∃ o, o = ord.map (fun x => sint.nat x) := ⟨_, rfl⟩
  rw [← ho] at hp ⊢
  have hlen : o.length = nR := by rw [hp.length_eq]; simp
  have hlast : o[nR - 1]? = some i := by
    rw [ho, List.getElem?_map, hl]
    simp only [Option.map_some, Option.some.injEq]
    simp only [nR] at hi
    have : sint.Z (W32 (i : Int)) = (i : Int) := by word
    show (sint.Z (W32 (i : Int))).toNat = i
    omega
  refine ⟨hlen, ?_⟩
  have hd : o.drop (nR - 1) = [i] := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_drop]
    rcases j with _ | j
    · simpa using hlast
    · have : o.length ≤ nR - 1 + (j + 1) := by rw [hlen]; simp only [nR]; omega
      simp [List.getElem?_eq_none this]
  have hsplit : o = o.take (nR - 1) ++ [i] := by
    have := List.take_append_drop (nR - 1) o
    rw [hd] at this; exact this.symm
  have h1 : (o.take (nR - 1) ++ [i]).Perm (List.range nR) := hsplit ▸ hp
  have h2 : (i :: o.take (nR - 1)).Perm (List.range nR) :=
    (List.perm_append_comm.trans h1 : _)
  have h3 := h2.erase i
  rw [List.erase_cons_head, List.Nodup.erase_eq_filter List.nodup_range] at h3
  refine h3.trans ?_
  apply List.Perm.of_eq
  congr 1; funext x; by_cases h : x = i
  · subst h; simp
  · have h' : ¬ i = x := fun e => h e.symm
    simp [h, h']

/-- A list of outputs with no send and no broadcast. -/
def NoSend (outs : List Out) : Prop :=
  ∀ o ∈ outs, (∃ p, o = .repropose p) ∨ (∃ e, o = .ev e)

theorem sendsTo_noSend (outs : List Out) (h : NoSend outs) (to : Nat) : sendsTo outs to = [] := by
  unfold sendsTo
  rw [List.filterMap_eq_nil_iff]
  intro o ho
  rcases h o ho with ⟨p, rfl⟩ | ⟨e, rfl⟩ <;> rfl

theorem pendOf_noSend (outs : List Out) (h : NoSend outs) : pendOf outs = none := by
  unfold pendOf
  suffices ∀ acc, (∀ o ∈ outs, (∃ p, o = .repropose p) ∨ (∃ e, o = .ev e)) →
      outs.foldl (fun acc o => match o with | .bcast b => b.norm | _ => acc) acc = acc by
    exact this none h
  intro acc h
  induction outs generalizing acc with
  | nil => rfl
  | cons o os ih =>
    simp only [List.foldl_cons]
    rcases h o (List.mem_cons_self) with ⟨p, rfl⟩ | ⟨e, rfl⟩ <;>
      exact ih (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')) _ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))

theorem hCommit_noSend (σ : RState) (m : Commit) : NoSend (hCommit σ m).2 := by
  by_cases h1 : stGe (commitW0 σ m).status stCOMMITTED = true ∨
      m.ballot.slt (commitW0 σ m).bal = true
  · rw [hCommit_early σ m h1]; intro o ho; simp at ho
  · have h1a : stGe (commitW0 σ m).status stCOMMITTED = false := by
      cases h : stGe (commitW0 σ m).status stCOMMITTED <;> simp_all
    have h1b : m.ballot.slt (commitW0 σ m).bal = false := by
      cases h : m.ballot.slt (commitW0 σ m).bal <;> simp_all
    rw [hCommit_main σ m h1a h1b]
    intro o ho
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with ho | ho | ho
    · left
      unfold commitRp at ho
      split at ho
      · split at ho
        · split at ho
          · simp only [List.mem_map] at ho
            obtain ⟨p, -, rfl⟩ := ho; exact ⟨p, rfl⟩
          · simp at ho
        · simp at ho
      · simp at ho
    · right; exact ⟨_, ho⟩
    · right; exact ⟨_, ho⟩

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- The handler's outputs with no send and no broadcast: idle again, and the outputs' own
resources. -/
theorem outsOk_noSend (γ : EpNames) (i : Nat) (outs : List Out) (h : NoSend outs) :
    outsOk (GF := GF) γ i outs ⊢ repIdle γ i ∗ [∗list] o ∈ outs, outOk γ i o := by
  unfold outsOk repIdle
  rw [pendOf_noSend outs h]
  simp only [sendsTo_noSend outs h]
  iintro ⟨Hob, Hp, Hc, Ho⟩
  iframe

/-- At a lock acquisition of the run loop: the model's `peerOrder` step to the order
`ComputeClosestPeers` fixed (`prefOrder`), and `ownRep`'s peer order piece is that order. -/
theorem lock_peerOrder (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (ord : List w32)
    (σ : RState) (hi : i < nR) (hL : L.length = nR) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ efld r go!"Replica" ↦□ rr -∗ prefOrder rr i L ord -∗
      ownRep γ i r σ -∗ repFrag γ i σ -∗ £ 1 ={⊤}=∗
      ownRep γ i r { σ with peerOrder := ord.map (fun x => sint.nat x) } ∗
      repFrag γ i { σ with peerOrder := ord.map (fun x => sint.nat x) } := by
  iintro #Hinv #Hrr #Hpo Hrep Hf Hlc
  ihave %Hp : ⌜(ord.map (fun x => sint.nat x)).Perm (List.range L.length) ∧
      ord[L.length - 1]? = some (W32 i)⌝ $$ [Hpo]
  · unfold prefOrder
    icases Hpo with ⟨%po, -, -, %H⟩
    ipureintro; exact ⟨H.1, H.2.1⟩
  rw [hL] at Hp
  have hok := peerOrderOk_of i ord hi Hp.1 Hp.2
  imod ep_peerOrder γ ⊤ i σ _ (by solve_ndisj) hi hok $$ Hinv Hf Hlc with Hf
  imodintro
  iframe Hf
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, HlS, HlP, HmaxSeq, Hlead, Hmrb,
    Hstore, -⟩
  iframe
  isplitr
  · ipureintro; exact Hib
  isplitr
  · ipureintro; exact Hcb
  unfold repPeer
  iright
  iexists rr, L, ord
  iframe Hrr Hpo
  ipureintro; exact ⟨hL, rfl⟩

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
