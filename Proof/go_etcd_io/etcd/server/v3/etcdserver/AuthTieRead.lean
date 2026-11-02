/-
**The read law of the auth history's tie** (H5, 2026-10-29; `notes/decisions.md`, "H5: the auth
history's cap"): a client that froze the auth history at `hs` (`authHistFrozen`, the auth-mode
merge's 5b) and read the store's state `last hs` at the index `k` reads it at every later index
`m` (`authStateAt_setup`).

The store's states are below its cap (`auth.authStateAt_capped`), the cap is the history of a
committed log (the tie, `authHistTie`), whose admin states the frozen view bounds
(`authHistFrozen_prefix`), so every recorded state is in the history the frozen `hs` is the log's
part of (`authHistFrozen_adm`: `hs` is the KV invariant's `admStates` of its log). That history has
no state twice (`srvHist_nodup`), so `last hs` is at one index only, its last: no index after `k`
holds a state.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthTie
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- In a list with no element twice, an index holding the last element is the last index, so no
later index holds anything. -/
theorem nodup_at_last {α : Type _} (l : List α) (hn : l.Nodup) (k m : Nat) (x y : α)
    (hk : l[k]? = some x) (hl : l.getLast? = some x) (hm : l[m]? = some y) (hkm : k ≤ m) :
    k = m := by
  have hkl : k < l.length := (List.getElem?_eq_some_iff.mp hk).1
  have hml : m < l.length := (List.getElem?_eq_some_iff.mp hm).1
  have hlast : l[l.length - 1]? = some x := by
    rw [List.getLast?_eq_getElem?] at hl; exact hl
  have heq : k = l.length - 1 := List.Nodup.eq_of_getElem?_eq hn hkl (hk.trans hlast.symm)
  omega

/-- **The namespaces of the tie's read law** (`authStateAt_setup`): the raft log's invariant, the
KV invariant, the auth history's, the tie's and the auth store's revision invariant. -/
def authTieReadMask : CoPset :=
  ↑srvRaftN ∪ ↑kvN ∪ ↑authHistN ∪ ↑authTieN ∪ ↑(nroot.@"authRev")

/-- A mask holding the read law's namespaces holds each. -/
theorem authTieReadMask_sub (E' : CoPset) (h : authTieReadMask ⊆ E') :
    ↑srvRaftN ⊆ E' ∧ ↑kvN ⊆ E' ∧ ↑authHistN ⊆ E' ∧ ↑authTieN ⊆ E' ∧
      ↑(nroot.@"authRev") ⊆ E' := by
  unfold authTieReadMask at h
  refine ⟨fun p hp => h p ?_, fun p hp => h p ?_, fun p hp => h p ?_, fun p hp => h p ?_,
    fun p hp => h p ?_⟩ <;> simp only [Iris.Std.LawfulSet.mem_union]
  · exact Or.inl (Or.inl (Or.inl (Or.inl hp)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hp)))
  · exact Or.inl (Or.inl (Or.inr hp))
  · exact Or.inl (Or.inr hp)
  · exact Or.inr hp

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A frozen history is the KV invariant's**: `hs` is the admin states of the KV invariant's log
`L` (the view and the invariant's halves agree), whose start's consistent index is at most the
start's applied index. -/
theorem authHistFrozen_adm (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (γz : GName)
    (hs : List auth.AuthState) (E : CoPset) (hE1 : ↑kvN ⊆ E) (hE2 : ↑authHistN ⊆ E) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ authHistFrozen γk γz hs ={E}=∗
      ⌜∃ L, hs = admStates γk st₀ L ∧ uint.Z γk.c0 ≤ uint.Z γ.ai0⌝ := by
  have h2' : (↑authHistN : CoPset) ⊆ E \ ↑kvN := fun p hp => by
    rw [Iris.Std.LawfulSet.mem_diff]
    exact ⟨hE2 p hp, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩
  iintro #Hinv #Hf
  iunfold authHistFrozen at Hf
  icases Hf with ⟨#Hc, #Hmk⟩
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw⟩
  iunfold authHistCell at Hc
  iinv Hc with >Hj Hclose2
  icases Hj with ⟨%hs₀, Hv, Hz⟩
  ihave %Heq : ⌜hs₀ = hs⌝ $$ [Hz]
  · icases Hz with (Hz | #Hz)
    · iexfalso; iapply authHistOpen_mark γz hs₀ hs _ $$ Hz Hmk
    · iapply authHistMark_agree γz hs₀ hs $$ Hz Hmk
  subst Heq
  iunfold authHistView at Hv
  ihave %Ha := monoListAuthOwn_agree γk.hist _ _ hs₀ _ $$ Hv Hh
  imod Hclose2 $$ [Hv] with -
  · inext; iexists hs₀; iunfold authHistView; iframe Hv; iright; iexact Hmk
  imod Hclose $$ [HL Hσ Hh] with -
  · inext; iexists L; iframe HL Hσ Hh Hw; ipureintro; exact Hok
  imodintro
  ipureintro
  exact ⟨L, Ha.2, Hok.2.2.2.1⟩

/-- **The read law** (H5; see the file header): with the auth history frozen at `hs` and the
store's state `last hs` at the index `k`, the store's state at an index `m ≥ k` is `last hs`. -/
theorem authStateAt_setup (E : apply.AEnv GF) (ρ : ReadNames) (γa : auth.AuthNames) (γz : GName)
    (hs : List auth.AuthState) (k m : Nat) (st : auth.AuthState) (E' : CoPset)
    (hγa : E.authMode = .on γa) (hE : authTieReadMask ⊆ E') :
    srvRaftLogInv ρ.raft ∗ kvInvOn ρ.raft ρ.kv srvAuthSt0 ∗ authHistTie E ρ srvAuthSt0 ∗
        authHistFrozen ρ.kv γz hs ∗ auth.authStateAt γa k (hs.getLastD srvAuthSt0) ∗ ⌜k ≤ m⌝ ∗
        auth.authStateAt γa m st ={E'}=∗
      ⌜st = hs.getLastD srvAuthSt0⌝ := by
  obtain ⟨hE0, hE1, hE2, hE3, hE4⟩ := authTieReadMask_sub E' hE
  unfold authHistTie
  rw [hγa]
  iintro ⟨#Hrl, #Hkv, ⟨⟨%stl, %R, #Hinv⟩, #Htinv⟩, #Hfz, #Hk, %hkm, #Hm⟩
  imod auth.authStateAt_capped stl R γa m st E' hE4 $$ [Hinv Hm] with ⟨%C, #HC, %hC⟩
  · isplitl []
    · iexact Hinv
    · iexact Hm
  imod auth.authStateAt_capped stl R γa k _ E' hE4 $$ [Hinv Hk] with ⟨%C', #HC', %hC'⟩
  · isplitl []
    · iexact Hinv
    · iexact Hk
  iinv Htinv with Hi Hclose
  icases Hi with ⟨%A₀, >#HA₀, >Hcap⟩
  ihave %p1 := capAuth_lb_prefixW γa _ C $$ Hcap HC
  ihave %p2 := capAuth_lb_prefixW γa _ C' $$ Hcap HC'
  imod Hclose $$ [Hcap] with -
  · inext; iexists A₀; iframe HA₀; iexact Hcap
  imod srvReqLogLb_of_rlogLb ρ.raft E' hE0 A₀ $$ Hrl HA₀ with ⟨%L₀, #HL₀, %heqv⟩
  imod authHistLb_of_reqLogLb ρ.raft ρ.kv srvAuthSt0 L₀ E' hE1 $$ Hkv HL₀ with #Hlb
  imod authHistFrozen_prefix ρ.kv γz hs _ E' hE2 $$ Hfz Hlb with %hp
  imod authHistFrozen_adm ρ.raft ρ.kv srvAuthSt0 γz hs E' hE1 hE2 $$ Hkv Hfz with %Hadm
  obtain ⟨L, hL, hc⟩ := Hadm
  imodintro
  ipureintro
  -- the history `P` of the KV invariant's log, of which the cap's history is a prefix
  have he : admStates ρ.kv srvAuthSt0 A₀ = admStates ρ.kv srvAuthSt0 L₀ :=
    admStates_eqv ρ.raft ρ.kv srvAuthSt0 A₀ L₀ heqv hc
  have hP : auth.bootState :: admStates ρ.kv srvAuthSt0 A₀ <+: srvHist ρ.kv L := by
    rw [he]; unfold srvHist
    rw [show auth.bump auth.bootState = srvAuthSt0 from rfl, ← hL]
    exact (List.prefix_cons_inj _).mpr hp
  have hCP : C <+: srvHist ρ.kv L := p1.trans hP
  have hCP' : C' <+: srvHist ρ.kv L := p2.trans hP
  have hpre : ∀ (D : List auth.AuthState) (i : Nat) (x : auth.AuthState), D <+: srvHist ρ.kv L →
      D[i]? = some x → (srvHist ρ.kv L)[i]? = some x := by
    intro D i x hD hx
    obtain ⟨t, ht⟩ := hD
    rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]
    exact hx
  have hS : srvHist ρ.kv L = auth.bootState :: hs := by rw [hL]; rfl
  have hne : hs ≠ [] := by rw [hL]; exact admStates_ne_nil _ _ _
  have hlast : (srvHist ρ.kv L).getLast? = some (hs.getLastD srvAuthSt0) := by
    rw [hS, List.getLast?_cons, List.getLastD_eq_getLast?]
    cases h : hs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
    | some x => rfl
  have hm' := hpre C m st hCP hC
  have hk' := hpre C' k _ hCP' hC'
  have hkm' := nodup_at_last _ (srvHist_nodup ρ.kv L) k m _ st hk' hlast hm' hkm
  subst hkm'
  rw [hk'] at hm'
  exact (Option.some.inj hm').symm

end ghost

end EtcdGrove
end Perennial
