/-
**The barrier after the set-up, at a member other than the set-up's** (the auth3 Scope's A2, §3,
2026-11-14; Q2's route (ii), decided by etcd-grove-81). Lean-first (no Rocq counterpart).

authkv's checks at a member run under `akAuthFixed γa ρ Lset n` at that member's names; its first
row, a lower bound `n` of the member's published auth index at which the store records the set-up's
last state, is what a watch's creation is checked at (a watch has no read index). `SetUp`'s post
gives it at the member that took the set-up's requests only. At another member, a linearizable read
gives it (`akAuthFixed_barrier`): `SetUp`'s post also gives a committed raft log `Lc` whose auth
state is the set-up's last one (`AuthEnable`'s entry and what precedes it); a read at the member at
the bound `ai0 + |Lc|` (`committedAtLeast`'s second disjunct, L2) checks at a published index `m`
(`rangeAuthed`'s `authPubLbM`, L1) at which the member's store recorded the auth state of a
committed log `A` reaching the bound (`authFloorAt`), so `A` extends `Lc`; with the auth history
frozen at the set-up's `hs` (`authHistFrozen`), `A`'s history is `hs`, and its auth state the set-up's
last one.

**The members' names** (`etcdstart.sameCluster`, from `alloc3On`): the cluster's predicates read
only the KV names' state, start and history fields and the raft names' committed and requested
logs, so the set-up's facts at member 1's names hold at every member's (`*_same`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.WorkEnv
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3On
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthTie

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth3

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver etcd_auth

section pure
variable [GooseExts]

/-- `admStates` reads the KV names' start fields only. -/
theorem admStates_same (ρ ρ' : ReqNames) (h : etcdstart.sameCluster ρ ρ') (st₀ : auth.AuthState)
    (L : List EntryModel) : admStates ρ'.kv st₀ L = admStates ρ.kv st₀ L := by
  obtain ⟨-, h2, h3, h4, -⟩ := h
  unfold admStates; rw [h2, h3, h4]

/-- `srvAuthAtLog` reads the KV names' start fields only. -/
theorem srvAuthAtLog_same (ρ ρ' : ReqNames) (h : etcdstart.sameCluster ρ ρ') (st₀ : auth.AuthState)
    (L : List EntryModel) : srvAuthAtLog ρ'.kv st₀ L = srvAuthAtLog ρ.kv st₀ L := by
  obtain ⟨-, h2, h3, h4, -⟩ := h
  unfold srvAuthAtLog; rw [h2, h3, h4]

/-- A list with no element twice: a prefix of it ending at its last element is all of it, and so is
every list between the two. -/
theorem prefix_between_last {α : Type} (l h1 h2 : List α) (hn : l.Nodup) (p1 : h1 <+: h2)
    (p2 : h2 <+: l) (hl : h1.getLast? = l.getLast?) (h1n : h1 ≠ []) : h2 = l := by
  have he : h1 = l := prefix_eq_of_last l h1 l hn (p1.trans p2) (List.prefix_refl l) hl h1n
  subst he
  exact List.IsPrefix.eq_of_length p2 (Nat.le_antisymm p2.length_le p1.length_le)

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A committed log at one member's raft names is one at another's of the cluster. -/
theorem srvRLogLb_same (ρ ρ' : ReqNames) (h : etcdstart.sameCluster ρ ρ') (L : List EntryModel) :
    srvRLogLb (GF := GF) ρ.raft L ⊢ srvRLogLb ρ'.raft L := by
  obtain ⟨-, -, -, -, -, h6, -, h8, h9⟩ := h
  unfold srvRLogLb srvLE
  rw [h6, h8, h9]

/-- A requested log at one member's raft names is one at another's of the cluster. -/
theorem srvReqLogLb_same (ρ ρ' : ReqNames) (h : etcdstart.sameCluster ρ ρ') (L : List EntryModel) :
    srvReqLogLb (GF := GF) ρ.raft L ⊢ srvReqLogLb ρ'.raft L := by
  obtain ⟨-, -, -, -, -, -, h7, -, -⟩ := h
  unfold srvReqLogLb
  rw [h7]

/-- The auth history frozen at one member's KV names is frozen at another's of the cluster. -/
theorem authHistFrozen_same (ρ ρ' : ReqNames) (h : etcdstart.sameCluster ρ ρ') (γz : GName)
    (hs : List auth.AuthState) :
    authHistFrozen (GF := GF) ρ.kv γz hs ⊢ authHistFrozen ρ'.kv γz hs := by
  obtain ⟨-, -, -, -, h5, -⟩ := h
  unfold authHistFrozen authHistCell authHistView
  rw [h5]

/-- The history invariant at one member's KV names is the one at another's of the cluster. -/
theorem akHistInv_same (ρ ρ' : ReqNames) (h : etcdstart.sameCluster ρ ρ') :
    akHistInv (GF := GF) ρ.kv ⊢ akHistInv ρ'.kv := by
  obtain ⟨h1, -⟩ := h
  unfold akHistInv etcdKV
  rw [h1]

/-- **The barrier** (see the file header): at the member `s` (environment `E` at the auth names
`γa`, read names `ρ.rd`), the set-up's facts (at its own names, `*_same`) and a linearizable read's
check at the bound `c = ai0 + |Lc|` give the auth state fixed after the set-up at the member. -/
theorem akAuthFixed_barrier (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ρ : ReqNames)
    (γz : GName) (hs : List auth.AuthState) (Lset Lc : List EntryModel) (r n : Nat) (c : w64)
    (tok : Option GoString) (o : OpFull) (hγa : E.authMode = .on γa)
    (hser : o.base.serializable = false)
    (hc : uint.Z c = uint.Z ρ.raft.ai0 + Lc.length) :
    isServerReadM true s E ρ.rd ∗ authHistFrozen ρ.kv γz hs ∗ srvReqLogLb ρ.raft Lset ∗
        ⌜admStates ρ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog ρ.kv srvAuthSt0 Lset = setupSt r⌝ ∗
        srvRLogLb ρ.raft Lc ∗ ⌜srvAuthAtLog ρ.kv srvAuthSt0 Lc = setupSt r⌝ ∗
        v3rpc.rangeAuthed (srvTLSId s) E ρ.rd c n tok o ⊢
      |={⊤}=> ∃ i : Nat, akAuthFixed γa ρ Lset i := by
  rw [v3rpc.rangeAuthed, hγa, hser]
  simp only [auth.authPubLbM, authFloorAt, Bool.false_eq_true, ↓reduceIte]
  iintro ⟨#Hrd, #Hfz, #HLs, %Hh, #HLc, %HLcst, ⟨%info, %m, %Hnm, -, -, #Hpub, %A, %i, #HA, %HAi,
    #Hst⟩⟩
  ihave ⟨#Hrl, #Hkv, #Htie⟩ := isServerReadM_tie s E ρ.rd $$ Hrd
  -- `A` extends `Lc`: committed logs are comparable, and `A` is at least as long
  ihave %Hcmp := srvRLogLb_prefix ρ.raft Lc A $$ [HLc HA]
  · iframe HLc HA
  have hLcA : Lc <+: A := by
    rcases Hcmp with h | h
    · exact h
    · have hc' : uint.Z c = uint.Z ρ.rd.raft.ai0 + Lc.length := hc
      have hl : A.length = Lc.length := Nat.le_antisymm h.length_le (by omega)
      rw [h.eq_of_length hl]; exact List.prefix_refl _
  -- `A`'s history is a prefix of the frozen `hs` (through the requested log it is equivalent to)
  have hE0 : (↑srvRaftN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
  have hE1 : (↑kvN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
  have hE2 : (↑authHistN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
  imod srvReqLogLb_of_rlogLb ρ.raft ⊤ hE0 A $$ Hrl HA with ⟨%L₀, #HL₀, %heqv⟩
  imod authHistLb_of_reqLogLb ρ.raft ρ.kv srvAuthSt0 L₀ ⊤ hE1 $$ Hkv HL₀ with #Hlb
  imod authHistFrozen_prefix ρ.kv γz hs _ ⊤ hE2 $$ Hfz Hlb with %hp
  imod authHistFrozen_adm ρ.raft ρ.kv srvAuthSt0 γz hs ⊤ hE1 hE2 $$ Hkv Hfz with %Hadm
  obtain ⟨L, hL, hc0⟩ := Hadm
  have heA : admStates ρ.kv srvAuthSt0 A = admStates ρ.kv srvAuthSt0 L₀ :=
    admStates_eqv ρ.raft ρ.kv srvAuthSt0 A L₀ heqv hc0
  -- `hs` has no state twice, ends at `setupSt r`, as `Lc`'s history does
  have hn : hs.Nodup := by
    have h := srvHist_nodup ρ.kv L
    unfold srvHist at h
    rw [show auth.bump auth.bootState = srvAuthSt0 from rfl, ← hL] at h
    exact (List.nodup_cons.mp h).2
  have hlast : ∀ L' : List EntryModel,
      (admStates ρ.kv srvAuthSt0 L').getLast? = some (srvAuthAtLog ρ.kv srvAuthSt0 L') := by
    intro L'
    have hne := admStates_ne_nil ρ.kv srvAuthSt0 L'
    rw [← admStates_getLastD ρ.kv srvAuthSt0 L' srvAuthSt0, List.getLastD_eq_getLast?]
    cases h : (admStates ρ.kv srvAuthSt0 L').getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
    | some x => rfl
  have hAeq : admStates ρ.kv srvAuthSt0 A = hs := by
    refine prefix_between_last hs (admStates ρ.kv srvAuthSt0 Lc) _ hn
      (admStates_prefix ρ.kv srvAuthSt0 Lc A hLcA) (by rw [heA]; exact hp) ?_
      (admStates_ne_nil _ _ _)
    rw [hlast Lc, ← Hh.1, hlast Lset, HLcst, Hh.2]
  have hAst : srvAuthAtLog ρ.kv srvAuthSt0 A = setupSt r := by
    rw [← admStates_getLastD ρ.kv srvAuthSt0 A srvAuthSt0, hAeq, ← Hh.1, admStates_getLastD, Hh.2]
  ihave #Hst' : auth.authStateAt γa i (setupSt r) $$ []
  · rw [← hAst]; unfold srvAuthAtLog; iexact Hst
  ihave #Hpub' := auth.authPubLb_le γa i HAi.2 $$ Hpub
  imodintro
  iexists i
  iapply akAuthFixed_alloc s E γa ρ γz hs Lset i r hγa
  iframe Hrd Hfz HLs Hpub' Hst'
  ipureintro; exact Hh

end ghost

end etcd_auth3
end EtcdGrove
end Perennial
