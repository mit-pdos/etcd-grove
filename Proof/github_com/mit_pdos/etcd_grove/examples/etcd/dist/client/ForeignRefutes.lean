/-
**`foreign`'s TimeToLive check refuted at the view** (F7 (fork), option (3), 2026-11-26; replaces the hypothesis
`foreignReads.law` of F7 stage S5, `notes/etcd-dist-f7-fork.md`).

`foreign(ucli, "u", lz, zKey)` and `foreign(vcli, "v", lu, aKey)` (`examples/etcd/dist/client/authlease.go`) ask a
user about a lease of another principal (`Lz`, root's, holding `z/lease`; `Lu`, u's, holding `a/lease`): its
`TimeToLive(id, WithAttachedKeys())` panics only if it returns the key the user may not read. `foreign.spec` takes
the caller's refutation of member `mid`'s read check granting the principal that key at a published index past
`n₀`. Here it is proved from the frozen set-up: from the barrier floor's index `m` on, member `mid` records only
`setupSt r` (`authFloorD_frozen`), at which auth is enabled (the check's disabled arm), neither u nor v is an admin
(`etcd_authlease.not_adminOk_setupSt`), u may not read `z/lease` (outside `[a, b)`, `not_inRangeK_zK`) and v reads
nothing (`etcd_authlease.not_permitted_setupSt`). Nothing of the lessor is needed: the claim is about the
returned keys, not the lease's attachments. (v's own lease, `ownLease`, is no lease of this check: `foreign` asks
v about `Lu`.) Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthCell
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthFrozenFloor
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseRefusalFacts

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcd_dist.authd etcd_authlease

section refutes
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- See the file header: u's check at `z/lease`, v's at `a/lease`, from the frozen floor of member `mid`. -/
theorem foreign_refutesD (Γ : DistView) (γR : ServerRaftNames) (mid : w64) (Lset : List EntryModel) (m : Nat)
    (γz : GName) (hs : List auth.AuthState) (r : Nat) (hadm : admStates Γ.kv srvAuthSt0 Lset = hs)
    (hst : srvAuthAtLog Γ.kv srvAuthSt0 Lset = etcd_auth.setupSt r) (P : Option GoString) (k : GoString)
    (hP : (P = some go!"u" ∧ k = zK) ∨ (P = some go!"v" ∧ k = aK)) :
    ⊢ kvInvOn (GF := GF) γR Γ.kv srvAuthSt0 -∗ authHistFrozen Γ.kv γz hs -∗ authFloorD Γ γR mid Lset m -∗
      □ (∀ n : Nat, ⌜m ≤ n⌝ -∗
          leaseCheckD (Γ.au mid) P n
            (fun info => auth.permVerdictFrom (.on (Γ.au mid)) n info k [] .read GoInterface.nil) ={⊤}=∗
          False) := by
  iintro #Hk #Hz #Hf
  ihave ⟨%i, %hi, #Hfz⟩ := authFloorD_frozen Γ γR mid Lset Lset m γz hs r (List.prefix_refl _) hadm hst ⊤
    CoPset.subseteq_top $$ Hk Hz Hf
  iintro !> %n %hn Hc
  simp only [leaseCheckD, auth.enabledVerdictFrom, auth.adminVerdictFrom, auth.permVerdictFrom]
  icases Hc with (⟨%j, %st, #Hst, %Hj⟩ | ⟨%info, %Hp, (⟨%j, %st, #Hst, %Hj⟩ | ⟨⟨%j, %st, #Hst, %Hj⟩, -, -⟩)⟩)
  · imod Hfz $$ %j %st [] Hst with %Heq
    · ipureintro; omega
    subst Heq
    simp [etcd_auth.setupSt] at Hj
  · imod Hfz $$ %j %st [] Hst with %Heq
    · ipureintro; omega
    subst Heq
    have hu : info.Username' = go!"u" ∨ info.Username' = go!"v" := by
      rcases hP with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl (Option.some.inj Hp).symm
      · exact Or.inr (Option.some.inj Hp).symm
    exact absurd (Hj.2 trivial) (not_adminOk_setupSt r info hu)
  · imod Hfz $$ %j %st [] Hst with %Heq
    · ipureintro; omega
    subst Heq
    rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd (Hj.2 trivial) (not_permitted_setupSt r info zK (by decide)
        (Or.inl ⟨(Option.some.inj Hp).symm, not_inRangeK_zK⟩))
    · exact absurd (Hj.2 trivial) (not_permitted_setupSt r info aK (by decide)
        (Or.inr (Option.some.inj Hp).symm))

end refutes

end etcd_dist_client
end EtcdGrove
end Perennial
