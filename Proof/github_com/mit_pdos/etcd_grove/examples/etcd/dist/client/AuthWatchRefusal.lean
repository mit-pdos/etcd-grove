/-
**The principals' refused watch across machines** (F7 stage S6, `notes/etcd-dist-f7.md`, "Handoff RA-1"; how
`auth.Work`'s watch of `c/` discharges `WatchOn_dist`, the lead's post on #50, 2026-11-26). Lean-first (no Rocq
counterpart).

- `streamKeyOf_single_only`: metadata with the stream key of a one-entry map `{k: [v]}` has no value under any
  other key (the printed `map[k:[v]]` has no space, so the other map has one key, which is `k`:
  `streamKeyOf_single`). The untrusted variant of `streamKeyOf_single` `WatchOn_dist`'s `outTokOkS` needs for
  `bad`: no context of its stream key sends `authorization`.
- `outTokOkS_reqMd`: `WatchOn_dist`'s premise `outTokOkS P (reqMd who)` for an anonymous principal (and for
  any principal but `bad`): `bad`'s stream key's metadata carries `token: [badtoken]` and nothing else, and
  `badtoken` has no simple token's shape.
- `watchCheckedD_c_refuted`: a response with events of a principal's watch of `[c/, c0)` is refuted at the
  frozen set-up state: its `watchCheckedD` names a committed prefix `L ⊒ L₀ ⊒ Lset`, whose auth state is the
  set-up's (`srvAuthAtLog_frozen`), where auth is on and no user a principal of the program may be bound to
  reads `c/` (`etcd_auth.not_granted_c`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthFrozenFloor
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchOnViewDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkAuth

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcd_dist.authd

section pure
variable [GooseExts]

/-- Every key a Go map's sorted keys omit has no entry. -/
theorem mdSortedKeys_mem (f : GoString → Option (List GoString)) (ks : List GoString)
    (h : mdSortedKeys f = some ks) (k : GoString) (hk : (f k).isSome) : k ∈ ks := by
  unfold mdSortedKeys at h
  split at h
  · rename_i hex
    simp only [Option.some.injEq] at h
    subst h
    rw [List.mem_mergeSort, List.mem_eraseDups, List.mem_filter]
    exact ⟨Classical.choose_spec hex k hk, by simpa using hk⟩
  · simp at h

/-- **Metadata with a one-entry map's stream key has no other key** (see the file header): under
`streamKeyOf_single`'s premises, no value under any key but `k`. -/
theorem streamKeyOf_single_only (m : GrpcMd) (k v : GoString) (hk : metadata.lowerKey k)
    (hs : ∀ b ∈ k ++ v, b ∉ [W8 32, W8 58, W8 91, W8 93]) (hv : v ≠ go!"")
    (h : streamKeyOf m = streamKeyOf (metadata.mdAdd none k v)) (k' : GoString) (hne : k' ≠ k) :
    metadata.mdVals m k' = [] := by
  have hk1 := streamKeyOf_single m k v hk hs hv h
  have hadd : metadata.mdAdd none k v = some (fun k' => if k' = k then some [v] else none) := by
    unfold metadata.mdAdd; congr 1
  have hE : streamKeyOf (metadata.mdAdd none k v) =
      go!"map[" ++ (k ++ go!":" ++ (go!"[" ++ v ++ go!"]")) ++ go!"]" := by
    rw [hadd]; simp [streamKeyOf, mdSortedKeys_single, fmtMdEntry, fmtStrSlice]
  rw [hE] at h
  have hkv : ∀ b ∈ k, b ≠ W8 32 ∧ b ≠ W8 58 := fun b hb => by
    have := hs b (List.mem_append_left _ hb); simp at this; exact ⟨this.1, this.2.1⟩
  have hvv : ∀ b ∈ v, b ≠ W8 32 ∧ b ≠ W8 58 := fun b hb => by
    have := hs b (List.mem_append_right _ hb); simp at this; exact ⟨this.1, this.2.1⟩
  cases m with
  | none => simp [streamKeyOf] at h
  | some f =>
    cases hks : mdSortedKeys f with
    | none =>
      simp only [streamKeyOf, hks] at h
      have := congrArg List.length h
      simp at this
      have : v.length ≠ 0 := by simpa using hv
      omega
    | some ks =>
      simp only [streamKeyOf, hks] at h
      have h' := List.append_cancel_left (List.append_cancel_right h)
      have hns : noSp ([W8 32].intercalate (ks.map (fmtMdEntry f))) := by
        rw [h']; unfold noSp; intro hm
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with ((hm | hm) | (hm | hm) | hm)
        · exact (hkv _ hm).1 rfl
        · exact absurd hm (by decide)
        · exact absurd hm (by decide)
        · exact (hvv _ hm).1 rfl
        · exact absurd hm (by decide)
      have hlen := intercalate_sp_noSp hns
      rw [List.length_map] at hlen
      have hfk : (f k).isSome := by
        simp only [metadata.mdVals, Option.bind_some] at hk1
        cases hf : f k with
        | none => rw [hf] at hk1; simp at hk1
        | some _ => rfl
      have hkm := mdSortedKeys_mem f ks hks k hfk
      simp only [metadata.mdVals, Option.bind_some]
      cases hf : f k' with
      | none => rfl
      | some vs =>
        exfalso
        have hk'm := mdSortedKeys_mem f ks hks k' (by simp [hf])
        match ks, hlen, hkm, hk'm with
        | [a], _, h1, h2 =>
          simp only [List.mem_singleton] at h1 h2
          exact hne (h2.trans h1.symm)

/-- **`WatchOn_dist`'s token premise for a principal's watch context** (see the file header): `reqMd who` (no
metadata, or `bad`'s `token: badtoken`) and every metadata of its stream key send no issued token, for an
anonymous principal, and for any principal when `who ≠ "bad"`. -/
theorem outTokOkS_reqMd (P : Option GoString) (who : GoString) (h : who = go!"bad" → P = none) :
    outTokOkS P (reqMd who) := by
  by_cases hw : who = go!"bad"
  · intro m hm
    have hr : reqMd who = metadata.mdAdd none go!"token" etcd_auth.badToken := by
      unfold reqMd; rw [if_pos hw]
    rw [hr] at hm
    have hk : metadata.lowerKey go!"token" := by unfold metadata.lowerKey; decide
    have hs : ∀ b ∈ go!"token" ++ etcd_auth.badToken, b ∉ [W8 32, W8 58, W8 91, W8 93] := by decide
    have hv : etcd_auth.badToken ≠ go!"" := by decide
    have htok := streamKeyOf_single m _ _ hk hs hv hm
    have hauth := streamKeyOf_single_only m _ _ hk hs hv hm go!"authorization" (by decide)
    right
    refine ⟨h hw, ?_⟩
    intro k hk' t ht hsh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
    rcases hk' with rfl | rfl
    · rw [htok, List.mem_singleton] at ht
      subst ht
      rw [etcd_auth.trimPrefix_badToken] at hsh
      obtain ⟨pre, idx, he, -⟩ := hsh
      exact etcd_auth.simpleTok_ne_badToken pre idx he.symm
    · rw [hauth] at ht; simp at ht
  · have hr : reqMd who = none := by unfold reqMd; rw [if_neg hw]
    rw [hr]
    exact outTokOkS_none P

/-- A user a principal of the program (`none`, `u`'s or `v`'s name) may be bound to is one of its
(`etcd_auth.akUser`). -/
theorem akUser_of_userOk (P : Option GoString) (user : GoString)
    (hP : P = none ∨ P = some go!"u" ∨ P = some go!"v") (hu : userOk P user) :
    ∃ who, etcd_auth.akUser who user := by
  rcases hu with h0 | hs
  · exact ⟨go!"u", Or.inl h0⟩
  · rcases hP with rfl | rfl | rfl
    · cases hs
    · cases hs; exact ⟨go!"u", Or.inr ⟨rfl, Or.inl rfl⟩⟩
    · cases hs; exact ⟨go!"v", Or.inr ⟨rfl, Or.inr rfl⟩⟩

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A principal's watch of `[c/, c0)` has no checked create** (see the file header): after the set-up froze
the history at `hs` (a committed prefix `Lset ⊑ L₀`, auth state `setupSt r`), `watchCheckedD` for a principal
of the program refutes. -/
theorem watchCheckedD_c_refuted [NetProtoGS] (eps : List GoString) (Γ : DistView) (γR : ServerRaftNames)
    (P : Option GoString) (L₀ Lset : List EntryModel) (γz : GName) (hs : List auth.AuthState) (r : Nat)
    (hLs : Lset <+: L₀) (hadm : admStates Γ.kv srvAuthSt0 Lset = hs)
    (hst : srvAuthAtLog Γ.kv srvAuthSt0 Lset = etcd_auth.setupSt r)
    (hP : P = none ∨ P = some go!"u" ∨ P = some go!"v") (E : CoPset) (hE : authTieReadMask ⊆ E) :
    ⊢ kvInvOn (GF := GF) γR Γ.kv srvAuthSt0 -∗ authHistFrozen Γ.kv γz hs -∗
      watchCheckedD eps Γ γR P L₀ go!"c/" go!"c0" ={E}=∗ False := by
  obtain ⟨-, hE1, hE2, -, -⟩ := authTieReadMask_sub E hE
  iintro #Hinv #Hfz #Hw
  iunfold watchCheckedD at Hw
  icases Hw with ⟨%mid, %info, %L, -, #HL, %Hc⟩
  imod authHistLb_of_reqLogLb γR Γ.kv srvAuthSt0 L E hE1 $$ Hinv HL with #Hlb
  imod authHistFrozen_prefix Γ.kv γz hs _ E hE2 $$ Hfz Hlb with %hp
  obtain ⟨hu, hL, hperm⟩ := Hc
  rw [srvAuthAtLog_frozen Γ.kv Lset L₀ L hs hLs hL hadm hp, hst] at hperm
  obtain ⟨who, hwho⟩ := akUser_of_userOk P _ hP hu
  have hkey : apply.watchKey go!"c/" = go!"c/" := by unfold apply.watchKey; decide
  rw [hkey] at hperm
  rcases hperm with hen | hg
  · simp [etcd_auth.setupSt] at hen
  · exact absurd hg (etcd_auth.not_granted_c r who _ _ hwho)

end ghost

end etcd_dist_client
end EtcdGrove
end Perennial
