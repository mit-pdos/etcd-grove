/-
The definitions, specs and lemmas of `QuorumMaps.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.quorum

theorem w32n_inj (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (h : w32n a = w32n b) :
    a = b := by
  unfold w32n at h
  have h1 : sint.Z (W32 (a : Int)) = a := sint_W32 _ (by omega) (by omega)
  have h2 : sint.Z (W32 (b : Int)) = b := sint_W32 _ (by omega) (by omega)
  rw [h] at h1; omega

theorem nodup_map_w32n (s : List Nat) (hnd : s.Nodup) (hs : ∀ x ∈ s, x < 2 ^ 31) :
    (s.map w32n).Nodup := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd ⊢
    refine ⟨?_, ih hnd.2 (fun x hx => hs x (by simp [hx]))⟩
    rintro ⟨b, hb, h⟩
    have := w32n_inj b a (hs b (by simp [hb])) (hs a (by simp)) h
    subst this; exact hnd.1 hb

theorem qRepr_size (m : GMap w32 Unit) (s : List Nat) (h : qRepr m s) (hnd : s.Nodup)
    (hs : ∀ x ∈ s, x < 2 ^ 31) : GMap.size m = s.length := by
  rw [GMap.size_eq_length m (s.map w32n) (nodup_map_w32n s hnd hs)]
  · simp
  intro k
  rw [h k]
  split <;> simp_all

end replica.quorum

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

set_option goose.wp.extras true

open replica.quorum

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

end
