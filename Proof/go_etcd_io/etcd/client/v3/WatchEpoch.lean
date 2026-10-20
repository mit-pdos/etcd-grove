/-
**`run`'s epochs** (D24, `notes/decisions.md`): one per gRPC stream it opened, in a mono list
(`WgsPrm.γep`), each with its first position on `respc` and its count of responses forwarded.
`run` holds the list's authority and, for every ended epoch, its count's authority at its end
(at or below the current epoch's first position): so a response it takes from `respc` at a
position past the current epoch's first is the current stream's (`respcE_at`). Lean-first, no
Rocq counterpart.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3
open go_etcd_io.etcd.cache.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`run`'s current epoch** (its gRPC stream `γs`, from `respc`'s position `b`): the epochs'
authority, the earlier ones ended at or below `b` (their counts' authorities). -/
def epochSt (G : WgsPrm GF) (γs : StreamNames) (b : Nat) : IProp GF :=
  iprop(∃ (eps : List EpInfo) (γc : GName),
    monoListAuthOwn G.γep 1 (eps ++ [((γs, b, γc) : EpInfo)]) ∗
    [∗list] x ∈ eps, ∃ n : Nat, monoNatAuthOwn x.2.2 1 n ∗ ⌜n ≤ b⌝)

/-- **A response taken from `respc` in the current epoch is its stream's**: at a position `k` past
the epoch's first, its tag is the current epoch (an earlier one's count ended at or below `b`). -/
theorem respcE_at (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (b k : Nat) (p : Loc)
    (hk : b ≤ k) :
    epochSt G γs b ∗ respcE V G.γep (k : Int) p ⊢
      epochSt G γs b ∗
        respcElem γs (v3rpc.watchDn γs V.R.γ V.R.cid V.R.mid) ((k - b : Nat) : Int) p := by
  unfold epochSt respcE
  iintro ⟨⟨%eps, %γc, Ha, Hend⟩, ⟨%e, %b', %γs', %γc', #Hi, #Hlb, %Hb', Hel⟩⟩
  ihave %Hl := mono_list_auth_idx_lookup _ _ _ _ _ $$ Ha Hi
  simp only [Int.toNat_natCast] at Hb' ⊢
  by_cases he : e < eps.length
  · rw [List.getElem?_append_left he] at Hl
    icases (BigSepL.bigSepL_lookup_acc Hl).1 $$ Hend with ⟨⟨%n, Hn, %Hnb⟩, -⟩
    ihave %Hv := monoNatLbOwn_valid _ _ _ _ $$ Hn Hlb
    exfalso; simp at Hv; omega
  · have he' : e = eps.length := by
      obtain ⟨h1, -⟩ := List.getElem?_eq_some_iff.1 Hl
      simp only [List.length_append, List.length_singleton] at h1; omega
    subst he'
    rw [List.getElem?_append_right (Nat.le_refl _)] at Hl
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at Hl
    obtain ⟨rfl, rfl, rfl⟩ := Hl
    iframe Hel
    iexists eps, γc
    iframe

/-- **The epoch at `run`'s start** (`b = 0`, no earlier epoch). -/
theorem epochSt_first (G : WgsPrm GF) (γs : StreamNames) (γc : GName) :
    monoListAuthOwn (GF := GF) G.γep 1 ([] ++ [((γs, 0, γc) : EpInfo)]) ⊢ epochSt G γs 0 := by
  iintro Ha
  unfold epochSt
  iexists [], γc
  iframe Ha
  iapply BigSepL.bigSepL_nil.2
  itrivial

end lemmas

end client
end EtcdGrove
end Perennial
