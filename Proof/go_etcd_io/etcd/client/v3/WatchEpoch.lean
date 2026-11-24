/-
**`run`'s epochs** (D25, `notes/decisions.md`): one per gRPC stream it opened, in a mono list
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`run`'s current epoch** (its gRPC stream `γs`, from `respc`'s position `b`): the epochs'
authority, the earlier ones ended at or below `b` (their counts' authorities). (Phase 7's switch,
SW1, R2: the epoch no longer records its member and token, learned with each response.) -/
def epochSt (G : WgsPrm GF) (γs : StreamNames) (b : Nat) : IProp GF :=
  iprop(∃ (eps : List EpInfo) (γc : GName),
    monoListAuthOwn G.γep 1 (eps ++ [((γs, b, γc) : EpInfo)]) ∗
    [∗list] x ∈ eps, ∃ n : Nat, monoNatAuthOwn x.2.2 1 n ∗ ⌜n ≤ b⌝)

/-- **`run`'s current epoch at its member** (SW1, R2): the epoch (`epochSt`), and its stream's
dispatch, known once a response came (`Dm`, the responses taken in the epoch): at `V`'s address,
with the metadata of an attempt of the stream's context's (`G.omd`). Before the first response the
member is not known (a transparent retry may re-pick it), and none of `run`'s state reads it. -/
def epochAt (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (b : Nat) (Dm : List v3rpc.WatchRespM) :
    IProp GF :=
  iprop(epochSt G γs b ∗
    (⌜Dm = []⌝ ∨ ∃ md : GrpcMd, streamDispIs γs V.addr md ∗ clientAttemptMdI V.conn G.omd md))

/-- **A response taken from `respc` in the current epoch is its stream's**: at a position `k` past
the epoch's first, its tag is the current epoch (an earlier one's count ended at or below `b`), with
the dispatch it came with (SW1, R2). -/
theorem respcE_at (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (b k : Nat) (p : Loc)
    (hk : b ≤ k) :
    epochSt G γs b ∗ respcE V G.omd G.γep (k : Int) p ⊢
      epochSt G γs b ∗ ∃ (a : GoString) (md : GrpcMd), streamDispIs γs a md ∗ watchMdW V G.omd a md ∗
        respcElem γs (v3rpc.watchDn γs (V.memOf a) (V.memWOf a) (auth.mdTokenOf md))
          ((k - b : Nat) : Int) p := by
  unfold epochSt respcE
  iintro ⟨⟨%eps, %γc, Ha, Hend⟩, ⟨%e, %b', %γs', %γc', %a, %md, #Hi, #Hlb, %Hb', #Hd, #Hmd, Hel⟩⟩
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
    isplitl [Ha Hend]
    · iexists eps, γc
      iframe
    iexists a, md
    iframe Hd Hmd Hel

/-- **The epoch at `run`'s start** (`b = 0`, no earlier epoch). -/
theorem epochSt_first (G : WgsPrm GF) (γs : StreamNames) (γc : GName) :
    monoListAuthOwn (GF := GF) G.γep 1 ([] ++ [((γs, 0, γc) : EpInfo)]) ⊢ epochSt G γs 0 := by
  iintro Ha
  unfold epochSt
  iexists [], γc
  iframe Ha
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- **The current epoch ends** (D25, `run`'s reconnection): with the count authority of an epoch
the producer side handed back (`prodBack`), at a count `k` at or above the current epoch's start,
every epoch so far has ended at or below `k` (the handed-back one is the current one: an earlier
one's authority is `run`'s). -/
theorem epochSt_close (G : WgsPrm GF) (γs : StreamNames) (b : Nat)
    (e b0 : Nat) (γs0 : StreamNames) (γc0 : GName) (k : Nat) (hb : b ≤ k) :
    epochSt G γs b ∗ monoListIdxOwn G.γep e ((γs0, b0, γc0) : EpInfo) ∗
      monoNatAuthOwn γc0 1 k ⊢
      ∃ eps : List EpInfo, monoListAuthOwn G.γep 1 eps ∗
        [∗list] x ∈ eps, ∃ n : Nat, monoNatAuthOwn x.2.2 1 n ∗ ⌜n ≤ k⌝ := by
  unfold epochSt
  iintro ⟨⟨%eps, %γc, Ha, Hend⟩, #Hi, Hc⟩
  ihave %Hl := mono_list_auth_idx_lookup _ _ _ _ _ $$ Ha Hi
  by_cases he : e < eps.length
  · rw [List.getElem?_append_left he] at Hl
    icases (BigSepL.bigSepL_lookup_acc Hl).1 $$ Hend with ⟨⟨%n, Hn, -⟩, -⟩
    iexfalso
    iapply monoNatAuthOwn_exclusive $$ Hn Hc
  · have he' : e = eps.length := by
      obtain ⟨h1, -⟩ := List.getElem?_eq_some_iff.1 Hl
      simp only [List.length_append, List.length_singleton] at h1; omega
    subst he'
    rw [List.getElem?_append_right (Nat.le_refl _)] at Hl
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at Hl
    obtain ⟨rfl, rfl, rfl⟩ := Hl
    iexists eps ++ [((γs, b, γc) : EpInfo)]
    iframe Ha
    iapply BigSepL.bigSepL_snoc.2
    isplitl [Hend]
    · have hm : ∀ {j : Nat} {x : EpInfo},
          iprop(∃ n : Nat, monoNatAuthOwn (GF := GF) x.2.2 1 n ∗ ⌜n ≤ b⌝) ⊢
            iprop(∃ n : Nat, monoNatAuthOwn (GF := GF) x.2.2 1 n ∗ ⌜n ≤ k⌝) := by
        intro _ x
        iintro ⟨%n, Hn, %Hn⟩
        iexists n; iframe; ipureintro; omega
      iapply BigSepL.bigSepL_mono_of_forall (fun {j x} => hm (j := j) (x := x)) $$ Hend
    · iexists k; iframe; ipureintro; exact Nat.le_refl _

/-- **The next epoch** (D25): from `respc`'s position `k`, every earlier epoch ended at or below it. -/
theorem epochSt_open (G : WgsPrm GF) (γs : StreamNames) (k : Nat) (γc : GName)
    (eps : List EpInfo) :
    monoListAuthOwn (GF := GF) G.γep 1 (eps ++ [((γs, k, γc) : EpInfo)]) ∗
      ([∗list] x ∈ eps, ∃ n : Nat, monoNatAuthOwn x.2.2 1 n ∗ ⌜n ≤ k⌝) ⊢ epochSt G γs k := by
  iintro ⟨Ha, Hend⟩
  unfold epochSt
  iexists eps, γc
  iframe

/-- **A new epoch at its start** (SW1): no response yet, so no member. -/
theorem epochAt_nil (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (b : Nat) :
    epochSt G γs b ⊢ epochAt V G γs b [] := by
  iintro H
  unfold epochAt
  iframe H
  ileft; ipureintro; rfl

end lemmas

end client
end EtcdGrove
end Perennial
