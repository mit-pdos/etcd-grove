/-
Lean-first (no Rocq counterpart).

The proof of `Check`: `Run`'s premises, met by the model (`Model`), `Gen` (`genSpec`) and the
closure `apply`. `Run`'s `applySpec` hands `apply` a one-shot update (Perennial's atomic-fupd
style: it cannot be closed without committing), but the store's operations take an Iris
atomic update (`AU`), which they may open and abort. So the library's state `libState` is not
the store's client half `rkvVal γr` itself but a copy `rkvVal γd` (a second ghost variable
holding the same history), and the invariant `checkN` holds the client half with the other
half of the copy. The store's `AU` (`kvAu_of_run`) opens that invariant (abort closes it
back); its commit runs `Run`'s update on the copy, at the mask `⊤ \ checkMask` (`Run`'s `Eapp`
is `checkMask`, all but `kvMask \ checkN`: what the store's updates may open less the
invariant).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.Check
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.Model
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.Gen
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.KV__Get
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.KV__Put
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.KV__Append
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.Run

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [KVStor GF]

/-- The invariant's namespace: the store's client half, with the driver's copy. -/
abbrev checkN : Namespace := nroot.@"kvcheck"

/-- The library's mask (`Run`'s `Eapp`): all but what the store's updates may open, less
`checkN`. -/
def checkMask : CoPset := ⊤ \ (kvMask \ ↑checkN)

theorem checkMask_sub : ⊤ \ checkMask ⊆ kvMask \ ↑checkN := by
  intro p hp
  unfold checkMask at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_diff] at hp
  exact Classical.byContradiction fun h => hp.2 ⟨CoPset.mem_full, h⟩

theorem checkN_sub : (↑checkN : CoPset) ⊆ kvMask := by
  intro p hp
  unfold kvMask
  rw [LawfulSet.mem_diff, LawfulSet.mem_diff]
  refine ⟨⟨CoPset.mem_full, ?_⟩, ?_⟩
  · intro h
    have := mask_ndot_ne' nroot "kvcheck" "raft_commit" (by decide) _ hp
    rw [LawfulSet.mem_diff] at this
    exact this.2 h
  · intro h
    have := mask_ndot_ne' nroot "kvcheck" "rkv" (by decide) _ hp
    rw [LawfulSet.mem_diff] at this
    exact this.2 h

theorem lintestN_checkMask : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ checkMask := by
  intro p hp
  unfold checkMask kvMask
  simp only [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h => h.2 ⟨⟨⟨CoPset.mem_full, ?_⟩, ?_⟩, ?_⟩⟩
  · intro h'
    have := mask_ndot_ne' nroot "lintest" "raft_commit" (by decide) _ hp
    rw [LawfulSet.mem_diff] at this
    exact this.2 h'
  · intro h'
    have := mask_ndot_ne' nroot "lintest" "rkv" (by decide) _ hp
    rw [LawfulSet.mem_diff] at this
    exact this.2 h'
  · intro h'
    have := mask_ndot_ne' nroot "lintest" "kvcheck" (by decide) _ hp
    rw [LawfulSet.mem_diff] at this
    exact this.2 h'

instance rkvVal_timeless (γr : RKVNames) (x : KVMap) : Timeless (rkvVal (GF := GF) γr x) := by
  unfold rkvVal; infer_instance

/-- The store's atomic update, for the input `xin` (whose operation takes the state `x` to
`g x`, answering `out x`), from `Run`'s one-shot update: opened, it lends the store's client half
from the invariant `checkN` (so it can be closed back); committed, it runs `Run`'s update, moving
the driver's copy along. -/
theorem kvAu_of_run (γr γd : RKVNames) (xin : KVInput) (g : KVMap → KVMap)
    (out : KVMap → GoString) (Ψ : GoInterface → IProp GF)
    (Hg : ∀ s, inStep xin s = g s) (Hout : ∀ s, inOut xin s = out s) :
    ⊢ inv checkN iprop(∃ x, rkvVal (GF := GF) γr x ∗ rkvVal γd x) -∗
      (|={⊤ \ checkMask, ∅}=> ∃ s, rkvVal γd s ∗
        ∀ s' o, rkvVal γd s' ∗ ⌜kvS (GF := GF).M.step s (boxIn xin, o) = some s'⌝ ={∅, ⊤ \ checkMask}=∗
          Ψ o) -∗
      AU <{ ∃∃ (x : KVMap), rkvVal γr x }> @ kvMask, ∅
        <{ rkvVal γr (g x), COMM Ψ (boxS (out x)) }> := by
  iintro #Hinv HAU
  iauintro
  unfold atomic_acc
  iinv Hinv with ⟨%x, >Hr, >Hd⟩ Hclose
  · exact checkN_sub
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ kvMask \ ↑checkN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists x
  iframe Hr
  isplit
  · -- abort
    iintro Hr
    imod Hclose2 with -
    imod Hclose $$ [Hr Hd] with -
    · inext
      iexists x
      iframe
    imodintro
    iframe
  · -- commit
    iintro Hr
    imod Hclose2 with -
    imod fupd_mask_subseteq checkMask_sub with Hclose3
    imod HAU with ⟨%s, Hds, Hcommit⟩
    unfold rkvVal
    icases Hd with ⟨%Hx, Hd, %Hdx⟩
    icases Hds with ⟨%Hs, Hds, %Hss⟩
    icombine Hd Hds gives % ⟨_, Heq⟩
    subst Heq
    have Hsx : s = x := Hss.symm.trans Hdx
    subst Hsx
    icases Hr with ⟨%Hg', Hr, %Hgx⟩
    imod ghostVar_update_halves Hg' γd.val _ _ $$ Hd Hds with ⟨Hd, Hds⟩
    imod Hcommit $$ %(g s) %(boxS (out s)) [Hds] with HΨ
    · isplitl
      · iexists Hg'
        iframe
        ipureintro; exact Hgx
      · ipureintro
        simp only [kvS]
        rw [kvM_step_box, Hout, Hg, if_pos rfl]
    imod Hclose3 with -
    imod Hclose $$ [Hr Hd] with -
    · inext
      iexists g s
      isplitl [Hr]
      · iexists Hg'; iframe; ipureintro; exact Hgx
      · iexists Hg'; iframe; ipureintro; exact Hgx
    imodintro
    iexact HΨ

theorem idx_bounds (a n : w64) (h0 : 0 ≤ sint.Z n) (hn : ¬ uint.Z n = 0) :
    0 ≤ sint.Z (a % n) ∧ sint.Z (a % n) < sint.Z n := by
  have hu : uint.Z (a % n) = uint.Z a % uint.Z n := word.unsigned_modu a n
  have hnn : sint.Z n = uint.Z n := by word
  have hpos : 0 < uint.Z n := by word
  have hlt : uint.Z a % uint.Z n < uint.Z n := Int.emod_lt_of_pos _ hpos
  have hge : 0 ≤ uint.Z a % uint.Z n := Int.emod_nonneg _ (by omega)
  have hn63 : uint.Z n < 2 ^ 63 := by word
  have hs : sint.Z (a % n) = uint.Z (a % n) := by
    have : uint.Z (a % n) < 2 ^ 63 := by omega
    word
  omega

theorem idx_lt (a n : w64) (h0 : 0 ≤ sint.Z (a % n)) (h1 : sint.Z (a % n) < sint.Z n) :
    (sint.Z (a % n)).toNat < sint.nat n := by
  word

theorem Check.wp_proof
    (wp_Run : lintest.Run.spec (GF := GF) (hG := hG))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_Get : KV.Get.spec (GF := GF) (hG := hG))
    (wp_Put : KV.Put.spec (GF := GF) (hG := hG))
    (wp_Append : KV.Append.spec (GF := GF) (hG := hG)) :
    Check.spec (GF := GF) (hG := hG) := by
  intro γr ksl rs clockVal t0 Eclk clock clients ops HN Hne H0 H31 Hops Hmul
  wp_start as ⟨#Hcc, #Hks, #Hrs, Hval, #Hclk, Ht0⟩
  wp_auto
  ipersist kvs
  iunfold rkvVal at Hval
  icases Hval with ⟨%Hs0, Hv, %HH0⟩
  imod ghostVar_alloc (GF := GF) Hs0 with ⟨%γc, Hc⟩
  icases (ghostVar_split_half γc 1 Hs0).1 $$ Hc with ⟨Hc1, Hc2⟩
  let γd : RKVNames := { γr with val := γc }
  imod inv_alloc checkN ⊤ iprop(∃ x, rkvVal γr x ∗ rkvVal γd x) $$ [Hv Hc1] with #Hinv
  · inext
    iexists kvEmpty
    unfold rkvVal
    isplitl [Hv]
    · iexists Hs0; iframe; ipureintro; exact HH0
    · iexists Hs0; iframe; ipureintro; exact HH0
  wp_apply wp_Model as %m #Hm
  wp_apply wp_Run KVMap kvS m _ _ clock kvInOk (rkvVal γd) clockVal t0 checkMask Eclk clients ops
    (W64 0) lintestN_checkMask HN H0 H31 Hops Hmul $$ [Hc2 Ht0]
  · isplitr
    · iexact Hcc
    isplitr
    · iexact Hm
    isplitr
    · -- `apply`
      unfold lintest.applySpec
      iintro %i
      iintro !> %Φ' %Hin HAU
      obtain ⟨x, rfl, Hk, Hv⟩ := Hin
      wp_auto
      ihave %Hlen := ownSlice_len $$ Hks
      have Hrl : 0 < rs.length := List.length_pos_iff.mpr Hne
      have Hlen0 : ¬ uint.Z ksl.len = 0 := by word
      simp only [Hlen0, ↓reduceIte]
      wp_auto
      have Hidx := idx_bounds x.Replica' ksl.len Hlen.2 Hlen0
      simp only [Hidx, _root_.and_self, ↓reduceIte]
      obtain ⟨r, Hr⟩ : ∃ r, rs[(sint.Z (x.Replica' % ksl.len)).toNat]? = some r :=
        ⟨_, List.getElem?_eq_getElem (by rw [Hlen.1]; exact idx_lt _ _ Hidx.1 Hidx.2)⟩
      wp_apply wp_load_slice_index ksl (sint.Z (x.Replica' % ksl.len)) rs DFrac.discard r Hidx.1
        $$ [$Hks] as _
      · ipureintro; exact Hr
      ihave #HrKV := BigSepL.bigSepL_lookup (Φ := fun _ r => iprop(∃ γp, isKV (GF := GF) γr γp r)) Hr $$ Hrs
      icases HrKV with ⟨%γp, #HrKV⟩
      wp_if_destruct
      · -- Get
        replace Hif : x.Kind' = opGetB := Hif
        ihave HAU' := kvAu_of_run γr γd x (fun s => s) (fun s => s x.Key')
          (fun o => iprop(kvS.ioOk (GF := GF) (boxIn x) o -∗ Φ' #o))
          (fun s => by unfold inStep; rw [if_pos Hif])
          (fun s => by unfold inOut; rw [if_pos Hif]) $$ Hinv HAU
        wp_apply wp_Get γr γp r x.Key' (fun v => iprop(kvS.ioOk (GF := GF) (boxIn x) (boxS v) -∗ Φ' #(boxS v)))
          Hk $$ [$HrKV $HAU'] as %v HΨ
        iapply HΨ
        ipureintro; exact ⟨⟨x, rfl⟩, v, rfl⟩
      replace Hng : ¬ x.Kind' = opGetB := Hif
      wp_if_destruct
      · -- Put
        replace Hif : x.Kind' = opPutB := Hif
        ihave HAU' := kvAu_of_run γr γd x (fun s => kvUpd s x.Key' x.Val') (fun _ => [])
          (fun o => iprop(kvS.ioOk (GF := GF) (boxIn x) o -∗ Φ' #o))
          (fun s => by unfold inStep; rw [if_neg Hng, if_pos Hif])
          (fun s => by unfold inOut; rw [if_neg Hng]) $$ Hinv HAU
        wp_apply wp_Put γr γp r x.Key' x.Val' iprop(kvS.ioOk (GF := GF) (boxIn x) (boxS []) -∗ Φ' #(boxS []))
          Hk Hv $$ [$HrKV $HAU'] as HΨ
        iapply HΨ
        ipureintro; exact ⟨⟨x, rfl⟩, [], rfl⟩
      · -- Append
        replace Hif : ¬ x.Kind' = opPutB := Hif
        ihave HAU' := kvAu_of_run γr γd x (fun s => kvUpd s x.Key' (s x.Key' ++ x.Val')) (fun _ => [])
          (fun o => iprop(kvS.ioOk (GF := GF) (boxIn x) o -∗ Φ' #o))
          (fun s => by unfold inStep; rw [if_neg Hng, if_neg Hif])
          (fun s => by unfold inOut; rw [if_neg Hng]) $$ Hinv HAU
        wp_apply wp_Append γr γp r x.Key' x.Val' iprop(kvS.ioOk (GF := GF) (boxIn x) (boxS []) -∗ Φ' #(boxS []))
          Hk Hv $$ [$HrKV $HAU'] as HΨ
        iapply HΨ
        ipureintro; exact ⟨⟨x, rfl⟩, [], rfl⟩
    isplitr
    · -- `gen`
      unfold lintest.genSpec
      iintro %id
      iintro !> %Φ' _ HΦ'
      wp_apply wp_Gen as %i #Hi
      iapply HΦ' $$ Hi
    isplitr
    · iexact Hclk
    iframe
    unfold rkvVal
    iexists Hs0
    iframe
    ipureintro
    exact HH0
  iintro %r %Hr
  wp_auto
  iapply HΦ
  ipureintro
  exact Hr.2 (by decide)

end proof

end kvwitness
end EtcdGrove
end Perennial
