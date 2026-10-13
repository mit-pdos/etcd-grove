/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Register__Read.lean`.
Lean-first (no Rocq counterpart).

Under the lock, a new sequence number mints the read's context, registered in raft's
read-context registry with the committed log of the caller's lower bound (`reg_mint_read`),
and the read waits on a handoff channel in `reads` (`readsOwn`); `Node.ReadIndex` takes the
context's slice (registered, `node_read_register`), its record and the read credit; the
applier answers with `readP` (`Register.answer`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__Read
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.encode
public import Spec.go_etcd_io.raft.v3.node__ReadIndex
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem Register.Read.wp_proof
    (wp_encode : register.encode.spec (GF := GF) (hG := hG))
    (wp_node_ReadIndex : node.ReadIndex.spec (GF := GF) (hG := hG)) :
    Register.Read.spec (GF := GF) (hG := hG) := by
  intro γr γp r L0 Hcfg
  wp_start as ⟨#Hreg, Hcr, Hrdc, #Hlb⟩
  iunfold isRegister at Hreg
  icases Hreg with ⟨%id, %n, %st, #Hrep⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  iunfold regLb at Hlb
  icases Hlb with ⟨%l0, %ods0, #Hl0, #Hods0, %HL0⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  iNamed HR
  imod opCred_spend γp c $$ Hcred Hcr with ⟨%Hc1, Hcred⟩
  have Hns : uint.Z ns + 1 < 2 ^ 64 := by omega
  wp_auto
  -- the read's context, minted and registered with the caller's committed log
  imod reg_mint_read γr id ns l0 ⊤ CoPset.subseteq_top Hns $$ Hinv Hseq Hl0
    with ⟨Hseq, #Hmint, #Hrq⟩
  generalize Hc : encodeOp id (ns + W64 1) opReadB [] = cx
  wp_apply chan.wp_make2 (V := GoString) (W64 1) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  ihave Hoc : ownChan γc GoString (.Buffered []) $$ Hoc
  imod start_handoff ch (readP γr (firstOcc ods0)) iprop(True) iprop(False) γc $$ Hch Hoc
    with ⟨%γh, %Hγh, #Hho, Hprod, Hcons⟩
  iunfold readsOwn at Hrds
  iNamed Hrds
  have HRfresh : Rd !! (ns + W64 1) = none := by
    cases h : Rd !! (ns + W64 1) with
    | none => rfl
    | some ch' => have := HRdom _ _ h; word
  wp_auto
  wp_apply wp_mapInsert go.uint64 mR Rd (ns + W64 1) ch $$ [$HRd] as HRd
  wp_apply sync.Mutex.wp_Unlock _ _
    $$ [$Hmu $Hlocked Hns HmW HW Hseq Hcred Hwaiters HmR HRd Hreads Hprod]
  · inext
    unfold lockInv
    iexists ns + W64 1, mW, W, c - 1
    iframe Hns HmW HW Hseq Hcred Hwaiters
    isplitr
    · ipureintro; word
    isplitr
    · ipureintro
      intro s ch' Hs
      have := HWdom _ _ Hs; word
    unfold readsOwn
    iexists mR, Rd.insert (ns + W64 1) ch
    iframe HmR HRd
    isplitr
    · ipureintro
      intro s ch' Hs
      by_cases Hss : s = ns + W64 1
      · subst Hss; exact Int.le_refl _
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hss)] at Hs
        have := HRdom _ _ Hs; word
    iapply (BigSepM.bigSepM_insert (Φ := fun s ch => readWaiterOk (GF := GF) γr id s ch)
      HRfresh).2
    iframe Hreads
    unfold readWaiterOk
    iexists cx, l0, ods0, γh
    iframe Hmint Hrq Hods0 Hho Hprod
  -- `ReadIndex`, with the context's slice registered
  wp_apply context.wp_Background
  wp_apply wp_encode id (ns + W64 1) (W8 3) [] (by simp) as %b ⟨Hb, -⟩
  rw [show (W8 3 : w8) = opReadB from rfl, Hc]
  imod ownSlice_persist b _ _ $$ Hb with #Hb
  imod node_read_register γp.node id n b cx ⊤ CoPset.subseteq_top $$ HisNode Hb with #Hpd
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  rw [← Hraft] at Hcfg
  wp_apply wp_node_ReadIndex γp.node id n b cx l0 Hcfg $$ [$Hraftinit $HisNode $Hpd Hrq Hrdc] as %err -
  · rw [Hraft]; iframe Hrq Hrdc
  -- the answer
  wp_apply wp_handoff_receive (t := go.string) γh ch (readP γr (firstOcc ods0))
    iprop(True) iprop(False) false $$ [$Hho $Hcons] as %v %ok ⟨Hcons, Hgot⟩
  unfold handoffGot
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hgot with ⟨-, Hf⟩
    iexfalso; iexact Hf
  simp only [↓reduceIte]
  icases Hgot with ⟨Hw, -⟩
  iapply HΦ
  rw [← HL0]
  iunfold readP at Hw; iexact Hw

end proof

end register
end EtcdGrove
end Perennial
