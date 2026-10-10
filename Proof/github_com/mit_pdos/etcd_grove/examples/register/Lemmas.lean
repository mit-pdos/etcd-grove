/-
Lean-first (no Rocq counterpart).

# The register's ghost lemmas (2026-10-10)

- `regStor_register`: a new storage joins the registry (`regStorInv`, `Defs.lean`).
- `reg_mint`: a new sequence number mints the operation's fresh token (`MintOk`).
- `reg_deposited_minted`: a deposited datum (raft's registry) was minted, so a datum with
  a minted key is the one minted there.
- `reg_propAu`: the client's atomic update over the register's value, wrapped as the
  atomic update over raft's client log that `Node.Propose` deposits: when raft commits
  the operation's first entry, it opens `regInv`, runs the client's update and moves the
  client log and the value together. Its result is the client's, at the value after the
  operation.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- A pointer-valued location wholly owned has no other fraction. -/
theorem loc_pointsto_excl (l : Loc) (v1 v2 : Loc) (q : Qp) :
    ⊢ (l ↦ v1 : IProp GF) -∗ l ↦{DFrac.own q} v2 -∗ False := by
  iintro H1 H2
  ihave H1 := typedPointsto_split _ _ _ $$ H1
  ihave H2 := typedPointsto_split _ _ _ $$ H2
  have h : ∀ (v : Loc) (dq : DFrac),
      typedPointstoDef (GF := GF) l v dq = heapPointsto l dq #v := fun _ _ => rfl
  rw [h, h]
  icombine H1 H2 gives %H
  exfalso
  have := DFrac.valid_own_op H.1
  have h1 : (1 : Qp).val = 1 := rfl
  have h2 : 0 < q.val := q.property
  grind

/-- A new storage joins the registry. -/
theorem regStor_register (s ms : Loc) (γs : MemStorNames) (E : CoPset) (HE : ↑regStorN ⊆ E) :
    ⊢ regStorInv (GF := GF) -∗ s.[RStorage, go!"MemoryStorage"] ↦ ms ={E}=∗
      regStorRec s ms γs := by
  iintro #Hinv Hf
  unfold regStorInv
  iinv Hinv with >Hi Hclose
  unfold regStorInvBody
  icases Hi with ⟨%M, Ha, Hm⟩
  cases HM : M !! s with
  | some x =>
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun (s : Loc) (x : MemStorRec) =>
      iprop(s.[RStorage, go!"MemoryStorage"] ↦{DFrac.own (1 : Qp).half} x.1)) HM).1 $$ Hm
      with ⟨Hx, -⟩
    iexfalso
    iapply loc_pointsto_excl $$ Hf Hx
  | none =>
    imod ghost_map_insert_persist s (memStorRec ms γs) HM $$ Ha with ⟨Ha, #Hfrag⟩
    icases (typedPointsto_dfractional (GF := GF) (s.[RStorage, go!"MemoryStorage"]) ms).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) |>.1 $$ [Hf] with ⟨Hf1, Hf2⟩
    · rw [DFrac.op_own, Qp.half_add_half]; iexact Hf
    imod (typedPointsto_dfractional (GF := GF) _ ms).dfractional_persist _ $$ Hf2 with #Hf2
    imod Hclose $$ [Ha Hm Hf1] with -
    · inext
      iexists M.insert s (memStorRec ms γs)
      iframe Ha
      iapply (BigSepM.bigSepM_insert (Φ := fun (s : Loc) (x : MemStorRec) =>
        iprop(s.[RStorage, go!"MemoryStorage"] ↦{DFrac.own (1 : Qp).half} x.1)) HM).2
      iframe Hm
      unfold memStorRec
      iexact Hf1
    imodintro
    unfold regStorRec
    iframe Hf2 Hfrag

/-- A new sequence number mints the operation's fresh token, and records it. -/
theorem reg_mint (γr : RegNames) (id ns : w64) (kind : w8) (val : List w8) (E : CoPset)
    (HE : ↑regN ⊆ E) (Hns : uint.Z ns + 1 < 2 ^ 64) :
    ⊢ regInv (GF := GF) γr -∗ id ↪[γr.seq] ns ={E}=∗
      id ↪[γr.seq] (ns + W64 1) ∗
      (id, ns + W64 1) ↪[γr.mint]□ encodeOp id (ns + W64 1) kind val ∗
      propFresh γr.raft (encodeOp id (ns + W64 1) kind val) := by
  iintro #Hinv Hseq
  unfold regInv
  iinv Hinv with >Hi Hclose
  unfold regInvBody
  icases Hi with ⟨%L, %M, %S, %Mi, HcL, Hv, HM, HS, HMi, %Hok⟩
  icases ghost_map_lookup $$ HS Hseq with %HSi
  have Hsucc : uint.Z (ns + W64 1) = uint.Z ns + 1 := by word
  generalize Hd : encodeOp id (ns + W64 1) kind val = d
  have Hkey : opKey d = some (id, ns + W64 1) := by rw [← Hd]; exact opKey_encodeOp _ _ _ _
  have HMi0 : Mi !! (id, ns + W64 1) = none := by
    cases h : Mi !! (id, ns + W64 1) with
    | none => rfl
    | some d' =>
      obtain ⟨n, Hn, Hle⟩ := Hok.2 _ _ _ h
      rw [HSi] at Hn; cases Hn
      omega
  have HM0 : M !! d = none := by
    cases h : M !! d with
    | none => rfl
    | some u =>
      cases u
      obtain ⟨k, Hk, Hk'⟩ := Hok.1 d h
      rw [Hkey] at Hk; cases Hk
      rw [HMi0] at Hk'; cases Hk'
  imod ghost_map_update (ns + W64 1) $$ HS Hseq with ⟨HS, Hseq⟩
  imod ghost_map_insert_persist (id, ns + W64 1) d HMi0 $$ HMi with ⟨HMi, #Hmint⟩
  imod ghost_map_insert d () HM0 $$ HM with ⟨HM, Hfresh⟩
  imod Hclose $$ [HcL Hv HM HS HMi] with -
  · inext
    iexists L, M.insert d (), S.insert id (ns + W64 1), Mi.insert (id, ns + W64 1) d
    iframe HcL Hv HM HS HMi
    ipureintro
    constructor
    · intro d' Hd'
      by_cases Heq : d' = d
      · subst Heq
        exact ⟨_, Hkey, GMap.lookup_insert_eq _ _ _⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)] at Hd'
        obtain ⟨k, Hk, Hk'⟩ := Hok.1 d' Hd'
        refine ⟨k, Hk, ?_⟩
        have Hne : (id, ns + W64 1) ≠ k := by
          intro h; subst h; rw [HMi0] at Hk'; cases Hk'
        rw [GMap.lookup_insert_ne _ _ Hne]; exact Hk'
    · intro i s d' Hs
      by_cases Hk : (i, s) = (id, ns + W64 1)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hk
        exact ⟨ns + W64 1, GMap.lookup_insert_eq _ _ _, Int.le_refl _⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hk)] at Hs
        obtain ⟨n, Hn, Hle⟩ := Hok.2 _ _ _ Hs
        by_cases Hi : i = id
        · subst Hi
          rw [HSi] at Hn; cases Hn
          exact ⟨ns + W64 1, GMap.lookup_insert_eq _ _ _, by omega⟩
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hi)]
          exact ⟨n, Hn, Hle⟩
  imodintro
  iframe Hseq Hmint
  unfold propFresh
  iexact Hfresh

/-- A deposited datum was minted (its fresh token is raft's registry's, and every token
was minted), so it is the one minted at its key. -/
theorem reg_deposited_minted (γr : RegNames) (d d0 : List w8) (k : w64 × w64) (E : CoPset)
    (HE1 : ↑regN ⊆ E) (HE2 : ↑raftN ⊆ E \ ↑regN) (Hk : opKey d = some k) :
    ⊢ regInv (GF := GF) γr -∗ raftCommitInv γr.raft -∗ deposited γr.raft d -∗
      k ↪[γr.mint]□ d0 ={E}=∗ ⌜d0 = d⌝ := by
  iintro #Hinv #Hcinv #Hdep #Hmint
  unfold regInv
  iinv Hinv with >Hi Hclose
  unfold regInvBody
  icases Hi with ⟨%L, %M, %S, %Mi, HcL, Hv, HM, HS, HMi, %Hok⟩
  -- the datum's fresh token is in raft's registry: `d ∈ M`
  unfold raftCommitInv
  iinv Hcinv with ⟨%P, %R, >HP, >Hj, >Htbl, Hpo⟩ Hclose2
  imod propsOwn_open γr.raft _ P R $$ Hpo with Hpo
  unfold propsOwnL
  icases Hpo with ⟨%odsP, #HdsP, Hv2, Hra, Hs⟩
  unfold deposited
  icases Hdep with ⟨%γp, #Hfr⟩
  icases ghost_map_lookup $$ Hra Hfr with %HR
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun d γp =>
    iprop(▷ (propSlot (GF := GF) γr.raft d γp (firstOcc odsP) ∗ propFresh γr.raft d))) HR).1 $$ Hs
    with ⟨⟨Hsl, >Hf⟩, Hsback⟩
  iunfold propFresh at Hf
  icases ghost_map_lookup $$ HM Hf with %HMd
  ihave Hs := Hsback $$ [Hsl Hf]
  · inext; iframe Hsl; unfold propFresh; iexact Hf
  ihave Hpo : propsOwnL γr.raft P R $$ [Hv2 Hra Hs]
  · unfold propsOwnL
    iexists odsP
    iframe HdsP Hv2 Hra Hs
  ihave Hpo := propsOwn_close γr.raft P R $$ Hpo
  imod Hclose2 $$ [HP Hj Htbl Hpo] with -
  · inext
    iexists P, R
    iframe
  obtain ⟨k', Hk', HMik⟩ := Hok.1 d HMd
  rw [Hk] at Hk'; cases Hk'
  icases ghost_map_lookup $$ HMi Hmint with %HMi0
  rw [HMik] at HMi0
  cases HMi0
  imod Hclose $$ [HcL Hv HM HS HMi] with -
  · inext
    iexists L, M, S, Mi
    iframe
    ipureintro; exact Hok
  imodintro
  ipureintro; rfl

/-- The client's atomic update over the register's value, as the atomic update over the
client log that `Node.Propose` deposits for the operation's datum `d` (see the file
header). -/
theorem reg_propAu (γr : RegNames) (d : List w8) (kind : w8) (val : List w8)
    (Hd : ∀ x, regApply x d = opNext kind val x) (Φ : List w8 → IProp GF) :
    ⊢ regInv (GF := GF) γr -∗
      AU <{ ∃∃ (x : List w8), regVal γr x }> @ regMask, ∅
        <{ regVal γr (opNext kind val x), COMM Φ (opNext kind val x) }> -∗
      propAu γr.raft d (fun L => Φ (regFold (L ++ [d]))) := by
  iintro #Hinv Hau
  unfold propAu
  iauintro
  unfold atomic_acc
  unfold regInv
  have Hdisj := regN_raftN
  iinv Hinv with >Hi Hclose
  unfold regInvBody
  icases Hi with ⟨%L, %M, %S, %Mi, HcL, Hv, HM, HS, HMi, %Hok⟩
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc regMask
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%x, Hx, Hucl⟩
  iunfold regVal at Hx
  ihave %Hxeq := ghostVar_agree γr.val (regFold L) (1 : Qp).half x (1 : Qp).half $$ Hv Hx
  subst Hxeq
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  imodintro
  iexists L
  iframe HcL
  isplit
  · iintro HcL
    icases Hucl with ⟨Habort, -⟩
    imod Habort $$ [Hx] with Hau
    · unfold regVal; iexact Hx
    imod Hclose $$ [HcL Hv HM HS HMi] with -
    · inext
      iexists L, M, S, Mi
      iframe
      ipureintro; exact Hok
    imodintro
    iexact Hau
  · iintro HcL
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    have Hf : regFold (L ++ [d]) = opNext kind val (regFold L) := by rw [regFold_snoc, Hd]
    imod ghostVar_update_halves (regFold (L ++ [d])) γr.val (regFold L) (regFold L) $$ Hv Hx
      with ⟨Hv, Hx⟩
    rw [Hf]
    imod Hcommit $$ [Hx] with HΦ
    · unfold regVal; iexact Hx
    imod Hclose $$ [HcL Hv HM HS HMi] with -
    · inext
      iexists L ++ [d], M, S, Mi
      rw [Hf]
      iframe
      ipureintro; exact Hok
    imodintro
    iexact HΦ

end lemmas

end EtcdGrove
end Perennial
