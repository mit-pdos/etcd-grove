/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/Deploy.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The deployment's registry (U2): the start resources of the master and of the replica nodes'
registrations, the invariant that ties the master's registry to Gryff's node ids, and
`registeredAs` (the bodies of `masterStartRes`, `replicaRegRes`, `registeredAs`).

* `deployInv δ γp` (namespace `deployN`, allocated by the start, `deploy_alloc`): the
  registry's other authority half over `ks.map addrOf` (`ks`: the registered replica nodes, in
  registration order, distinct, each below 3), the authority of `γp.nodeIds` (its keys are
  registered nodes), and `nodeIdIs γp k i` for the `i`-th registered node `k`.
* The master holds the first authority half (`deployStartDef`) and appends to both halves under
  its lock, opening `deployInv` (`deploy_register`).
* D13: the registration request carries the node's recorded prediction (`regCarry`: `predIs γp k
  ws`, `masterSvc`'s `R`); the master's registration of node `k` as replica id `i` spends the
  invariant's slot `i` (`predSlot γp i`, then `predIdIs γp i ws` through `pred_register`) and records
  `regPred γp i k`; slot `i`'s start resources (`idSlotRes`) stay in the invariant until node `k`
  claims them with its token (`slotClaimTok`, `deploy_claim`).
* A replica that got a `Ready` reply (`regReady`: a witness of the full list and its index) gets
  its `nodeIdIs` from the invariant (`deploy_nodeId`), and all three predictions with its own
  (`deploy_ready`); `registeredAsDef` is the reply's facts, that `nodeIdIs` and those
  predictions.
* Agreement (`registeredAsDef_agree`): two witnesses of the registry are prefix-comparable, and
  two full lists are permutations of the same three addresses, hence equal.
-/
module

public import Dsverify.Proof.gryff.Rpc.Defs
public import Dsverify.Proof.gryff.Proto.Inv
public import Dsverify.Proof.gryff.Proto2.Laws
public import Batteries.Data.List.Perm

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure facts about the replicas' addresses -/

theorem addrOf_inj {k1 k2 : Nat} (h1 : k1 < 3) (h2 : k2 < 3) (h : addrOf k1 = addrOf k2) :
    k1 = k2 := by
  rcases k1 with _|_|_|k1 <;> rcases k2 with _|_|_|k2 <;>
    first | rfl | omega | (exfalso; revert h; decide)

theorem map_addrOf_inj {ks1 ks2 : List Nat} (h1 : ∀ k ∈ ks1, k < 3) (h2 : ∀ k ∈ ks2, k < 3)
    (h : ks1.map addrOf = ks2.map addrOf) : ks1 = ks2 := by
  induction ks1 generalizing ks2 with
  | nil => cases ks2 with
    | nil => rfl
    | cons _ _ => simp at h
  | cons k ks ih => cases ks2 with
    | nil => simp at h
    | cons k' ks' =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [addrOf_inj (h1 k (by simp)) (h2 k' (by simp)) h.1,
        ih (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx])) h.2]

theorem prefix_map_addrOf {ks : List Nat} {L : List GoString} (h : L <+: ks.map addrOf) :
    ∃ ks', ks' <+: ks ∧ L = ks'.map addrOf := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨a, b, hab, ha, _⟩ := List.map_eq_append_iff.mp ht.symm
  exact ⟨a, ⟨b, hab.symm⟩, ha.symm⟩

theorem bound_subset {ks : List Nat} (hb : ∀ k ∈ ks, k < 3) : ks ⊆ [0, 1, 2] := by
  intro x hx; have := hb x hx; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

/-- Distinct replica nodes number at most 3. -/
theorem nodup_bound_length {ks : List Nat} (hnd : ks.Nodup) (hb : ∀ k ∈ ks, k < 3) :
    ks.length ≤ 3 :=
  (List.subperm_of_subset hnd (bound_subset hb)).length_le

/-- Three distinct replica nodes are a permutation of `[0, 1, 2]`. -/
theorem nodup_bound_perm {ks : List Nat} (hnd : ks.Nodup) (hb : ∀ k ∈ ks, k < 3)
    (hl : ks.length = 3) : ks.Perm [0, 1, 2] :=
  (List.subperm_of_subset hnd (bound_subset hb)).perm_of_length_le (by simp [hl])

/-! ## The deployment's invariant and the start resources -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

instance nodeIdIs_timeless (γp : ProtoNames) (k : Nat) (id : w64) :
    Timeless (nodeIdIs (GF := GF) γp k id) := by
  unfold nodeIdIs; infer_instance

instance nodeIdIs_persistent (γp : ProtoNames) (k : Nat) (id : w64) :
    Persistent (nodeIdIs (GF := GF) γp k id) := by
  unfold nodeIdIs; infer_instance

def deployN : Namespace := ndot nroot "gryff.deploy"

/-- Gryff's invariant can be opened inside the registry's. -/
theorem gryffN_sub_top_deployN : (↑gryffN : CoPset) ⊆ ⊤ \ ↑deployN := by
  intro p hp
  refine CoPset.in_diff.mpr ⟨CoPset.subseteq_top p hp, fun h => ?_⟩
  exact ndot_ne_disjoint nroot (x := "gryff") (y := "gryff.deploy") (by decide) p ⟨hp, h⟩

/-- What a registering node carries (D13): its recorded prediction. -/
def regCarry (γp : ProtoNames) (k : Nat) : IProp GF := iprop(∃ ws, predIs γp k ws)

/-- The rpc world's services are the deployment's (the start allocates the world with
`rpcServices`, `net.rpc.rpcWorld_alloc`). -/
def worldOk (γ : GryffNames GF) : Prop :=
  ∀ a svc, γ.rpc.SS a svc = rpcServicesDef γ.deploy (regCarry γ.proto) a svc

/-- Replica id `i`'s prediction is registered node `k`'s (persistent). -/
def regPred (γp : ProtoNames) (i k : Nat) : IProp GF :=
  iprop(∃ ws, predIs γp k ws ∗ predIdIs γp i ws)

/-- Replica id `i`'s start resources (`idSlotRes`; nothing for `i ≥ 3`). -/
def idSlotResN (γp : ProtoNames) (i : Nat) : IProp GF :=
  if h : i < 3 then idSlotRes γp ⟨i, h⟩ else iprop(True)

theorem idSlotResN_lt (γp : ProtoNames) (i : Nat) (h : i < 3) :
    idSlotResN γp i ⊣⊢ idSlotRes γp ⟨i, h⟩ := by
  unfold idSlotResN; rw [dif_pos h]; exact .rfl

/-- See the file header. -/
def deployInv (δ : DeployNames) (γp : ProtoNames) : IProp GF :=
  iprop(∃ (ks : List Nat) (M : GMap Nat w64),
    regAuth δ (1 : Qp).half (ks.map addrOf) ∗ ghostMapAuth γp.nodeIds 1 M ∗
    ⌜ks.Nodup ∧ (∀ k ∈ ks, k < 3) ∧ ∀ k, M !! k ≠ none → k ∈ ks⌝ ∗
    ([∗list] i ↦ k ∈ ks, nodeIdIs γp k (W64 i)) ∗
    ([∗list] i ↦ k ∈ ks, regPred γp i k ∗ (slotClaimTok γp k ∨ idSlotResN γp i)) ∗
    [∗list] i ∈ List.range' ks.length (3 - ks.length), predSlot γp i ∗ idSlotResN γp i)

/-- The master's start resources: the registry's authority half, empty, the invariant, and the
rpc world's services. -/
def deployStartDef (γ : GryffNames GF) : IProp GF :=
  iprop(regAuth γ.deploy (1 : Qp).half [] ∗ inv deployN (deployInv γ.deploy γ.proto) ∗
    ⌜worldOk γ⌝)

/-- Replica node `k`'s registration resources: the invariant and the rpc world's services
(persistent). -/
def deployRegResDef (γ : GryffNames GF) (_k : Nat) : IProp GF :=
  iprop(inv deployN (deployInv γ.deploy γ.proto) ∗ ⌜worldOk γ⌝)

/-- Replica node `k` registered as `id` with the list `nodes`; all three replica ids' predictions
are set, `id`'s is `k`'s recorded one (D13). -/
def registeredAsDef (γ : GryffNames GF) (k : Nat) (id : w64) (nodes : List GoString) :
    IProp GF :=
  iprop(⌜k < 3⌝ ∗ regReady γ.deploy k id nodes ∗ nodeIdIs γ.proto k id ∗ predsSet γ.proto ∗
    regPred γ.proto (uint.nat id) k)

instance deployRegResDef_persistent (γ : GryffNames GF) (k : Nat) :
    Persistent (deployRegResDef γ k) := by
  unfold deployRegResDef; infer_instance

instance predSlot_timeless (γp : ProtoNames) (i : Nat) :
    Timeless (predSlot (GF := GF) γp i) := by
  unfold predSlot; infer_instance

instance slotClaimTok_timeless (γp : ProtoNames) (k : Nat) :
    Timeless (slotClaimTok (GF := GF) γp k) := by
  unfold slotClaimTok; infer_instance

instance regPred_timeless (γp : ProtoNames) (i k : Nat) : Timeless (regPred (GF := GF) γp i k) := by
  unfold regPred predIs predIdIs; infer_instance

instance idSlotResN_timeless (γp : ProtoNames) (i : Nat) : Timeless (idSlotResN (GF := GF) γp i) := by
  unfold idSlotResN
  split
  · unfold idSlotRes traceHalf rxCurTok; infer_instance
  · infer_instance

instance regPred_persistent (γp : ProtoNames) (i k : Nat) : Persistent (regPred (GF := GF) γp i k) := by
  unfold regPred; infer_instance

instance regCarry_persistent (γp : ProtoNames) (k : Nat) : Persistent (regCarry (GF := GF) γp k) := by
  unfold regCarry; infer_instance

instance registeredAsDef_persistent (γ : GryffNames GF) (k : Nat) (id : w64)
    (nodes : List GoString) : Persistent (registeredAsDef γ k id nodes) := by
  unfold registeredAsDef nodeIdIs; infer_instance

end defs

/-! ## The registry's ghost laws -/

section reg
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

theorem regAuth_halves (δ : DeployNames) (L : List GoString) :
    regAuth δ 1 L ⊣⊢ regAuth δ (1 : Qp).half L ∗ regAuth δ (1 : Qp).half L := by
  unfold regAuth
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (@monoListAuthOwn_fractional GF _ GoString _ δ.registry L).fractional _ _

theorem regAuth_agree (δ : DeployNames) (q1 q2 : Qp) (L1 L2 : List GoString) :
    regAuth δ q1 L1 ∗ regAuth δ q2 L2 ⊢ ⌜L1 = L2⌝ := by
  unfold regAuth
  iintro ⟨H1, H2⟩
  icases (@monoListAuthOwn_agree GF _ GoString _ δ.registry q1 q2 L1 L2) $$ H1 H2
    with %H
  ipureintro; exact H.2

theorem regAuth_lb (δ : DeployNames) (q : Qp) (L : List GoString) :
    regAuth δ q L ⊢ regLb δ L := by
  unfold regAuth regLb
  exact @monoListLbOwn_get GF _ GoString _ δ.registry q L

theorem regAuth_lb_prefix (δ : DeployNames) (q : Qp) (L L' : List GoString) :
    regAuth δ q L ∗ regLb δ L' ⊢ ⌜L' <+: L⌝ := by
  unfold regAuth regLb
  iintro ⟨H1, H2⟩
  icases (@mono_list_auth_lb_valid GF _ GoString _ δ.registry q L L') $$ H1 H2
    with %H
  ipureintro; exact H.2

theorem regLb_valid (δ : DeployNames) (L1 L2 : List GoString) :
    regLb δ L1 ∗ regLb δ L2 ⊢ ⌜L1 <+: L2 ∨ L2 <+: L1⌝ := by
  unfold regLb
  iintro ⟨H1, H2⟩
  iapply (@mono_list_lb_valid GF _ GoString _ δ.registry L1 L2) $$ H1 H2

/-- A witness of the registry from both halves, keeping them. -/
theorem regAuth_halves_lb (δ : DeployNames) (L : List GoString) :
    regAuth δ (1 : Qp).half L ∗ regAuth δ (1 : Qp).half L ⊢ |==>
      (regAuth δ (1 : Qp).half L ∗ regAuth δ (1 : Qp).half L ∗ regLb δ L) := by
  iintro H
  ihave H := (regAuth_halves δ L).2 $$ H
  ihave H : (@monoListAuthOwn GF _ GoString _ δ.registry 1 L) $$ [H]
  · unfold regAuth; iexact H
  imod (@monoListAuthOwn_update GF _ GoString _ δ.registry L L (List.prefix_refl L))
    $$ H with ⟨H, #Hlb⟩
  imodintro
  ihave H : regAuth δ 1 L $$ [H]
  · unfold regAuth; iexact H
  ihave Hlb : regLb δ L $$ [Hlb]
  · unfold regLb; iexact Hlb
  icases (regAuth_halves δ L).1 $$ H with ⟨H1, H2⟩
  iframe

theorem regAuth_append (δ : DeployNames) (L : List GoString) (a : GoString) :
    regAuth δ (1 : Qp).half L ∗ regAuth δ (1 : Qp).half L ⊢ |==>
      (regAuth δ (1 : Qp).half (L ++ [a]) ∗ regAuth δ (1 : Qp).half (L ++ [a])) := by
  iintro H
  ihave H := (regAuth_halves δ L).2 $$ H
  ihave H : (@monoListAuthOwn GF _ GoString _ δ.registry 1 L) $$ [H]
  · unfold regAuth; iexact H
  imod (@monoListAuthOwn_update_app GF _ GoString _ δ.registry L [a]) $$ H
    with ⟨H, -⟩
  imodintro
  ihave H : regAuth δ 1 (L ++ [a]) $$ [H]
  · unfold regAuth; iexact H
  iapply (regAuth_halves δ (L ++ [a])).1 $$ H

end reg


section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- The start's allocation of the registry and its invariant, from the authority of Gryff's
node ids (empty) and the three replica ids' slots (D13: unset predictions, start resources): the
master's half of the registry (empty) and the invariant. -/
theorem deploy_alloc (γp : ProtoNames) (E : CoPset) :
    ghostMapAuth (K := Nat) (V := w64) γp.nodeIds 1 ∅ ∗
      ([∗list] i ∈ [0, 1, 2], predSlot γp i ∗ idSlotResN γp i) ⊢
      |={E}=> (∃ δ : DeployNames, regAuth δ (1 : Qp).half [] ∗ inv deployN (deployInv δ γp)) := by
  iintro ⟨HM, Hsl⟩
  imod (@mono_list_own_alloc GF _ GoString _ []) with ⟨%γr, Ha, -⟩
  ihave Ha : regAuth ⟨γr⟩ 1 [] $$ [Ha]
  · unfold regAuth; iexact Ha
  icases (regAuth_halves ⟨γr⟩ []).1 $$ Ha with ⟨Ha1, Ha2⟩
  imod inv_alloc deployN E (deployInv ⟨γr⟩ γp) $$ [Ha2 HM Hsl] with #Hinv
  · inext
    unfold deployInv
    iexists ([] : List Nat), ∅
    rw [List.map_nil]
    isplitl [Ha2]
    · iexact Ha2
    iframe HM
    isplitr
    · ipureintro
      refine ⟨List.nodup_nil, by simp, ?_⟩
      intro k hk; exact absurd rfl hk
    isplitr [Hsl]
    · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr [Hsl]
    · iapply BigSepL.bigSepL_nil.2; iempintro
    rw [show List.range' ([] : List Nat).length (3 - ([] : List Nat).length) = [0, 1, 2] from rfl]
    iexact Hsl
  imodintro
  iexists ⟨γr⟩
  isplitl [Ha1]
  · iexact Ha1
  iexact Hinv

/-- The master's registration of replica node `k` (not registered yet), under its lock: both
halves of the registry move to `ks ++ [k]`, and `k` gets its node id `ks.length`; replica id
`ks.length`'s prediction becomes `k`'s, which the request carried (D13, `pred_register`). -/
theorem deploy_register (δ : DeployNames) (γp : ProtoNames) (ks : List Nat) (k : Nat)
    (ws : List w64) (hk : k < 3) (hks : ∀ x ∈ ks, x < 3) (hnot : k ∉ ks) (E : CoPset)
    (hE : ↑deployN ⊆ E) (hE2 : ↑gryffN ⊆ E \ ↑deployN) :
    inv deployN (deployInv δ γp) ∗ gryffInv2 γp ∗ predIs γp k ws ∗
        regAuth δ (1 : Qp).half (ks.map addrOf) ⊢
      |={E}=> regAuth δ (1 : Qp).half ((ks ++ [k]).map addrOf) := by
  iintro ⟨#Hinv, #Hg, #Hp, Ha⟩
  iinv Hinv with Hi Hclose
  unfold deployInv
  icases Hi with ⟨%ks', %M, >Ha', >HM, >%Hf, >Hids, >Hreg, >Hfree⟩
  icases regAuth_agree δ (1 : Qp).half (1 : Qp).half (ks.map addrOf) (ks'.map addrOf) $$ [Ha Ha']
    with %Heq
  · iframe Ha Ha'
  have hks' := map_addrOf_inj hks Hf.2.1 Heq
  subst hks'
  imod regAuth_append δ (ks.map addrOf) (addrOf k) $$ [Ha Ha'] with ⟨Ha, Ha'⟩
  · iframe Ha Ha'
  have hMk : M.lookup k = none := by
    rcases h : M.lookup k with _ | v
    · rfl
    · exfalso; exact hnot (Hf.2.2 k (by rw [h]; simp))
  imod ghost_map_insert_persist k (W64 ks.length) hMk $$ HM with ⟨HM, #Hel⟩
  have hlen3 : ks.length < 3 := by
    have := nodup_bound_length (ks := k :: ks) (List.nodup_cons.mpr ⟨hnot, Hf.1⟩)
      (by intro x hx; simp at hx; rcases hx with rfl | hx; exact hk; exact hks x hx)
    simp at this; omega
  have hr : List.range' ks.length (3 - ks.length) =
      ks.length :: List.range' (ks.length + 1) (3 - (ks.length + 1)) := by
    rw [show 3 - ks.length = (3 - (ks.length + 1)) + 1 by omega, List.range'_succ]
  rw [hr]
  icases BigSepL.bigSepL_cons.1 $$ Hfree with ⟨⟨Hslot, Hres⟩, Hfree⟩
  ihave #Hnid : nodeIdIs γp k (W64 ks.length) $$ []
  · unfold nodeIdIs; iexact Hel
  imod pred_register (GF := GF) γp k ks.length ws hlen3 _ hE2 $$ [Hslot] with #Hpid
  · iframe Hslot; iframe #
  imod Hclose $$ [Ha' HM Hids Hreg Hfree Hres] with -
  · inext
    iexists ks ++ [k], _
    rw [List.map_append, List.map_singleton, List.length_append, List.length_singleton]
    iframe Ha' HM
    isplitr
    · ipureintro
      refine ⟨List.nodup_append.mpr ⟨Hf.1, by simp, ?_⟩, ?_, ?_⟩
      · intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb
        intro h; subst h; exact hnot ha
      · intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hks x hx
        · exact hk
      · intro x hx
        simp only [List.mem_append, List.mem_singleton]
        by_cases hxk : x = k
        · exact Or.inr hxk
        · left; apply Hf.2.2 x
          rwa [lookup_insert_ne M _ (Ne.symm hxk)] at hx
    isplitl [Hids]
    · iapply BigSepL.bigSepL_snoc.2
      iframe Hids
      iexact Hnid
    isplitl [Hreg Hres]
    · iapply BigSepL.bigSepL_snoc.2
      iframe Hreg
      isplitr
      · unfold regPred; iexists ws; iframe #
      iright; iexact Hres
    iexact Hfree
  imodintro
  rw [List.map_append, List.map_singleton]
  iexact Ha

/-- The master's witness of the registry it holds a half of. -/
theorem deploy_lb (δ : DeployNames) (γp : ProtoNames) (L : List GoString) (E : CoPset)
    (hE : ↑deployN ⊆ E) :
    inv deployN (deployInv δ γp) ∗ regAuth δ (1 : Qp).half L ⊢
      |={E}=> (regAuth δ (1 : Qp).half L ∗ regLb δ L) := by
  iintro ⟨#Hinv, Ha⟩
  iinv Hinv with Hi Hclose
  unfold deployInv
  icases Hi with ⟨%ks', %M, >Ha', >HM, >%Hf, >Hids, >Hreg, >Hfree⟩
  icases regAuth_agree δ (1 : Qp).half (1 : Qp).half L (ks'.map addrOf) $$ [Ha Ha'] with %Heq
  · iframe Ha Ha'
  subst Heq
  imod regAuth_halves_lb δ (ks'.map addrOf) $$ [Ha Ha'] with ⟨Ha, Ha', #Hlb⟩
  · iframe Ha Ha'
  imod Hclose $$ [Ha' HM Hids Hreg Hfree] with -
  · inext
    iexists ks', M
    iframe Ha' HM Hids Hreg Hfree
    ipureintro; exact Hf
  imodintro
  iframe Ha Hlb

/-- A replica's node id, from a `Ready` registration: the registry's invariant gives its
`nodeIdIs`. -/
theorem deploy_nodeId (δ : DeployNames) (γp : ProtoNames) (k : Nat) (hk : k < 3) (id : w64)
    (nodes : List GoString) (E : CoPset) (hE : ↑deployN ⊆ E) :
    inv deployN (deployInv δ γp) ∗ regReady δ k id nodes ⊢ |={E}=> nodeIdIs γp k id := by
  iintro ⟨#Hinv, #Hr⟩
  unfold regReady
  icases Hr with ⟨#Hlb, %Hf⟩
  iinv Hinv with Hi Hclose
  unfold deployInv
  icases Hi with ⟨%ks, %M, >Ha, >HM, >%Hks, >Hids, >Hreg, >Hfree⟩
  icases regAuth_lb_prefix δ (1 : Qp).half (ks.map addrOf) nodes $$ [Ha Hlb] with %Hpre
  · iframe Ha Hlb
  obtain ⟨ks', hks', rfl⟩ := prefix_map_addrOf Hpre
  have hl3 : ks'.length = 3 := by
    have := Hf.1.length_eq; simpa using this
  have hle := nodup_bound_length Hks.1 Hks.2.1
  have hkseq : ks' = ks := hks'.eq_of_length (by have := hks'.length_le; omega)
  subst hkseq
  obtain ⟨Hp, Hid⟩ := Hf
  rw [List.getElem?_map] at Hid
  obtain ⟨k', Hk', Hak⟩ : ∃ k', ks'[uint.nat id]? = some k' ∧ addrOf k' = addrOf k := by
    rcases h : ks'[uint.nat id]? with _ | k'
    · rw [h] at Hid; simp at Hid
    · rw [h] at Hid; simp only [Option.map_some, Option.some.injEq] at Hid
      exact ⟨k', rfl, Hid⟩
  have hk' : k' < 3 := Hks.2.1 k' (List.mem_of_getElem? Hk')
  have hkk := addrOf_inj hk' hk Hak
  subst hkk
  icases (BigSepL.bigSepL_lookup_acc (Φ := fun i x => nodeIdIs (GF := GF) γp x (W64 i))
    Hk').1 $$ Hids with ⟨#Hel, Hback⟩
  ihave Hids := Hback $$ %k' Hel
  have hset : ks'.set (uint.nat id) k' = ks' := by
    apply List.ext_getElem?; intro j
    rw [List.getElem?_set]
    by_cases hj : uint.nat id = j
    · subst hj; have h1 := List.getElem?_eq_some_iff.mp Hk'; simp [h1.1, h1.2]
    · simp [hj]
  rw [hset]
  imod Hclose $$ [Ha HM Hids Hreg Hfree] with -
  · inext
    iexists ks', M
    iframe Ha HM Hids Hreg Hfree
    ipureintro; exact Hks
  imodintro
  have hid : W64 (uint.nat id) = id := by word
  rw [hid]
  iexact Hel

/-- A `Ready` registration's predictions (D13): the registry is full, so the three replica ids'
predictions are set (`predsSet`), and the caller's is its own recorded one (`regPred`). -/
theorem deploy_ready (δ : DeployNames) (γp : ProtoNames) (k : Nat) (hk : k < 3) (id : w64)
    (nodes : List GoString) (E : CoPset) (hE : ↑deployN ⊆ E) :
    inv deployN (deployInv δ γp) ∗ regReady δ k id nodes ⊢
      |={E}=> predsSet γp ∗ regPred γp (uint.nat id) k := by
  iintro ⟨#Hinv, #Hr⟩
  unfold regReady
  icases Hr with ⟨#Hlb, %Hf⟩
  iinv Hinv with Hi Hclose
  unfold deployInv
  icases Hi with ⟨%ks, %M, >Ha, >HM, >%Hks, >Hids, >Hreg, >Hfree⟩
  icases regAuth_lb_prefix δ (1 : Qp).half (ks.map addrOf) nodes $$ [Ha Hlb] with %Hpre
  · iframe Ha Hlb
  obtain ⟨ks', hks', rfl⟩ := prefix_map_addrOf Hpre
  have hl3 : ks'.length = 3 := by
    have := Hf.1.length_eq; simpa using this
  have hle := nodup_bound_length Hks.1 Hks.2.1
  have hkseq : ks' = ks := hks'.eq_of_length (by have := hks'.length_le; omega)
  subst hkseq
  obtain ⟨Hp, Hid⟩ := Hf
  rw [List.getElem?_map] at Hid
  obtain ⟨k', Hk', Hak⟩ : ∃ k', ks'[uint.nat id]? = some k' ∧ addrOf k' = addrOf k := by
    rcases h : ks'[uint.nat id]? with _ | k'
    · rw [h] at Hid; simp at Hid
    · rw [h] at Hid; simp only [Option.map_some, Option.some.injEq] at Hid
      exact ⟨k', rfl, Hid⟩
  have hk' : k' < 3 := Hks.2.1 k' (List.mem_of_getElem? Hk')
  have hkk := addrOf_inj hk' hk Hak
  subst hkk
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, ks' = [a, b, c] := by
    match ks', hl3 with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  ihave #Hrp : □ ([∗list] i ↦ k ∈ [a, b, c], regPred γp i k) $$ [Hreg]
  · icases Hreg with ⟨⟨#R0, -⟩, ⟨#R1, -⟩, ⟨#R2, -⟩, -⟩
    imodintro
    iframe R0 R1 R2
    iempintro
  ihave #Hk := (BigSepL.bigSepL_lookup (Φ := fun i x => regPred γp i x) Hk') $$ Hrp
  imod Hclose $$ [Ha HM Hids Hreg Hfree] with -
  · inext
    iexists [a, b, c], M
    iframe Ha HM Hids Hreg Hfree
    ipureintro; exact Hks
  imodintro
  ihave #R0 := (BigSepL.bigSepL_lookup (Φ := fun i x => regPred γp i x)
    (show [a, b, c][0]? = some a from rfl)) $$ Hrp
  ihave #R1 := (BigSepL.bigSepL_lookup (Φ := fun i x => regPred γp i x)
    (show [a, b, c][1]? = some b from rfl)) $$ Hrp
  ihave #R2 := (BigSepL.bigSepL_lookup (Φ := fun i x => regPred γp i x)
    (show [a, b, c][2]? = some c from rfl)) $$ Hrp
  unfold regPred
  icases R0 with ⟨%w0, -, #P0⟩
  icases R1 with ⟨%w1, -, #P1⟩
  icases R2 with ⟨%w2, -, #P2⟩
  iframe Hk
  iapply predsSet_intro (GF := GF) γp w0 w1 w2
  iframe P0 P1 P2

/-- **Claim** (D13; replica node `k`'s boot, registered as `id`, before `NewReplica`): its
replica id's start resources, once (the node's claim token stays in the invariant in their
place). -/
theorem deploy_claim (δ : DeployNames) (γp : ProtoNames) (k : Nat) (hk : k < 3) (id : w64)
    (nodes : List GoString) (E : CoPset) (hE : ↑deployN ⊆ E) :
    inv deployN (deployInv δ γp) ∗ regReady δ k id nodes ∗ slotClaimTok γp k ⊢
      |={E}=> idSlotResN γp (uint.nat id) := by
  iintro ⟨#Hinv, #Hr, Htok⟩
  iinv Hinv with Hi Hclose
  unfold regReady
  icases Hr with ⟨#Hlb, %Hf⟩
  unfold deployInv
  icases Hi with ⟨%ks, %M, >Ha, >HM, >%Hks, >Hids, >Hreg, >Hfree⟩
  icases regAuth_lb_prefix δ (1 : Qp).half (ks.map addrOf) nodes $$ [Ha Hlb] with %Hpre
  · iframe Ha Hlb
  obtain ⟨ks', hks', rfl⟩ := prefix_map_addrOf Hpre
  have hl3 : ks'.length = 3 := by
    have := Hf.1.length_eq; simpa using this
  have hle := nodup_bound_length Hks.1 Hks.2.1
  have hkseq : ks' = ks := hks'.eq_of_length (by have := hks'.length_le; omega)
  subst hkseq
  obtain ⟨Hp, Hid⟩ := Hf
  rw [List.getElem?_map] at Hid
  obtain ⟨k', Hk', Hak⟩ : ∃ k', ks'[uint.nat id]? = some k' ∧ addrOf k' = addrOf k := by
    rcases h : ks'[uint.nat id]? with _ | k'
    · rw [h] at Hid; simp at Hid
    · rw [h] at Hid; simp only [Option.map_some, Option.some.injEq] at Hid
      exact ⟨k', rfl, Hid⟩
  have hk' : k' < 3 := Hks.2.1 k' (List.mem_of_getElem? Hk')
  have hkk := addrOf_inj hk' hk Hak
  subst hkk
  icases (BigSepL.bigSepL_lookup_acc (Φ := fun i x => iprop(regPred γp i x ∗
    (slotClaimTok γp x ∨ idSlotResN γp i))) Hk').1 $$ Hreg with ⟨⟨#Hrp, Hc⟩, Hback⟩
  icases Hc with (Hc | Hres)
  · unfold slotClaimTok
    ihave %hv := ghostMapElem_valid_2 _ _ _ _ _ _ $$ Hc Htok
    exfalso
    have := DFrac.valid_op_own hv.1
    simp at this
  ihave Hreg := Hback $$ %k' [Hrp Htok]
  · iframe Hrp; ileft; iexact Htok
  have hset : ks'.set (uint.nat id) k' = ks' := by
    apply List.ext_getElem?; intro j
    rw [List.getElem?_set]
    by_cases hj : uint.nat id = j
    · subst hj; have h1 := List.getElem?_eq_some_iff.mp Hk'; simp [h1.1, h1.2]
    · simp [hj]
  rw [hset]
  imod Hclose $$ [Ha HM Hids Hreg Hfree] with -
  · inext
    iexists ks', M
    iframe Ha HM Hids Hreg Hfree
    ipureintro; exact Hks
  imodintro
  iexact Hres

theorem registeredAsDef_agree (γ : GryffNames GF) (k1 k2 : Nat) (id1 id2 : w64)
    (n1 n2 : List GoString) :
    registeredAsDef γ k1 id1 n1 ∗ registeredAsDef γ k2 id2 n2 ⊢ ⌜n1 = n2⌝ := by
  unfold registeredAsDef regReady
  iintro ⟨⟨-, ⟨#H1, %Hf1⟩, -⟩, ⟨-, ⟨#H2, %Hf2⟩, -⟩⟩
  icases regLb_valid γ.deploy n1 n2 $$ [H1 H2] with %Hp
  · iframe H1 H2
  ipureintro
  have hl : n1.length = n2.length := by rw [Hf1.1.length_eq, Hf2.1.length_eq]
  rcases Hp with Hp | Hp
  · exact Hp.eq_of_length hl
  · exact (Hp.eq_of_length hl.symm).symm

end laws

end Perennial.gryff
