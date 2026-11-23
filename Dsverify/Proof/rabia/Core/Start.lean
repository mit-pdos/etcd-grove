/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/Rabia/Start.lean`, run `rabia-r1wake-1`, onto
Net's address protocols and remote's deployment.)

The deployment's ghost start (`start`), for the top level's `robust_of_distProtoRB`: from the
protocol registry `regCtx` and the unset addresses of the kit (`protoAddrs`, then the client
machines' addresses `cliAddr c`), the shared state (`shared γ`: the facts' invariant, the five
broadcast logs, the established connections' map over `nC × maxS`, the 21 `protoAddrs`' protocols
`addrP γ`/`addrQ γ`), the orchestrator's share `orchCore γ`, the client machines' `cliCore γ c`,
the server machines' `serverShare γ k`, the key-value state `kvState γ.rab init` (for remote's
pending library) and the client machines' addresses still unset (for remote's request protocols).

Against the lab: no per-client counters or tokens (`RNames`, `client_tok`: the kit's `Sys` has a
mutex), the client machines' claim addresses are gone (each machine claims `config.Conf` with its
own package state), connection ids are `Nat`.
-/
module

public import Dsverify.Proof.rabia.Core.StartAlloc

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS GooseGlobalGS.gooseAllG

/-- Server `X`'s broadcast log's invariant, from half its (empty) authority. -/
theorem bcastInv_alloc (γ : Names) (X : Nat) :
    monoListAuthOwn (GF := GF) (γ.net.bcast X) (1 : Qp).half ([] : List model.MsgV) ⊢
      |={⊤}=> inv (bcastN X) (bcastInv (G := G) γ X) := by
  iintro Hb
  imod inv_alloc (bcastN X) ⊤ (bcastInv (G := G) γ X) $$ [Hb] with #Hi
  · inext; unfold bcastInv; iexists []
    iframe Hb
    isplitr
    · ileft; ipureintro; rfl
    ipureintro; simp [RoundsOrdered]
  imodintro; iexact Hi

/-- The broadcast logs' invariants, for a list of servers. -/
theorem bcastInvs_alloc (γ : Names) : ∀ l : List Nat,
    ([∗list] X ∈ l, monoListAuthOwn (GF := GF) (γ.net.bcast X) (1 : Qp).half ([] : List model.MsgV))
      ⊢ |={⊤}=> [∗list] X ∈ l, inv (bcastN X) (bcastInv (G := G) γ X)
  | [] => by
    iintro -
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | X :: l => by
    iintro Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨H, Hs⟩
    imod bcastInv_alloc γ X $$ H with #Hi
    imod bcastInvs_alloc γ l $$ Hs with Hl
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hi Hl

/-- Allocate a resource per index of a list, its names chosen by a function. -/
theorem alloc_indexedS {X V : Type} [Inhabited V] :
    ∀ (l : List X) (P : Nat → V → IProp GF), (∀ i, ⊢ |==> ∃ v, P i v) →
    ⊢ |==> ∃ f : Nat → V, [∗list] i ↦ _x ∈ l, P i (f i)
  | [], P, _ => by
    imodintro
    iexists fun _ => default
    iapply BigSepL.bigSepL_nil.2; iempintro
  | _ :: l, P, hP => by
    imod hP 0 with ⟨%v, Hv⟩
    imod alloc_indexedS l (fun i => P (i + 1)) (fun i => hP (i + 1)) with ⟨%f, Hf⟩
    imodintro
    iexists fun i => Nat.casesOn i v f
    iapply BigSepL.bigSepL_cons.2
    iframe Hv Hf

/-- A big separating conjunction over `List.range n` by index is one by element. -/
theorem range_idx {PROP : Type _} [BI PROP] (n : Nat) (Φ : Nat → PROP) :
    ([∗list] i ↦ _x ∈ List.range n, Φ i) ⊢ [∗list] c ∈ List.range n, Φ c := by
  refine BigSepL.bigSepL_mono fun h => ?_
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem_range] at h2
  subst h2; exact .rfl

/-- The established connections' keys: every client and every server machine. -/
def estabKeys : List (Nat × Nat) :=
  (List.range nC).flatMap fun c => (List.range maxS).map fun k => (c, k)

theorem estabKeys_nodup : estabKeys.Nodup := by decide

/-- The client machines' shares, element by element. -/
theorem cli_shares_list (γ : Names) : ∀ l : List Nat, (∀ c ∈ l, c < nC) →
    □ shared (G := G) γ ∗ ([∗list] c ∈ l, keysOf (GF := GF) γ.rab (.cli c) []) ∗
      ([∗list] c ∈ l, [∗list] k ∈ List.range maxS, estabTok (GF := GF) γ c k) ⊢
      [∗list] c ∈ l, cliCore (G := G) γ c
  | [], _ => by
    iintro -
    iapply BigSepL.bigSepL_nil.2; iempintro
  | c :: l, hl => by
    iintro ⟨#Hsh, Hk, He⟩
    icases BigSepL.bigSepL_cons.1 $$ Hk with ⟨Hk, Hks⟩
    icases BigSepL.bigSepL_cons.1 $$ He with ⟨He, Hes⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hk He]
    · ihave #Hp := shared_cliCfgProto γ c (hl c (by simp)) $$ Hsh
      ihave #Ht := addrProto_tok (cliCfgAddr c) _ _ $$ Hp
      unfold cliCore
      iframe Hsh Hk He Ht
    · iapply cli_shares_list γ l (fun c h => hl c (by simp [h]))
      iframe Hsh Hks Hes

/-- The server machines' shares, element by element. -/
theorem srv_shares_list (γ : Names) : ∀ l : List Nat, (∀ k ∈ l, k < maxS) →
    □ shared (G := G) γ ∗ ([∗list] k ∈ l, keysOf (GF := GF) γ.rab (.srv k) []) ∗
      ([∗list] k ∈ l, monoListAuthOwn (GF := GF) (γ.net.bcast k) (1 : Qp).half
        ([] : List model.MsgV)) ⊢
      [∗list] k ∈ l, serverShare (G := G) γ k
  | [], _ => by
    iintro -
    iapply BigSepL.bigSepL_nil.2; iempintro
  | k :: l, hl => by
    iintro ⟨#Hsh, Hk, Hb⟩
    icases BigSepL.bigSepL_cons.1 $$ Hk with ⟨Hk, Hks⟩
    icases BigSepL.bigSepL_cons.1 $$ Hb with ⟨Hb, Hbs⟩
    have hk : k < maxS := hl k (by simp)
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hk Hb]
    · ihave #Hp1 := shared_proxyProto γ k hk $$ Hsh
      ihave #Hp2 := shared_netProto γ k hk $$ Hsh
      ihave #Hp3 := shared_cfgProto γ k hk $$ Hsh
      ihave #Ht1 := addrProto_tok (proxyAddr k) _ _ $$ Hp1
      ihave #Ht2 := addrProto_tok (netAddr k) _ _ $$ Hp2
      ihave #Ht3 := addrProto_tok (cfgAddr k) _ _ $$ Hp3
      unfold serverShare serverCore
      iframe Hsh Hk Hb Ht1 Ht2 Ht3
    · iapply srv_shares_list γ l (fun k h => hl k (by simp [h]))
      iframe Hsh Hks Hbs

/-- **The start** (see the file header). -/
theorem start :
    ⊢ regCtx (Gg := G) -∗
      ([∗list] a ∈ protoAddrs ++ (List.range nC).map cliAddr, addrUnset (Gg := G) a) ={⊤}=∗
      ∃ γ : Names, orchCore (G := G) γ ∗ ([∗list] c ∈ List.range nC, cliCore (G := G) γ c) ∗
        ([∗list] k ∈ List.range maxS, serverShare (G := G) γ k) ∗
        kvState (G := G) γ.rab (model.kv GoString GoString).init ∗
        [∗list] a ∈ (List.range nC).map cliAddr, addrUnset (Gg := G) a := by
  iintro #Hreg Hs
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hp, Hc⟩
  -- the shared names
  imod rabia_alloc (GF := GF) ⊤ with ⟨%γr, #Hrab, Hkv, Hkc, Hks, Hko⟩
  imod alloc_indexedS (V := GName) (List.range maxS)
    (fun _ g => iprop(monoListAuthOwn (GF := GF) g (1 : Qp).half ([] : List model.MsgV) ∗
      monoListAuthOwn (GF := GF) g (1 : Qp).half ([] : List model.MsgV)))
    (fun _ => by
      imod mono_list_alloc_halves (GF := GF) (A := model.MsgV) with ⟨%g, H1, H2⟩
      imodintro
      iexists g
      iframe H1 H2) with ⟨%f, Hb⟩
  ihave Hb := range_idx maxS _ $$ Hb
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hb with ⟨Hb1, Hb2⟩
  imod ghost_map_alloc_full (GF := GF) (none : Option Nat) estabKeys estabKeys_nodup
    with ⟨%γe, %me, He, Htoks, -⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Names, γ = ⟨γr, ⟨f, γe⟩⟩ := ⟨_, rfl⟩
  have hr : γ.rab = γr := by subst hγ; rfl
  have hb : γ.net.bcast = f := by subst hγ; rfl
  have he : γ.net.estab = γe := by subst hγ; rfl
  -- the broadcast logs' and the established connections' invariants
  imod bcastInvs_alloc γ (List.range maxS) $$ [Hb1] with #Hbi
  · rw [hb]; iexact Hb1
  imod inv_alloc estabN ⊤ (estabInv (G := G) γ) $$ [He] with #Hest
  · inext; unfold estabInv; iexists me; rw [he]; iexact He
  -- the 21 `protoAddrs`' protocols
  imod addrs_set_proto ⊤ (addrP (G := G) γ) (addrQ (G := G) γ) protoAddrs $$ Hreg Hp with #Hps
  ihave #Hsh : □ shared (G := G) γ $$ []
  · iintro !>
    unfold shared
    rw [hr]
    iframe Hrab Hest Hps Hbi
  imodintro
  iexists γ
  iframe Hc
  isplitl [Hko]
  · unfold orchCore
    iframe Hsh
    rw [hr]; iexact Hko
  isplitl [Hkc Htoks]
  · iapply cli_shares_list γ (List.range nC) (fun c h => List.mem_range.1 h)
    iframe Hsh
    isplitl [Hkc]
    · rw [hr]; iexact Hkc
    · unfold estabTok
      rw [he]
      iapply (show ([∗list] x ∈ estabKeys, (x ↪[γe] (none : Option Nat) : IProp GF)) ⊢
          [∗list] c ∈ List.range nC, [∗list] k ∈ List.range maxS,
            (c, k) ↪[γe] (none : Option Nat) from by
        unfold estabKeys
        rw [BigSepL.bigSepL_flatMap]
        refine BigSepL.bigSepL_mono fun _ _ => ?_
        rw [BigSepL.bigSepL_map]; exact fun _ h => h) $$ Htoks
  isplitl [Hks Hb2]
  · iapply srv_shares_list γ (List.range maxS) (fun k h => List.mem_range.1 h)
    iframe Hsh
    isplitl [Hks]
    · rw [hr]; iexact Hks
    · rw [hb]; iexact Hb2
  unfold kvState
  iexists []
  rw [hr]
  iframe Hkv
  ipureintro; rfl

end start

end Perennial.rabia
