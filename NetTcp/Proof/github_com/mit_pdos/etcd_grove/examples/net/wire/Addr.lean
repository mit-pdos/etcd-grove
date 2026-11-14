/-
A per-address protocol, for the proofs of `examples/net/`: the invariant of a plan address `a`
(`addrInv a Φ`) holds `a`'s pending set (`tcpPend`) and, for each connection `cn` pending there,
the resources `Φ cn` its dialer deposited (`Φ` timeless). A dial that deposits `Φ cn`
(`dial_au`) and an accept that takes it (`accept_au`) are the atomic updates of `net.Dial` and
`Listener.Accept` (`NetTcp/Spec/net/`). Also `setMap`, sets as the maps `[∗map]` ranges over
(`GSet` has no `[∗set]` instance; as raft's `Protocol.toMap`), with its laws.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

/-- A set as the map `[∗map]` ranges over. -/
@[reducible] def setMap (X : GSet Nat) : GMap Nat Unit := X



theorem setMap_insert (S : GSet Nat) (c : Nat) :
    setMap (S ∪ {[c]}) = (setMap S).insert c () := by
  apply GMap.ext; intro k
  simp only [setMap, GMap.lookup_insert_eq_iff]
  by_cases h : c = k
  · subst h
    have : c ∈ S ∪ {[c]} := (GMap.elem_of_union _ _ _).2 (.inr (GMap.elem_of_singleton_2 c))
    simpa [GMap.elem_of_gset] using this
  · simp only [h, ↓reduceIte]
    have hiff : k ∈ S ∪ {[c]} ↔ k ∈ S := by
      rw [GMap.elem_of_union, GMap.elem_of_singleton]; constructor
      · rintro (h1 | h1)
        · exact h1
        · exact absurd h1.symm h
      · intro h1; exact .inl h1
    simp only [GMap.elem_of_gset] at hiff
    cases h1 : S !! k <;> cases h2 : (S ∪ {[c]}) !! k <;> simp_all

theorem setMap_lookup_none {S : GSet Nat} {c : Nat} (h : c ∉ S) :
    PartialMap.get? (setMap S) c = none := by
  rw [gmap_get?_eq]
  cases hk : (setMap S).lookup c with
  | none => rfl
  | some u => exact absurd ((GMap.elem_of_gset _ _).2 (by simpa using hk)) h

theorem setMap_delete (S : GSet Nat) (c : Nat) :
    PartialMap.delete (setMap S) c = setMap (S \ {[c]}) := by
  apply GMap.ext; intro k
  show (GMap.delete c S).lookup k = (S \ {[c]}).lookup k
  by_cases h : c = k
  · subst h
    rw [GMap.lookup_delete]
    have : c ∉ S \ {[c]} := by
      rw [GMap.elem_of_difference]; intro h1; exact h1.2 (GMap.elem_of_singleton_2 c)
    rw [GMap.elem_of_gset] at this
    cases hk : (S \ {[c]}).lookup c with
    | none => rfl
    | some u => exact absurd (by simpa using hk) this
  · rw [GMap.lookup_delete_ne _ h]
    have hiff : k ∈ S \ {[c]} ↔ k ∈ S := by
      rw [GMap.elem_of_difference, GMap.not_elem_of_singleton]
      exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, Ne.symm h⟩⟩
    simp only [GMap.elem_of_gset] at hiff
    cases h1 : S !! k <;> cases h2 : (S \ {[c]}) !! k <;> simp_all


/-- Two namespaces of different names are disjoint (as Perennial's `sync.wg_mask_ndot_ne`). -/
theorem ndot_mask (N : Namespace) (x y : String) (h : x ≠ y) :
    (↑(N.@x) : CoPset) ⊆ ⊤ \ ↑(N.@y) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint N h p ⟨hp, h'⟩⟩

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The network's ghost state. -/
abbrev G : TcpGS GF := extGlobalGS tcpExt (G := Gg)

/-- The invariant of the plan address `a`: its pending connections, each with its dialer's
deposit `Φ cn`. -/
def addrInv (a : GoString) (Φ : Nat → IProp GF) : IProp GF :=
  iprop(∃ S, tcpPend G a S ∗ [∗map] cn ↦ _u ∈ setMap S, Φ cn)

/-- A dial of `a` whose dialer deposits `Φ cn` (made, at the address's invariant's mask, from the
new connection's acceptor end, `mk`) and keeps its own end and `R cn`. -/
theorem dial_au (N : Namespace) (a : GoString) (Φ R : Nat → IProp GF) [∀ cn, Timeless (Φ cn)] :
    ⊢ inv N (addrInv a Φ) -∗
      (∀ cn, tcpConnAt G cn a -∗ tcpFreshEnd G cn true ={⊤ \ ↑N}=∗ Φ cn ∗ R cn) -∗
      |={⊤,∅}=> ∃ S, tcpPend G a S ∗
        ∀ cn, ⌜cn ∉ S⌝ -∗ tcpPend G a (S ∪ {[cn]}) -∗ tcpConnAt G cn a -∗
          tcpFreshEnd G cn false -∗ tcpFreshEnd G cn true ={∅,⊤}=∗
          tcpFreshEnd G cn false ∗ R cn := by
  iintro #Hinv Hmk
  iinv Hinv with Hi Hclose
  unfold addrInv
  icases Hi with ⟨%S, >Hpend, >Hdeps⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists S
  iframe Hpend
  iintro %cn %HcS Hpend #Hat Hd Ha
  imod Hmask
  imod Hmk $$ %cn Hat Ha with ⟨HΦ, HR⟩
  imod Hclose $$ [Hpend Hdeps HΦ] with -
  · inext
    iexists S ∪ {[cn]}
    iframe Hpend
    rw [setMap_insert]
    iapply (BigSepM.bigSepM_insert (setMap_lookup_none HcS)).2
    iframe Hdeps HΦ
  imodintro
  iframe Hd HR

/-- An accept at `a`: the acceptor takes the connection's deposit. -/
theorem accept_au (N : Namespace) (a : GoString) (Φ : Nat → IProp GF) [∀ cn, Timeless (Φ cn)] :
    ⊢ inv N (addrInv a Φ) -∗ |={⊤,∅}=> ∃ S, tcpPend G a S ∗
      ∀ cn, ⌜cn ∈ S⌝ -∗ tcpPend G a (S \ {[cn]}) ={∅,⊤}=∗ Φ cn := by
  iintro #Hinv
  iinv Hinv with Hi Hclose
  unfold addrInv
  icases Hi with ⟨%S, >Hpend, >Hdeps⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists S
  iframe Hpend
  iintro %cn %HcS Hpend
  imod Hmask
  have hl : PartialMap.get? (setMap S) cn = some () := by
    rw [gmap_get?_eq]; exact (GMap.elem_of_gset _ _).1 HcS
  icases (BigSepM.bigSepM_delete hl).1 $$ Hdeps with ⟨Hp, Hdeps⟩
  rw [setMap_delete]
  imod Hclose $$ [Hpend Hdeps] with -
  · inext
    iexists S \ {[cn]}
    iframe Hpend Hdeps
  imodintro
  iexact Hp

/-- The address's invariant of a fresh network: nothing pending. -/
theorem addrInv_alloc (N : Namespace) (a : GoString) (Φ : Nat → IProp GF) :
    tcpPend G a ∅ ={⊤}=∗ inv N (addrInv a Φ) := by
  iintro Hpend
  iapply inv_alloc
  inext
  unfold addrInv
  iexists ∅
  iframe Hpend
  iapply BigSepM.bigSepM_empty.2
  iempintro


/-- A write by an end its thread owns: the update of `net.Conn.Write`, which hands back the end's
state and bytes after the write. -/
theorem owned_write_au (c : Nat) (s : Bool) (st : TcpEnd) (r : Nat) (out : GoString) (f : Bool)
    (bs : GoString) :
    ⊢ tcpEnd G c s st r -∗ tcpOut (G (Gg := Gg)) c s out f -∗
      |={⊤,∅}=> ∃ st0 r0 out0 f0, tcpEnd G c s st0 r0 ∗ tcpOut G c s out0 f0 ∗
        ∀ k ok st', ⌜WriteRes st0 bs k ok st'⌝ -∗ tcpEnd G c s st' r0 -∗
          tcpOut G c s (out0 ++ bs.take k) f0 ={∅,⊤}=∗
          ∃ st'', ⌜WriteRes st bs k ok st''⌝ ∗ tcpEnd G c s st'' r ∗
            tcpOut G c s (out ++ bs.take k) f := by
  iintro Hend Hout
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r, out, f
  iframe Hend Hout
  iintro %k %ok %st' %Hwr Hend Hout
  imod Hmask
  imodintro
  iexists st'
  iframe Hend Hout
  ipureintro; exact Hwr

/-- A close by an end its thread owns: the update of `net.Conn.Close`. -/
theorem owned_close_au (c : Nat) (s : Bool) (st : TcpEnd) (r : Nat) (out : GoString) (f : Bool) :
    ⊢ tcpEnd G c s st r -∗ tcpOut (G (Gg := Gg)) c s out f -∗
      |={⊤,∅}=> ∃ st0 r0 out0 f0, tcpEnd G c s st0 r0 ∗ tcpOut G c s out0 f0 ∗
        ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st0 f0 ok st' f'⌝ -∗
          tcpEnd G c s st' r0 -∗ tcpOut G c s out0 f' ={∅,⊤}=∗
          ∃ st'' f'', ⌜CloseRes false (fun st => { st with closed := true }) st f ok st'' f''⌝ ∗
            tcpEnd G c s st'' r ∗ tcpOut G c s out f'' := by
  iintro Hend Hout
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r, out, f
  iframe Hend Hout
  iintro %ok %st' %f' %Hcr Hend Hout
  imod Hmask
  imodintro
  iexists st', f'
  iframe Hend Hout
  ipureintro; exact Hcr


/-- A close by an end its thread owns, whose state the thread no longer needs. -/
theorem owned_close_drop (c : Nat) (s : Bool) (st : TcpEnd) (r : Nat) (out : GoString) (f : Bool) :
    ⊢ tcpEnd G c s st r -∗ tcpOut (G (Gg := Gg)) c s out f -∗
      |={⊤,∅}=> ∃ st0 r0 out0 f0, tcpEnd G c s st0 r0 ∗ tcpOut G c s out0 f0 ∗
        ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st0 f0 ok st' f'⌝ -∗
          tcpEnd G c s st' r0 -∗ tcpOut G c s out0 f' ={∅,⊤}=∗ True := by
  iintro Hend Hout
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r, out, f
  iframe Hend Hout
  iintro %ok %st' %f' %Hcr - -
  imod Hmask
  imodintro
  itrivial

end wps

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
